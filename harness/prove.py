#!/usr/bin/env python3
"""prove.py: a small proof-loop harness for Lean 4 targets.

A target is a Lean file whose theorems are stated with `:= by sorry`. `freeze` records it. `check` compiles a
candidate proof file and passes it only if (1) it compiles, (2) no theorem uses `sorry`, (3) it leaves no namespace
or section open, (4) each frozen theorem is proved by the candidate theorem of the SAME fully qualified name with
the SAME statement (Lean checks this: the frozen statement is re-stated after the candidate and closed with
`apply <candidate theorem>`), (5) each frozen `def` is unchanged (`rfl`), (6) every re-stated frozen statement and
def elaborates to the same term as in the frozen file alone (a fingerprint; this catches a candidate that changes
what the statement means with an instance, notation or `open`), (7) `#print axioms` shows only the standard
axioms and the candidate declares no axiom, (8) the candidate uses no metaprogramming command that could bypass
the checks (`run_cmd`, `elab`, `macro_rules`, `#eval`, `#exit`, `unsafe`, `implemented_by`, `extern`,
`debug.skipKernelTC`). Every check is appended to a ledger.

Frozen-file format (kept simple on purpose):
  * target theorems: `theorem`/`lemma` at column 0, proof ending in the single token `sorry`;
  * frozen definitions: `def`/`abbrev` at column 0 (non-recursive); `instance`/`structure`/`inductive`/`class`
    are compared as text;
  * the candidate must be one file that closes every namespace and section it opens.

Usage (from the repository root):
  harness/prove.py freeze   BSD/Foo.lean
  harness/prove.py check    BSD/Foo.lean --approach "what was tried" [--worker NAME] [--candidate FILE]
  harness/prove.py status   [-v] [--all]
  harness/prove.py run      BSD/Foo.lean [--prover "CMD"] [--rounds N]
  harness/prove.py split    BSD/Foo.lean [--out DIR]
  harness/prove.py merge    BSD/Foo.lean [--out DIR]
  harness/prove.py scan     BSD/Foo.lean [--prover "CMD"] [--out FILE]
  harness/prove.py selftest
"""
import argparse, hashlib, json, os, re, shutil, subprocess, sys, tempfile, time
from pathlib import Path

ROOT = next((d for d in Path(__file__).resolve().parents if (d / "lakefile.toml").exists() or (d / "lakefile.lean").exists()),
            Path(__file__).resolve().parent.parent)
HARNESS = ROOT / "harness"
FROZEN = HARNESS / "frozen"
WORK = HARNESS / ".work"
LEDGER = HARNESS / "ledger.jsonl"
TESTS = HARNESS / "tests"
if os.environ.get("PROVE_STATE"):  # a private frozen dir and ledger, for dry runs and tests
    FROZEN, LEDGER = Path(os.environ["PROVE_STATE"]) / "frozen", Path(os.environ["PROVE_STATE"]) / "ledger.jsonl"
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
SUFFIX = "_frozenCheck"
MODS = r"(?:(?:private|protected|noncomputable|public|nonrec|unsafe|partial)\s+)*"
DECL = re.compile(rf"^(?:@\[[^\]]*\]\s*)*{MODS}(theorem|lemma|def|abbrev|instance|structure|inductive|class)\s+([^\s:({{\[]+)?")
BOUNDARY = re.compile(rf"^(?:/--|/-!|--|@\[|end\b|namespace\b|section\b|open\b|variable\b|universe\b|set_option\b|"
                      rf"attribute\b|#|import\b|{MODS}(?:theorem|lemma|def|abbrev|instance|structure|inductive|class|example)\b)")
MACRO = ("macro \"harness_close \" n:ident : tactic => `(tactic| first | exact $n | (apply $n <;> assumption) | "
         "(intros; apply $n <;> assumption))\n")
# Lean side of the gate: a scope check and a fingerprint of a declaration (type hash, top-level binder kinds,
# universe names, value hash for definitions). Binder names are not part of Expr.hash, so renaming a bound
# variable does not change the fingerprint; changing an instance, a constant or an explicit/implicit binder does.
LEAN_PRE = r'''open Lean Elab Command in
elab "#harness_scope_closed" : command => do
  let n := (← getScopes).length
  if n > 1 then
    throwError "HARNESS-SCOPE: the candidate leaves {n - 1} namespace or section open (namespace {← getCurrNamespace})"

open Lean in
partial def harnessShape : Expr → String
  | .forallE _ _ b bi => (match bi with
      | .default => "e" | .implicit => "i" | .strictImplicit => "s" | .instImplicit => "c") ++ harnessShape b
  | _ => ""

open Lean Elab Command in
elab "#harness_sig " id:ident : command => do
  let n ← liftCoreM <| realizeGlobalConstNoOverload id
  let ci ← getConstInfo n
  let v := match ci.value? with | some v => toString v.hash | none => "-"
  let lv := if ci.levelParams.isEmpty then "-" else ",".intercalate (ci.levelParams.map toString)
  let sh := harnessShape ci.type
  logInfo m!"HARNESS-SIG {n} {lv} {ci.type.hash} {if sh.isEmpty then "-" else sh} {v}"
'''
SIG = re.compile(r"HARNESS-SIG (\S+) (\S+) (\S+) (\S+) (\S+)")
# Commands a proof never needs and that could fake or bypass a check. Matched on the candidate with comments removed.
FORBIDDEN = [
    ("metaprogram", re.compile(r"(?<![\w.])(run_cmd|run_elab|run_meta|run_tac|#eval|#exit|elab|elab_rules|macro_rules|"
                               r"initialize|builtin_initialize)(?![\w.])")),
    ("command-macro", re.compile(r":\s*command\b")),
    ("environment", re.compile(r"\b(Lean\.Elab|Lean\.Meta|Lean\.Environment|addDecl|modifyEnv|setEnv)\b")),
    ("unsafe", re.compile(r"\b(unsafe|implemented_by|extern)\b")),
    ("kernel-off", re.compile(r"\bdebug\.skipKernelTC\b|\bLean\.ofReduceBool\b|\bLean\.trustCompiler\b|\bsorryAx\b")),
    ("harness-name", re.compile(r"harness_|HARNESS")),
]
AXIOM_DECL = re.compile(rf"^(?:@\[[^\]]*\]\s*)*{MODS}axiom\s+(\S+)", re.M)


def sha(text):
    return hashlib.sha256(text.encode()).hexdigest()[:16]


def now():
    return time.strftime("%Y-%m-%dT%H:%M:%S")


def frozen_path(target):
    return FROZEN / (str(Path(target)).replace("/", "__"))


def append_row(row):
    LEDGER.parent.mkdir(parents=True, exist_ok=True)
    with LEDGER.open("a") as f:
        f.write(json.dumps(row) + "\n")


def ledger_rows():
    if not LEDGER.exists():
        return []
    return [json.loads(l) for l in LEDGER.read_text().splitlines() if l.strip()]


def strip_comments(text):
    text = re.sub(r"/-.*?-/", "", text, flags=re.S)
    return re.sub(r"--.*", "", text)


def split_chunks(text):
    """Split a Lean file into chunks that each start at a column-0 command boundary."""
    chunks, cur, in_doc, has_cmd = [], [], False, False
    for line in text.splitlines(keepends=True):
        starts = bool(BOUNDARY.match(line)) and not in_doc
        if starts and cur and has_cmd:
            chunks.append("".join(cur)); cur, has_cmd = [], False
        cur.append(line)
        # a docstring or a bare attribute line stays attached to the declaration that follows it
        if starts and (DECL.match(line) or not re.match(r"^(/--|@\[)", line)):
            has_cmd = True
        if not in_doc and (line.startswith("/--") or line.startswith("/-!") or line.startswith("/-")):
            in_doc = "-/" not in line
        elif in_doc and "-/" in line:
            in_doc = False
    if cur:
        chunks.append("".join(cur))
    return chunks


def decl_of(chunk):
    """Return (kind, name) for a declaration chunk, skipping its docstring and attributes."""
    body = re.sub(r"/--.*?-/", "", chunk, flags=re.S).lstrip()
    m = DECL.match(body)
    return (m.group(1), m.group(2)) if m else (None, None)


def norm(s):
    return re.sub(r"\s+", " ", re.sub(r"/--.*?-/", "", s, flags=re.S)).strip()


def walk(text):
    """Yield (chunk, kind, name, full_name) for each chunk, tracking the namespace the chunk is declared in."""
    stack = []  # (kind, number of namespace components)
    for chunk in split_chunks(text):
        kind, name = decl_of(chunk)
        full = None
        if name:
            ns = [c for k, cs in stack for c in cs]
            full = name[len("_root_."):] if name.startswith("_root_.") else ".".join(ns + [name])
        yield chunk, kind, name, full
        m = re.search(r"^(namespace|section|end)\b[ \t]*(\S*)", strip_comments(chunk), flags=re.M)
        if m and not kind:
            if m.group(1) == "namespace":
                stack.append(("namespace", m.group(2).split(".")))
            elif m.group(1) == "section":
                stack.append(("section", []))
            elif stack:
                stack.pop()


def is_target(chunk, kind, name):
    return kind in ("theorem", "lemma") and name and re.search(r"\bsorry\b", chunk)


def build_check(frozen_text, candidate_text):
    """Return (check file text, frozen theorem full names, text-compared chunks missing from the candidate)."""
    out, theorems, missing = [], [], []
    frozen_text = re.sub(r"^import .*\n", "", frozen_text, flags=re.M)
    cand_norm = norm(candidate_text)
    for chunk, kind, name, full in walk(frozen_text):
        if chunk.lstrip().startswith("import"):
            continue
        if kind in ("theorem", "lemma") and name:
            if not is_target(chunk, kind, name):
                continue  # a proved lemma in the frozen file: nothing to check
            head, _, tail = chunk.rpartition("sorry")
            renamed = re.sub(rf"\b{kind}\s+{re.escape(name)}(?=[\s:({{\[])", f"{kind} {name}{SUFFIX} ", head, count=1)
            out.append(f"{renamed}harness_close _root_.{full}{tail}\n#print axioms _root_.{full}\n"
                       f"#harness_sig {name}{SUFFIX}\n")
            theorems.append(full)
        elif kind in ("def", "abbrev") and name:
            renamed = re.sub(rf"\b{kind}\s+{re.escape(name)}(?=[\s:({{\[])", f"{kind} {name}{SUFFIX} ", chunk, count=1)
            out.append(f"{renamed}\nexample : @_root_.{full} = @{name}{SUFFIX} := rfl\n#harness_sig {name}{SUFFIX}\n")
        elif kind:
            if norm(chunk) not in cand_norm:
                missing.append(norm(chunk)[:120])
        else:
            out.append(chunk)  # namespace, open, variable, comments: keep the context
    return MACRO + LEAN_PRE + "\n#harness_scope_closed\n\n" + "".join(out), theorems, missing


def build_sig_file(frozen_text):
    """The frozen file alone, with a fingerprint printed after each target theorem and each frozen def."""
    lines = frozen_text.splitlines(keepends=True)
    last_import = max([i for i, l in enumerate(lines) if l.startswith("import ")], default=-1)
    head, rest = "".join(lines[: last_import + 1]), "".join(lines[last_import + 1:])
    out = []
    for chunk, kind, name, full in walk(rest):
        out.append(chunk if chunk.endswith("\n") else chunk + "\n")
        if is_target(chunk, kind, name) or (kind in ("def", "abbrev") and name):
            out.append(f"#harness_sig {name}\n")
    return head + "\n" + LEAN_PRE + "\n" + "".join(out)


def parse_sigs(out):
    """Fingerprint lines from Lean's output (info messages carry no position, so the whole output is read; a
    candidate cannot print one because the word HARNESS is forbidden in it)."""
    sigs = {}
    for m in SIG.finditer(out):
        name = m.group(1)
        name = name[: -len(SUFFIX)] if name.endswith(SUFFIX) else name
        sigs[name] = " ".join(m.groups()[1:])
    return sigs


ERR = re.compile(r"^(?P<file>[^:\n]+):(?P<line>\d+):(?P<col>\d+): (?P<sev>error|warning|info)(?:\([^)]*\))?: (?P<msg>.*)$")
CLASSES = [
    ("timeout", r"deterministic\) timeout|maximum recursion depth|heartbeats"),
    ("unknown-name", r"[Uu]nknown (identifier|constant|namespace)|unknown tactic|[Ii]nvalid field|does not contain"),
    ("type-mismatch", r"[Tt]ype mismatch|Application type mismatch|has type|Function expected"),
    ("syntax", r"unexpected token|unexpected identifier|^expected "),
    ("instance", r"failed to synthesize"),
    ("unsolved-goals", r"unsolved goals"),
    ("tactic-failed", r"linarith failed|omega could not|ring failed|simp made no progress|failed to prove|did not|Tactic|tactic .* failed|decide"),
]


def classify(msg):
    for name, pat in CLASSES:
        if re.search(pat, msg):
            return name
    return "other"


def parse(output):
    items, cur = [], None
    for line in output.splitlines():
        m = ERR.match(line)
        if m:
            cur = {"line": int(m["line"]), "sev": m["sev"], "msg": m["msg"]}
            items.append(cur)
        elif re.match(r"^(HARNESS-SIG |'.+' (depends on axioms|does not depend on any axioms))", line):
            cur = None  # position-less info output of the generated check region, not part of a message
        elif cur is not None:
            cur["msg"] += "\n" + line
    return items


def lean(path, timeout, slot=True):
    cmd = ["lake", "env", "lean", str(path)]
    if slot and shutil.which("heavy-slot"):
        cmd = ["heavy-slot", "run", "--"] + cmd
    t0 = time.time()
    try:
        p = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True, timeout=timeout)
        return p.returncode, p.stdout + p.stderr, time.time() - t0
    except subprocess.TimeoutExpired as e:
        out = e.stdout.decode() if isinstance(e.stdout, bytes) else (e.stdout or "")
        return 124, out + "\nharness: (deterministic) timeout after %ss" % timeout, time.time() - t0


def lean_text(text, stem, timeout, slot=True):
    WORK.mkdir(parents=True, exist_ok=True)
    path = WORK / f"{stem}_{os.getpid()}_{time.time_ns() % 10**6}.lean"
    path.write_text(text)
    try:
        rc, out, secs = lean(path, timeout, slot)
        if os.environ.get("PROVE_KEEP"):  # debugging: keep the generated file and its output
            path.with_suffix(".out").write_text(out)
        return rc, out, secs
    finally:
        if not os.environ.get("PROVE_KEEP"):
            path.unlink(missing_ok=True)


def frozen_sigs(target, frozen, timeout, slot):
    """Fingerprints of the frozen file elaborated alone, cached next to the frozen copy (keyed by its hash)."""
    cache = frozen_path(target).with_suffix(".sig.json")
    if cache.exists():
        data = json.loads(cache.read_text())
        if data.get("frozen_sha") == sha(frozen) and data.get("pre_sha") == sha(LEAN_PRE):
            return data["sigs"]
    rc, out, _ = lean_text(build_sig_file(frozen), frozen_path(target).stem + "_sig", timeout, slot)
    items = parse(out)
    if rc != 0 or any(i["sev"] == "error" for i in items):
        return None
    sigs = parse_sigs(out)
    cache.write_text(json.dumps({"frozen_sha": sha(frozen), "pre_sha": sha(LEAN_PRE), "sigs": sigs}, indent=1) + "\n")
    return sigs


def cmd_freeze(a):
    src = ROOT / a.target
    text = src.read_text()
    dst = frozen_path(a.target)
    if dst.exists() and not a.refreeze:
        sys.exit(f"already frozen: {dst} (use --refreeze --reason '...' to change the statement in the open)")
    if a.refreeze and not a.reason:
        sys.exit("--refreeze needs --reason")
    _, theorems, _ = build_check(text, text)
    if not theorems:
        sys.exit("no `theorem ... := by sorry` targets found")
    rc, out, secs = lean(src, a.timeout, not a.no_slot)
    errors = [i for i in parse(out) if i["sev"] == "error"]
    if rc != 0 or errors:
        print(out[-3000:]); sys.exit("the statement file does not compile; fix it before freezing")
    FROZEN.mkdir(parents=True, exist_ok=True)
    old = dst.read_text() if dst.exists() else None
    dst.write_text(text)
    sigs = frozen_sigs(a.target, text, a.timeout, not a.no_slot)
    row = {"ts": now(), "event": "refreeze" if old else "freeze", "target": a.target,
           "frozen_sha": sha(text), "theorems": theorems, "reason": a.reason or "", "old_sha": sha(old) if old else ""}
    append_row(row)
    print(f"frozen {a.target} sha {row['frozen_sha']} targets: {', '.join(theorems)}"
          + ("" if sigs is not None else " (WARNING: fingerprints unavailable)"))


def gate(target, cand, approach, worker, timeout=1500, slot=True, log=True, extra=None):
    """Run the gate on candidate text for a frozen target. Returns a dict: the ledger row plus details."""
    fz = frozen_path(target)
    if not fz.exists():
        sys.exit(f"not frozen: run `harness/prove.py freeze {target}` first")
    frozen = fz.read_text()
    check_text, theorems, missing = build_check(frozen, cand)
    n_cand = cand.count("\n") + (0 if cand.endswith("\n") else 1)
    full = cand + ("" if cand.endswith("\n") else "\n") + "\n-- HARNESS CHECK (generated)\n" + check_text
    rc, out, secs = lean_text(full, fz.name.replace(".lean", "") + "_check", timeout, slot)
    items = parse(out)
    errors = [i for i in items if i["sev"] == "error"]
    own = [e for e in errors if e["line"] <= n_cand]
    gate_errs = [e for e in errors if e["line"] > n_cand]
    scope = [e for e in gate_errs if "HARNESS-SCOPE" in e["msg"]]
    n_sorry = sum(1 for i in items if i["sev"] == "warning" and "sorry" in i["msg"] and i["line"] <= n_cand)
    tail = out  # `#print axioms` output is an info message with no position; faking it cannot hide an axiom
    axioms, reported = set(), set()
    for m in re.finditer(r"^'(.+?)' depends on axioms: \[(.*?)\]", tail, flags=re.S | re.M):
        reported.add(m.group(1)); axioms |= {x.strip() for x in m.group(2).split(",") if x.strip()}
    for m in re.finditer(r"^'(.+?)' does not depend on any axioms", tail, flags=re.M):
        reported.add(m.group(1))
    bare = strip_comments(cand)
    declared = sorted(set(AXIOM_DECL.findall(bare)) - set(AXIOM_DECL.findall(strip_comments(frozen))))
    bad_axioms = sorted(axioms - STANDARD_AXIOMS) + [f"declared:{d}" for d in declared]
    frozen_bare = strip_comments(frozen)
    forbidden = [f"{label}: {m.group(0).strip()[:60]}" for label, pat in FORBIDDEN for m in pat.finditer(bare)
                 if not pat.search(frozen_bare)]
    expected = frozen_sigs(target, frozen, timeout, slot)
    got = parse_sigs(out)
    sig_diffs = []
    if expected is not None and not gate_errs:
        sig_diffs = [n for n in expected if got.get(n) != expected[n]]
    if rc == 124 or any(classify(e["msg"]) == "timeout" for e in own):
        cls = "timeout"
    elif own:
        cls = classify(own[0]["msg"])
    elif n_sorry or "sorryAx" in axioms:
        cls = "sorry"
    elif scope:
        cls = "scope-open"
    elif gate_errs or missing or sig_diffs:
        cls = "statement-changed"
    elif bad_axioms:
        cls = "new-axiom"
    elif forbidden:
        cls = "forbidden"
    elif len(reported) < len(theorems):
        cls = "gate-incomplete"
    else:
        cls = "none"
    verdict = "pass" if cls == "none" and rc == 0 else "fail"
    prior = sum(1 for r in ledger_rows() if r.get("target") == target and r.get("event") == "check")
    first = (own or gate_errs or [{"msg": "", "line": 0}])[0]
    first_error = (f"line {first['line']}: " + first["msg"])[:400] if first["msg"] else ""
    if not first_error and sig_diffs:
        first_error = "frozen statement elaborates differently after the candidate: " + ", ".join(sig_diffs)
    row = {"ts": now(), "event": "check", "target": target, "attempt": prior + 1,
           "worker": worker, "approach": approach, "verdict": verdict, "error_class": cls,
           "n_errors": len(own), "n_gate_errors": len(gate_errs), "n_sorry": n_sorry, "axioms": sorted(axioms),
           "frozen_sha": sha(frozen), "candidate_sha": sha(cand), "seconds": round(secs, 1),
           "first_error": first_error}
    if extra:
        row.update(extra)
    if log:
        append_row(row)
    return {"row": row, "own": own, "gate": gate_errs, "missing": missing, "bad_axioms": bad_axioms,
            "forbidden": forbidden, "sig_diffs": sig_diffs, "sig_unavailable": expected is None}


def report(g, show=8, width=700):
    r = g["row"]
    print(f"{r['verdict'].upper()} {r['target']} attempt {r['attempt']} class={r['error_class']} errors={r['n_errors']} "
          f"gate_errors={r['n_gate_errors']} sorry={r['n_sorry']} axioms={r['axioms']} {r['seconds']:.0f}s")
    for e in g["own"][:show]:
        print(f"  error line {e['line']}: {e['msg'][:width]}")
    for e in g["gate"][:show]:
        print(f"  GATE (frozen statement not proved as stated) : {e['msg'][:width]}")
    for m in g["missing"]:
        print(f"  GATE frozen declaration missing or changed: {m}")
    for n in g["sig_diffs"]:
        print(f"  GATE {n}: the frozen statement elaborates differently after the candidate "
              f"(an instance, notation, open or definition changed what it means)")
    if g["bad_axioms"]:
        print(f"  GATE non-standard axioms: {g['bad_axioms']}")
    for f in g["forbidden"]:
        print(f"  GATE forbidden command in candidate: {f}")
    if g["sig_unavailable"]:
        print("  WARNING: the frozen file's fingerprints could not be computed; check (6) was skipped")


def cmd_check(a):
    src = Path(a.candidate) if a.candidate else ROOT / a.target
    g = gate(a.target, src.read_text(), a.approach, a.worker, a.timeout, not a.no_slot)
    report(g, a.show, a.width)
    sys.exit(0 if g["row"]["verdict"] == "pass" else 1)


def cmd_status(a):
    rows = ledger_rows()
    if not rows:
        sys.exit("no ledger yet")
    by = {}
    for r in rows:
        if not a.all and (r.get("selftest") or r["target"].startswith("harness/tests/")):
            continue
        by.setdefault(r["target"], []).append(r)
    for target, rs in by.items():
        checks = [r for r in rs if r["event"] == "check"]
        classes = {}
        for r in checks:
            classes[r["error_class"]] = classes.get(r["error_class"], 0) + 1
        last = checks[-1] if checks else None
        state = "PASS" if last and last["verdict"] == "pass" else "open"
        print(f"{state:5} {target}: {len(checks)} checks, classes {classes}, refreezes "
              f"{sum(1 for r in rs if r['event'] == 'refreeze')}")
        if a.verbose:
            for r in checks:
                print(f"    {r['ts']} #{r['attempt']} {r['verdict']} {r['error_class']:17} {r.get('worker', '')[:14]:14} "
                      f"{r['approach'][:90]}")


# ---------------------------------------------------------------- run: the unattended loop

PROVER_SYSTEM = ("You write Lean 4 proofs against Mathlib. Reply with one APPROACH line and one lean code block "
                 "holding the complete file.")
# Any command that reads a prompt on stdin and prints a reply. `PROVE_PROVER` overrides it; a local bulk wrapper
# named `claude-batch` is used when it is on PATH; otherwise the Claude Code CLI in print mode.
def default_prover(system):
    return os.environ.get("PROVE_PROVER") or (
        f"claude-batch --model sonnet --system-prompt '{system}'" if shutil.which("claude-batch")
        else f"claude -p --model sonnet --append-system-prompt '{system}'")


DEFAULT_PROVER = default_prover(PROVER_SYSTEM)
PROMPT = """You are proving theorems in Lean {lean} with Mathlib ({mathlib}). Replace every `sorry` in the
candidate file with a proof.

Rules (a gate checks all of them; breaking one fails the attempt):
- keep every theorem statement, `def`, namespace and `variable` line of the FROZEN file exactly as written;
- you may add helper lemmas above the theorems and extra Mathlib imports;
- no `sorry`, `admit`, `axiom`, `native_decide`, metaprogramming; close every namespace and section you open;
- Mathlib lemma names drift: prefer tactics (`simp`, `omega`, `linarith`, `nlinarith`, `ring`, `aesop`,
  `exact?` is NOT available to you) and names you are sure exist in current Mathlib.

Reply format: line 1 `APPROACH: <one line, what this attempt does and how it differs from earlier ones>`,
then the complete new file in ONE ```lean code block. Nothing else.

## FROZEN file (the statements to prove)
```lean
{frozen}```

## Current candidate{cand_note}
{cand_block}
## Result of the last check
{last}

## Earlier attempts on this target (newest last; do not repeat an approach that failed)
{history}
"""


def extract_reply(reply):
    blocks = re.findall(r"```(?:lean4?|Lean)?[ \t]*\n(.*?)```", reply, flags=re.S)
    m = re.search(r"^\s*APPROACH:\s*(.+)$", reply, flags=re.M)
    approach = m.group(1).strip() if m else next((l.strip() for l in reply.splitlines() if l.strip()), "")
    return (blocks[-1] if blocks else None), approach[:200]


def describe(g, width=900, show=6):
    if g is None:
        return "(no check yet)"
    r = g["row"]
    lines = [f"class={r['error_class']} errors={r['n_errors']} gate_errors={r['n_gate_errors']} sorry={r['n_sorry']}"]
    for e in g["own"][:show]:
        lines.append(f"- line {e['line']}: {e['msg'][:width]}")
    for e in g["gate"][:2]:
        lines.append(f"- GATE: a frozen statement is not proved as written: {e['msg'][:300]}")
    lines += [f"- GATE: frozen declaration missing or changed: {m}" for m in g["missing"]]
    lines += [f"- GATE: {n} elaborates differently (instance/notation/open changed)" for n in g["sig_diffs"]]
    if [x for x in g["bad_axioms"] if x != "sorryAx"]:
        lines.append(f"- GATE: non-standard axioms {g['bad_axioms']}")
    lines += [f"- GATE: forbidden command: {f}" for f in g["forbidden"]]
    return "\n".join(lines)


def score(g):
    r = g["row"]
    if r["verdict"] == "pass":
        return 0
    return r["n_sorry"] + r["n_errors"] + r["n_gate_errors"] + 1


def cmd_run(a):
    target, src = a.target, ROOT / a.target
    fz = frozen_path(target)
    if not fz.exists():
        sys.exit(f"not frozen: run `harness/prove.py freeze {target}` first")
    frozen = fz.read_text()
    worker = a.worker or "run:" + a.prover.split()[0]
    lean_v = (ROOT / "lean-toolchain").read_text().strip().split(":")[-1]
    cand = src.read_text()
    g = gate(target, cand, "run baseline (not an attempt)", worker, a.timeout, not a.no_slot, log=False)
    best_text, best_score = cand, score(g)
    print(f"run {target}: baseline class={g['row']['error_class']} score={best_score}; prover: {a.prover}")
    if g["row"]["verdict"] == "pass":
        print("already passes"); return
    for rnd in range(1, a.rounds + 1):
        hist = [r for r in ledger_rows() if r.get("target") == target and r.get("event") == "check"][-a.history:]
        history = "\n".join(f"- #{r['attempt']} {r['verdict']} {r['error_class']}: {r['approach'][:160]}"
                            + (f" | {r['first_error'][:200]}" if r.get("first_error") else "") for r in hist) or "(none)"
        same = cand.strip() == frozen.strip()
        prompt = PROMPT.format(
            lean=lean_v, mathlib="tag " + lean_v, frozen=frozen if frozen.endswith("\n") else frozen + "\n",
            cand_note=" (identical to the FROZEN file)" if same else "",
            cand_block="" if same else f"```lean\n{cand}{'' if cand.endswith(chr(10)) else chr(10)}```\n",
            last=describe(g), history=history)
        t0 = time.time()
        try:
            p = subprocess.run(a.prover, shell=True, input=prompt, capture_output=True, text=True,
                               timeout=a.prover_timeout, cwd=ROOT)
            reply, perr = p.stdout, (p.stderr or "")[-300:]
        except subprocess.TimeoutExpired:
            reply, perr = "", "prover timed out"
        psecs = time.time() - t0
        new, approach = extract_reply(reply)
        extra = {"round": rnd, "prover": a.prover[:120], "prompt_chars": len(prompt), "prover_seconds": round(psecs, 1)}
        if new is None:
            row = {"ts": now(), "event": "check", "target": target,
                   "attempt": sum(1 for r in ledger_rows() if r.get("target") == target and r.get("event") == "check") + 1,
                   "worker": worker, "approach": f"run r{rnd}: (no lean block in reply)", "verdict": "fail",
                   "error_class": "no-candidate", "n_errors": 0, "n_gate_errors": 0, "n_sorry": 0, "axioms": [],
                   "frozen_sha": sha(frozen), "candidate_sha": "", "seconds": 0.0,
                   "first_error": ("prover stderr: " + perr if not reply.strip() else "reply: " + reply[:300])[:400]}
            row.update(extra)
            append_row(row)
            print(f"  round {rnd}: no lean block in the reply ({len(reply)} chars, {psecs:.0f}s)")
            continue
        cand = new if new.endswith("\n") else new + "\n"
        src.write_text(cand)
        g = gate(target, cand, f"run r{rnd}: {approach}", worker, a.timeout, not a.no_slot, extra=extra)
        s = score(g)
        print(f"  round {rnd}: {g['row']['verdict'].upper()} class={g['row']['error_class']} score={s} "
              f"prompt={len(prompt)}c prover={psecs:.0f}s :: {approach[:100]}")
        if s < best_score:
            best_text, best_score = cand, s
        if g["row"]["verdict"] == "pass":
            print(f"PASS {target} in round {rnd}"); return
    if src.read_text() != best_text:
        src.write_text(best_text)
    print(f"no pass after {a.rounds} rounds; restored the best candidate (score {best_score}) to {target}")
    sys.exit(1)


# ---------------------------------------------------------------- scan: candidate bridges, each name checked by Lean

SCAN_SYSTEM = "You know Mathlib well. You propose proof routes; you do not write proofs."
DEFAULT_SCANNER = default_prover(SCAN_SYSTEM)
SCAN_PROMPT = """You are scouting proof routes for Lean 4 statements against Mathlib (Lean {lean}). Do not write a proof.

Strong proofs often come through a bridge: a result Mathlib already has in an area far from where the statement
itself lives, which carries most of the weight once the statement is connected to it. List candidate bridges.

Rules:
- at least {n} candidates, spread over at least 4 different areas of Mathlib; at most a third of them from the
  statement's own area;
- each name must be the exact fully qualified name of a theorem, lemma or definition in current Mathlib or Lean
  core. Every name is checked by Lean; a name that does not exist is worthless, so do not guess or invent names;
- prefer deep results (a named theorem, a classification, a counting formula) over routine simp lemmas.

Reply with one line per candidate and nothing else:
CANDIDATE: <fully qualified name> | <Mathlib area> | <one line: how it would be used> | <one line: what has to be shown to connect it>

## Statements
```lean
{statements}```
"""
SCAN_LINE = re.compile(r"^\W*CANDIDATE:\s*(.+)$", re.M)
SCAN_NAME = re.compile(r"^[^\s()\[\]{}⟨⟩:,;`\"|@]+$")


def scan_statements(text):
    """The statements alone: comments, docstrings and theorem proofs removed, so the prompt holds no hint."""
    out = []
    for chunk, kind, name, _ in walk(strip_comments(text)):
        if kind in ("theorem", "lemma"):
            chunk = re.split(r":=\s*by\b|:=\s*\n", chunk, maxsplit=1)[0].rstrip() + " := sorry\n"
        out.append(chunk)
    return re.sub(r"\n\s*\n+", "\n\n", "".join(out)).strip() + "\n"


def parse_candidates(reply):
    cands, seen = [], set()
    for line in SCAN_LINE.findall(reply):
        parts = [p.strip() for p in line.split("|", 3)] + ["", "", ""]
        name = parts[0].strip("`*_ ").removeprefix("_root_.")
        if name and name not in seen:
            seen.add(name)
            cands.append({"name": name, "area": parts[1], "use": parts[2], "connect": parts[3]})
    return cands


def verify_names(names, timeout, slot):
    """One Lean compile with a `#check` per name. Returns {name: (status, type or reason)}. `#check` output has no
    position, so each check is preceded by a printed marker and the output is read in order."""
    res = {n: ("NOT FOUND", "not a Lean name") for n in names}
    ok = [n for n in names if SCAN_NAME.match(n)]
    text = "import Mathlib\n\n" + "".join(f'#print "SCAN-MARK {k}"\n#check {n}\n' for k, n in enumerate(ok))
    rc, out, _ = lean_text(text, "scan", timeout, slot)
    blocks, cur = {}, None
    for line in out.splitlines():
        m = re.fullmatch(r"SCAN-MARK (\d+)", line.strip())
        if m:
            cur = ok[int(m.group(1))]; blocks[cur] = []
        elif cur is not None:
            blocks[cur].append(line)
    if ok and not blocks:
        sys.exit("scan: Lean printed nothing for the #check lines:\n" + out[-1500:])
    for n in ok:
        lines = blocks.get(n, [])
        err = next((l for l in lines if re.search(r":\d+:\d+: error", l)), None)
        body = [l for l in lines if not re.search(r":\d+:\d+: (warning|info|error)", l)]
        if err or not body:
            res[n] = ("NOT FOUND", (err.split(": ", 2)[-1] if err else "no output from #check")[:160])
        else:
            dep = " (deprecated)" if any("deprecated" in l for l in lines) else ""
            res[n] = ("EXISTS" + dep, re.sub(r"\s+", " ", " ".join(body)).strip()[:400])
    return res


def scan_table(target, prover, cands, res, prompt):
    cell = lambda s: s.replace("|", "\\|").replace("\n", " ")
    rows = sorted(cands, key=lambda c: not res[c["name"]][0].startswith("EXISTS"))
    n_ok = sum(res[c["name"]][0].startswith("EXISTS") for c in cands)
    md = [f"# Scan: `{target}`", "",
          f"{now()}, prover `{prover[:120]}`. {len(cands)} candidates, {n_ok} exist in Mathlib (checked by `#check`), "
          f"{len(cands) - n_ok} not found. A scan proposes routes; it proves nothing. Only EXISTS rows are usable.", "",
          "| name | in Mathlib | type (from `#check`) | area | how it would be used | to connect it |",
          "|---|---|---|---|---|---|"]
    for c in rows:
        st, ty = res[c["name"]]
        md.append(f"| `{cell(c['name'])}` | {st} | {cell(ty)} | {cell(c['area'])} | {cell(c['use'])} | {cell(c['connect'])} |")
    md += ["", "<details><summary>Prompt sent to the prover</summary>", "", "````", prompt.rstrip(), "````", "", "</details>", ""]
    return "\n".join(md), n_ok


def cmd_scan(a):
    fz = frozen_path(a.target)
    text = (fz if fz.exists() else ROOT / a.target).read_text()
    lean_v = (ROOT / "lean-toolchain").read_text().strip().split(":")[-1]
    prompt = SCAN_PROMPT.format(lean=lean_v, n=a.min, statements=scan_statements(text))
    t0 = time.time()
    if a.reply:  # a saved reply: re-verify without a model call
        reply = Path(a.reply).read_text()
    else:
        try:
            reply = subprocess.run(a.prover, shell=True, input=prompt, capture_output=True, text=True,
                                   timeout=a.prover_timeout, cwd=ROOT).stdout
        except subprocess.TimeoutExpired:
            reply = ""
    psecs = time.time() - t0
    WORK.mkdir(parents=True, exist_ok=True)
    (WORK / f"scan_{Path(a.target).stem}.reply.txt").write_text(reply)
    cands = parse_candidates(reply)
    res = verify_names([c["name"] for c in cands], a.timeout, not a.no_slot) if cands else {}
    md, n_ok = scan_table(a.target, a.prover, cands, res, prompt)
    out = Path(a.out) if a.out else HARNESS / "scans" / f"{Path(a.target).stem}.md"
    out = out if out.is_absolute() else ROOT / out
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(md)
    append_row({"ts": now(), "event": "scan", "target": a.target, "prover": a.prover[:120],
                "frozen_sha": sha(text), "prompt_chars": len(prompt), "prover_seconds": round(psecs, 1),
                "n_candidates": len(cands), "n_exists": n_ok, "n_not_found": len(cands) - n_ok,
                "out": out.relative_to(ROOT).as_posix() if out.is_relative_to(ROOT) else str(out)})
    print(f"scan {a.target}: {len(cands)} candidates, {n_ok} EXIST, {len(cands) - n_ok} NOT FOUND "
          f"(prover {psecs:.0f}s) -> {out.relative_to(ROOT) if out.is_relative_to(ROOT) else out}")
    for c in cands:
        print(f"  {res[c['name']][0]:10} {c['name']}  [{c['area'][:40]}]")
    sys.exit(0 if cands else 1)


# ---------------------------------------------------------------- split: one file per open theorem

BRIEF = """--- worker brief: {name} ---
Prove `{full}` in `{path}` (frozen; the statement, defs and namespaces are fixed).
Compile: `cd {root} && lake env lean {path}`
Gate:    `cd {root} && harness/prove.py check {path} --approach "<one line>" --worker <you>`
Unattended: `harness/prove.py run {path} --rounds 6`
Rules: edit only this file; add helper lemmas above the theorem; no sorry, axiom, native_decide or
metaprogramming; other theorems of {target} are not available here, so prove what you need as a private
helper. Done when the gate prints PASS; report the final gate line and the approaches tried.
"""


def split_name(full):
    return re.sub(r"[^A-Za-z0-9_]", "_", full)


def split_dir(target, out=None):
    d = Path(out) if out else HARNESS / "split" / Path(target).stem
    return d if d.is_absolute() else ROOT / d


def cmd_split(a):
    text = (ROOT / a.target).read_text()
    out_dir = split_dir(a.target, a.out)
    out_dir.mkdir(parents=True, exist_ok=True)
    chunks = list(walk(text))
    targets = [(i, name, full) for i, (c, k, name, full) in enumerate(chunks) if is_target(c, k, name)]
    if not targets:
        sys.exit("no `theorem ... := by sorry` targets found")
    made = []
    for i, name, full in targets:
        keep = [c for j, (c, k, n, _) in enumerate(chunks) if j == i or not is_target(c, k, n)]
        path = out_dir / f"{split_name(full)}.lean"
        path.write_text("".join(keep))
        made.append((path.relative_to(ROOT).as_posix(), full))
    for rel, full in made:
        if not frozen_path(rel).exists() or a.refreeze:
            ns = argparse.Namespace(target=rel, refreeze=frozen_path(rel).exists(), timeout=a.timeout,
                                    no_slot=a.no_slot, reason=f"split of {a.target}" if a.refreeze else None)
            cmd_freeze(ns)
    for rel, full in made:
        print(BRIEF.format(name=full.split(".")[-1], full=full, path=rel, root=ROOT, target=a.target))


def cmd_merge(a):
    """Put each proved split file back into the target: its new helper declarations go right above the theorem,
    in the theorem's place, and its new imports join the target's. Unproved theorems keep their `sorry`."""
    src = ROOT / a.target
    text = src.read_text()
    out_dir = split_dir(a.target, a.out)
    chunks, merged, skipped = list(walk(text)), [], []
    imports = re.findall(r"^import .*$", text, flags=re.M)
    pieces = []
    for chunk, kind, name, full in chunks:
        part = out_dir / f"{split_name(full)}.lean" if is_target(chunk, kind, name) else None
        if part is None or not part.exists():
            if part is not None:
                skipped.append(full)
            pieces.append(chunk); continue
        ptext = part.read_text()
        frozen_part = frozen_path(part.relative_to(ROOT).as_posix())
        known = {norm(c) for c, *_ in walk(frozen_part.read_text() if frozen_part.exists() else text)}
        pch = list(walk(ptext))
        idx = next((j for j, (_, _, _, f) in enumerate(pch) if f == full), None)
        if idx is None or is_target(*pch[idx][:3]):
            skipped.append(full); pieces.append(chunk); continue
        helpers = [c for c, k, n, f in pch[:idx] if k and norm(c) not in known]
        pieces += helpers + [pch[idx][0]]
        imports += [i for i in re.findall(r"^import .*$", ptext, flags=re.M) if i not in imports]
        merged.append(full)
    out = "".join(pieces)
    head = re.findall(r"^import .*$", out, flags=re.M)
    extra = [i for i in imports if i not in head]
    if extra:  # add new imports after the last existing import line
        last = list(re.finditer(r"^import .*\n", out, flags=re.M))[-1]
        out = out[: last.end()] + "".join(i + "\n" for i in extra) + out[last.end():]
    WORK.mkdir(parents=True, exist_ok=True)
    backup = WORK / f"{Path(a.target).name}.before-merge-{time.strftime('%Y%m%d-%H%M%S')}"
    backup.write_text(text)
    src.write_text(out)
    print(f"merged {len(merged)} into {a.target} (backup {backup.relative_to(ROOT)}): {', '.join(merged) or '-'}")
    if skipped:
        print(f"still open (no proved split file): {', '.join(skipped)}")
    print(f"next: harness/prove.py check {a.target} --approach \"merge of split proofs\"")


# ---------------------------------------------------------------- selftest: the controls

# (target, candidate, expected class). Candidates are files in harness/tests/; targets are frozen fresh into a
# private state directory, and the rows go to harness/tests/.state/ledger.jsonl, never to the real ledger.
CONTROLS = [
    ("Toy.lean", "good.lean", "none"),
    ("Toy.lean", "weakened.lean", "statement-changed"),
    ("Toy.lean", "defchanged.lean", "statement-changed"),
    ("Toy.lean", "axiom.lean", "new-axiom"),
    ("Toy.lean", "extrahyp.lean", "statement-changed"),
    ("Toy.lean", "nsopen.lean", "scope-open"),
    ("Toy.lean", "nativedecide.lean", "new-axiom"),
    ("Toy.lean", "nsswap.lean", "statement-changed"),
    ("Toy.lean", "skipkernel.lean", "forbidden"),
    ("Toy.lean", "macrocmd.lean", "forbidden"),
    ("Toy.lean", "Toy.lean", "sorry"),
    ("Vars.lean", "vars_good.lean", "none"),
    ("Vars.lean", "vars_commgroup.lean", "statement-changed"),
    ("Tamper.lean", "tamper_instance.lean", "statement-changed"),
]


def cmd_selftest(a):
    global FROZEN, LEDGER
    state = TESTS / ".state"
    if state.exists():
        shutil.rmtree(state)
    FROZEN, LEDGER = state / "frozen", state / "ledger.jsonl"
    failures = 0
    for t in sorted({t for t, _, _ in CONTROLS}):
        cmd_freeze(argparse.Namespace(target=f"harness/tests/{t}", refreeze=False, reason=None,
                                      timeout=a.timeout, no_slot=a.no_slot))
    for t, c, want in CONTROLS:
        g = gate(f"harness/tests/{t}", (TESTS / c).read_text(), f"control: {c}", "selftest", a.timeout,
                 not a.no_slot, extra={"selftest": True})
        got = g["row"]["error_class"]
        ok = got == want and (g["row"]["verdict"] == "pass") == (want == "none")
        failures += not ok
        print(f"{'ok  ' if ok else 'FAIL'} {t:12} {c:22} want={want:17} got={got:17} {g['row']['first_error'][:80]}")
    # the scan's mechanical half, no model call: a fixed reply with one real and one invented name
    cands = parse_candidates((TESTS / "scan_reply.txt").read_text())
    res = verify_names([c["name"] for c in cands], a.timeout, not a.no_slot)
    got = [res[c["name"]][0] for c in cands]
    ok = [c["name"] for c in cands] == ["Nat.add_comm", "Nat.harnessInventedBridgeLemma"] and got == ["EXISTS", "NOT FOUND"]
    failures += not ok
    print(f"{'ok  ' if ok else 'FAIL'} scan         scan_reply.txt         want=EXISTS,NOT FOUND got={','.join(got)}")
    n = len(CONTROLS) + 1
    print(f"selftest: {n - failures}/{n} controls behave as expected (ledger {LEDGER})")
    sys.exit(1 if failures else 0)


def main():
    sys.stdout.reconfigure(line_buffering=True)  # progress shows up live when piped to a log
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = p.add_subparsers(dest="cmd", required=True)
    f = sub.add_parser("freeze"); f.add_argument("target"); f.add_argument("--refreeze", action="store_true")
    f.add_argument("--reason"); f.add_argument("--timeout", type=int, default=900); f.add_argument("--no-slot", action="store_true")
    f.set_defaults(fn=cmd_freeze)
    c = sub.add_parser("check"); c.add_argument("target"); c.add_argument("--approach", required=True)
    c.add_argument("--worker", default=os.environ.get("PROVE_WORKER", "")); c.add_argument("--timeout", type=int, default=1500)
    c.add_argument("--candidate", help="check this file against the target's frozen statements (default: the target)")
    c.add_argument("--show", type=int, default=8); c.add_argument("--width", type=int, default=700)
    c.add_argument("--no-slot", action="store_true"); c.set_defaults(fn=cmd_check)
    s = sub.add_parser("status"); s.add_argument("-v", "--verbose", action="store_true")
    s.add_argument("--all", action="store_true", help="include selftest rows"); s.set_defaults(fn=cmd_status)
    r = sub.add_parser("run", help="unattended loop: prompt a prover command, gate its reply, repeat")
    r.add_argument("target"); r.add_argument("--prover", default=os.environ.get("PROVE_PROVER", DEFAULT_PROVER),
                                             help="any shell command that reads a prompt on stdin and prints a reply")
    r.add_argument("--rounds", type=int, default=6); r.add_argument("--history", type=int, default=6)
    r.add_argument("--worker", default=os.environ.get("PROVE_WORKER", ""))
    r.add_argument("--timeout", type=int, default=1500); r.add_argument("--prover-timeout", type=int, default=900)
    r.add_argument("--no-slot", action="store_true"); r.set_defaults(fn=cmd_run)
    sc = sub.add_parser("scan", help="ask a prover for bridge lemmas from far areas, check each name with Lean")
    sc.add_argument("target"); sc.add_argument("--prover", default=DEFAULT_SCANNER,
                                               help="any shell command that reads a prompt on stdin and prints a reply")
    sc.add_argument("--out", help="default: harness/scans/<target stem>.md"); sc.add_argument("--min", type=int, default=8)
    sc.add_argument("--reply", help="use this saved reply instead of calling the prover")
    sc.add_argument("--timeout", type=int, default=900); sc.add_argument("--prover-timeout", type=int, default=900)
    sc.add_argument("--no-slot", action="store_true"); sc.set_defaults(fn=cmd_scan)
    sp = sub.add_parser("split", help="one frozen file per open theorem, plus a worker brief for each")
    sp.add_argument("target"); sp.add_argument("--out"); sp.add_argument("--refreeze", action="store_true")
    sp.add_argument("--timeout", type=int, default=900); sp.add_argument("--no-slot", action="store_true")
    sp.set_defaults(fn=cmd_split)
    mg = sub.add_parser("merge", help="put proved split files back into the target (then run check)")
    mg.add_argument("target"); mg.add_argument("--out"); mg.set_defaults(fn=cmd_merge)
    t = sub.add_parser("selftest", help="run the controls in harness/tests/ (exit 0 only if all behave)")
    t.add_argument("--timeout", type=int, default=600); t.add_argument("--no-slot", action="store_true")
    t.set_defaults(fn=cmd_selftest)
    a = p.parse_args()
    a.fn(a)


if __name__ == "__main__":
    main()
