# prove.py: a proof-loop harness for Lean 4

A small research harness for proving formal statements: one Python 3 file, standard library only. Point it
at a Lean file whose theorems end in `sorry`. It freezes the statements, then gates each attempt. An attempt
passes only if it compiles and proves the frozen statements as written: no `sorry`, no new axiom, no edited
statement or definition. Every attempt goes into a ledger. The harness can run the whole loop unattended
with any model, and it can split a file into one lemma per worker.

Nothing in it is specific to elliptic curves or number theory. `examples/SquareZero.lean` is linear
algebra and went through the same unattended loop (see the ledger).

## Point it at a new statement

```sh
cd ~/code/bsd-lean                                   # any Lake project with Mathlib
harness/prove.py freeze path/To/Statements.lean      # record the statements (the file must compile)
harness/prove.py run    path/To/Statements.lean      # unattended: 6 rounds of prompt, gate, feed back
harness/prove.py status -v                           # what happened
```

By hand (a human or an agent writes the proof): edit the file, then
`harness/prove.py check path/To/Statements.lean --approach "one line: what this attempt does" --worker NAME`.
The command prints PASS or FAIL with an error class and exits 0 only on PASS.

## Commands

| command | what it does |
|---|---|
| `freeze <target> [--refreeze --reason "..."]` | copies the statement file to `harness/frozen/`, computes its fingerprints, logs a `freeze` row. Changing frozen statements later needs `--refreeze` and a reason, which is logged. |
| `check <target> --approach "..." [--worker W] [--candidate FILE]` | gates the target file (or another candidate file) against the frozen copy and logs a `check` row |
| `run <target> [--prover CMD] [--rounds N]` | the unattended loop: build a prompt, pipe it to `CMD`, take the last ```` ```lean ```` block of the reply as the new file, gate it, log it. Stops on PASS; otherwise restores the best candidate (fewest `sorry` plus errors). |
| `split <target> [--out DIR]` | one frozen file per open theorem (shared preamble, all definitions, no other open theorems), plus a ready-to-paste worker brief for each |
| `merge <target> [--out DIR]` | puts each proved split file back: its new helper lemmas go right above the theorem, its new imports join the target's. Then run `check` on the target. |
| `scan <target> [--prover CMD] [--out FILE]` | asks the prover for bridge lemmas from far areas of Mathlib, checks every proposed name with one `#check` compile, writes `harness/scans/<stem>.md` and logs a `scan` row (see below) |
| `status [-v] [--all]` | one line per target, PASS or open, with error-class counts; `-v` lists every attempt; `--all` includes selftest rows |
| `selftest` | runs the controls in `tests/` and exits non-zero unless each is classified as expected |

The prover is any shell command that reads a prompt on stdin and prints a reply, so the loop works with any
model. The default is the Claude Code CLI in print mode (`claude -p --model sonnet`). Set
`--prover` or `PROVE_PROVER` to use something else, for example a local model or a script. Each prompt
holds the frozen file, the current candidate, the errors from the last check, and the last six ledger rows
for the target, so the prover sees what has already failed. Prompts stay at a few thousand characters.

## Scan: look for a route before proving

The best proofs in this repo came through bridges to results Mathlib already had far from the goal: the rank
of `y² = x³ - 432` through `fermatLastTheoremThree`, a point count through `quadraticChar_card_sqrts`,
infinitely many vanishing coefficients through Dirichlet's theorem. `scan` makes looking for such a bridge a
step of its own.

```sh
harness/prove.py scan BSD/FermatCubic.lean                    # default prover
harness/prove.py scan BSD/FermatCubic.lean --prover "CMD"     # any command that reads stdin, prints a reply
harness/prove.py scan BSD/FermatCubic.lean --reply saved.txt  # re-check a saved reply, no model call
```

The prompt holds the statements only: comments, docstrings and proofs are stripped, so it cannot hint at an
answer the file's prose names. It asks for at least 8 candidates over at least 4 areas of Mathlib, each as a
fully qualified name, its area, how it would be used and what has to be shown to connect it. Then the
mechanical half: every name gets a `#check` in one scratch file compiled once with `lake env lean` (through
`heavy-slot` when it is on PATH). The table in `harness/scans/<stem>.md` lists each candidate as `EXISTS`, with
the type Lean printed, or `NOT FOUND`, with Lean's error; the prompt sent is kept at the bottom. The ledger
row has `event: scan`, `n_candidates`, `n_exists`, `n_not_found` and `out`.

Read it as a shortlist. An `EXISTS` row means the name is real and has the printed type, nothing more: the
"how it would be used" column is the model's guess. A scan proposes routes; it proves nothing. The proof
still goes through `check` or `run`. `selftest` includes a control for the mechanical half
(`tests/scan_reply.txt`: one real name, one invented, no model call).

## What the gate checks

The candidate is compiled with a generated check section appended to it:

1. **Compiles.** Errors in the candidate's own lines are classified: `unknown-name`, `type-mismatch`,
   `unsolved-goals`, `tactic-failed`, `instance`, `syntax`, `timeout`, `other`.
2. **No `sorry`** (`sorry`).
3. **No open scope.** Every `namespace` and `section` is closed (`scope-open`).
4. **Same statement, same name.** Each frozen theorem is re-stated and closed with `apply _root_.<full name>`,
   where the full name is the one the frozen file declares. A weaker conclusion, an extra hypothesis, a
   stronger instance, or the theorem moved to another namespace all fail (`statement-changed`).
5. **Same definitions.** Each frozen `def`/`abbrev` is re-stated and must be `rfl`-equal to the candidate's.
   `instance`/`structure`/`inductive`/`class` are compared as normalized text.
6. **Same meaning.** A fingerprint of each frozen theorem and def from the frozen file alone (type hash,
   top-level binder kinds, universe names, value hash) must match the re-stated one after the candidate.
   Without this, a candidate could change what the statement means, for both itself and the re-statement,
   with a high-priority instance, a notation or a leftover `open` (`tests/tamper_instance.lean` "proves" a
   false statement that way, and v1 passed it).
7. **Standard axioms only** (`propext`, `Classical.choice`, `Quot.sound`), and no `axiom` declared
   (`new-axiom`; `native_decide` lands here through its compiler axiom).
8. **No bypass commands** (`forbidden`): `run_cmd`, `elab`, `macro_rules`, `#eval`, `#exit`, `initialize`,
   command-level macros, `Lean.Elab`/`Lean.Meta`/environment edits, `unsafe`, `implemented_by`, `extern`,
   `debug.skipKernelTC`, and any identifier containing `harness_`/`HARNESS`.

## Frozen-file format

- Targets: `theorem`/`lemma` at column 0 whose proof ends in the single token `sorry`. Theorems in the frozen
  file that are already proved are context and are not re-checked.
- Definitions: `def`/`abbrev` at column 0, non-recursive (they are compared by `rfl`).
- Everything else at column 0 (`namespace`, `section`, `variable`, `open`, comments) is kept as context for
  the re-statements.
- A theorem may use section `variable`s and instance arguments (`tests/Vars.lean`).

## What the gate does not catch

- **Generalizations pass.** The check is "the frozen statement follows from the candidate theorem by
  `exact`, or by `apply` plus `assumption`". A candidate theorem with fewer hypotheses or a weaker typeclass
  passes as long as its definitions still match.
- The fingerprint covers the whole type's hash but binder kinds (explicit, implicit, instance) only at the
  top level of the statement. Binder names are not covered at all.
- `instance`/`structure`/`inductive`/`class` declarations are compared as text only, not by meaning.
- Recursive definitions cannot be frozen (the `rfl` comparison needs a plain body).
- The forbidden list is textual. It is a tripwire for accidents and lazy shortcuts, not a sandbox against
  an adversary who writes Lean metaprograms. The kernel check and `#print axioms` remain the real guarantee.
- Proof quality is not judged: Mathlib style, line length, non-terminal `simp`, naming. A human reviews that.
- `split` keeps the shared preamble and every definition but drops the other open theorems. A lemma that
  needs an earlier sibling has to prove it as a helper. `merge` only moves helpers that sit right above the
  theorem in the split file.

## Reading the ledger

`harness/ledger.jsonl` has one JSON object per line. `event` is `freeze`, `refreeze` or `check`. A check row
has `target`, `attempt` (counted per target), `worker`, `approach`, `verdict` (`pass`/`fail`), `error_class`
(as above, or `none` on pass, `no-candidate` when a prover reply held no lean block), `n_errors`,
`n_gate_errors`, `n_sorry`, `axioms`, `frozen_sha`, `candidate_sha`, `seconds`, and `first_error`. Rows
written by `run` also carry `round`, `prover`, `prompt_chars` and `prover_seconds`.

`harness/prove.py status -v` is the readable view. It shows one line per target, then each attempt with its
time, verdict, class, worker and approach. The approach lines are the research record: they show what was
tried and what failed, so the next attempt does not repeat it.

Selftest rows go to `tests/.state/ledger.jsonl`, never to the real ledger, and `status` hides
`harness/tests/` targets unless given `--all`. `PROVE_STATE=<dir>` points the frozen directory and ledger at
`<dir>` for dry runs. `PROVE_KEEP=1` keeps the generated check file and Lean's output in `harness/.work/` for
debugging.

## Files

- `prove.py` is the harness.
- `frozen/` holds the frozen copies, plus `*.sig.json` fingerprint caches keyed by the frozen file's hash.
- `ledger.jsonl` is the attempt ledger.
- `scans/` holds the `scan` tables, one per target.
- `tests/` holds the control targets (`Toy`, `Vars`, `Tamper`) and their candidates for `selftest`.
- `examples/` holds the generality example.
