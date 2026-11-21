# AGENTS.md

Setup and working rules for a person or a coding agent picking this repository up.

## What this is

A Lean 4 project on top of Mathlib: theorems about the L-function of an elliptic curve
(`BSD/*.lean`), an axiom audit (`Verify.lean`) and a small proof-loop harness (`harness/`).
`README.md` says what is proved and what is not.

## Setup

1. Install `elan`, the Lean toolchain manager (`brew install elan-init` on macOS, or see
   https://lean-lang.org/install). The toolchain version is pinned in `lean-toolchain`.
2. From the repository root:

   ```
   lake exe cache get        # download prebuilt Mathlib; never build Mathlib from source
   lake build                # compiles the files in BSD/
   lake env lean Verify.lean # axiom audit; the last line must report 0 with non-standard axioms
   ```

   The Mathlib checkout and cache take about 7 GB of disk under `.lake/`.
3. Python 3 for `harness/prove.py` (run here with Python 3.14). It has no dependencies outside the standard
   library.

## Checking a change

- One file, fast: `lake env lean BSD/<File>.lean`. A file that imports another file of this project
  needs that file built first: `lake build BSD.<Module>`.
- The whole project: `lake build && lake env lean Verify.lean`.
- A proof against its frozen statement: `harness/prove.py check BSD/<File>.lean --approach "<what changed>"`.
  It fails on `sorry`, a new axiom, or a statement that no longer matches the frozen copy in
  `harness/frozen/`.
- The harness itself: `harness/prove.py selftest` (controls that must pass and controls that must be
  rejected).

## Rules

- A result counts only when it compiles. No `sorry`, no `axiom`, no `native_decide`, no option that
  weakens kernel checking.
- Statements are frozen before they are proved. To change one, re-freeze in the open:
  `harness/prove.py freeze <file> --refreeze --reason "<what changed and why>"`. Never weaken a
  statement to make a proof go through.
- Do not run `lake update`: it moves the Mathlib pin, and the proofs are checked against the pinned
  version only.
- Follow Mathlib style: lines of at most 100 characters, a docstring on every main theorem, a module
  docstring listing the main results, Mathlib naming conventions.
- Adding a file: import it in `BSD.lean` so `lake build` and the audit cover it.

## Layout

| Path | What |
|---|---|
| `BSD/` | the Lean files, one topic each |
| `BSD.lean` | root module, imports every file |
| `Verify.lean` | axiom audit over every declaration of the project |
| `harness/prove.py` | freeze, check, run, scan, split, merge, status, selftest |
| `harness/frozen/` | frozen statement files and their fingerprints |
| `harness/scans/` | `scan` tables: candidate bridge lemmas, each name checked by Lean |
| `harness/ledger.jsonl` | one row per gate attempt |
| `PR-DRAFT.md` | how the files would be split into Mathlib pull requests |
| `scripts/ap_chart.py` | draws `docs/hero.png` by brute-force point counts |
