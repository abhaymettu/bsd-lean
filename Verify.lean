/-
Copyright (c) 2026 Abhay Mettu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhay Mettu
-/
import BSD

/-!
# Axiom audit of the whole project

Run with `lake build && lake env lean Verify.lean`.

This file walks over every declaration defined in a `BSD.*` module (theorems, definitions,
instances and the auxiliary declarations Lean generates for them), collects the axioms each one
depends on, and fails with an error if any axiom other than `propext`, `Classical.choice` and
`Quot.sound` appears. A `sorry` shows up as the axiom `sorryAx`, so this is also the `sorry` check.
It then prints one line per theorem with the axioms it uses.

The list of declarations is read from the compiled environment, not written by hand, so a theorem
cannot be left out of the audit by forgetting to list it.
-/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let standard : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let names := env.constants.map₁.fold (init := (#[] : Array Name)) fun acc n _ =>
    match env.getModuleIdxFor? n with
    | some idx =>
      if (`BSD).isPrefixOf env.header.moduleNames[idx.toNat]! then acc.push n else acc
    | none => acc
  let names := names.qsort fun a b => a.toString < b.toString
  let mut theorems : Nat := 0
  let mut bad : Nat := 0
  for n in names do
    let axioms ← collectAxioms n
    let extra := axioms.filter fun a => !standard.contains a
    unless extra.isEmpty do
      bad := bad + 1
      logError m!"{n} depends on non-standard axioms: {extra}"
    if let some (.thmInfo _) := env.find? n then
      unless n.isInternalDetail do
        theorems := theorems + 1
        let sorted := axioms.qsort fun a b => a.toString < b.toString
        logInfo m!"{n}: {sorted}"
  if names.isEmpty then
    logError "no declarations found in BSD.* modules: build the project first"
  logInfo m!"AUDIT: {names.size} declarations in BSD.* modules, {theorems} theorems, \
    {bad} with non-standard axioms"
