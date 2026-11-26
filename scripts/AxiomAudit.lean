/-
Copyright (c) 2026 Tom Hutchcroft. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Axiom audit of the library (D-4, D-34). Run from the repository root after a build:

  lake env lean --run scripts/AxiomAudit.lean [ROOT]      (default ROOT: PercLib)

Every constant declared in a module under ROOT (public or private, theorems and
definitions alike) must depend on no axiom other than `propext`, `Classical.choice`
and `Quot.sound`. A `sorry` shows up as `sorryAx` and fails the audit. Exits 1 and lists
each offending declaration otherwise.
-/
import Lean

open Lean

def allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]

def main (args : List String) : IO UInt32 := do
  let root := (args.headD "PercLib").toName
  initSearchPath (← findSysroot)
  unsafe enableInitializersExecution
  let env ← importModules #[{ module := root }] {} (trustLevel := 1024) (loadExts := true)
  let action : CoreM (Nat × Array (Name × Array Name)) := do
    let env ← getEnv
    let mut count := 0
    let mut bad := #[]
    for (name, _) in env.constants.toList do
      let some idx := env.getModuleIdxFor? name | continue
      unless root.isPrefixOf env.header.moduleNames[idx.toNat]! do continue
      count := count + 1
      let axs ← collectAxioms name
      let extra := axs.filter (fun a => !allowed.contains a)
      unless extra.isEmpty do bad := bad.push (name, extra)
    return (count, bad)
  let ((count, bad), _) ← Core.CoreM.toIO action
    { fileName := "<axiom-audit>", fileMap := default, maxHeartbeats := 0 } { env }
  for (name, extra) in bad do
    IO.println s!"FAIL {name}: {extra.toList}"
  if bad.isEmpty then
    IO.println s!"Axiom audit passed: {count} constants under {root}, only {allowed}."
    return 0
  else
    IO.println s!"Axiom audit failed: {bad.size} of {count} constants use other axioms."
    return 1
