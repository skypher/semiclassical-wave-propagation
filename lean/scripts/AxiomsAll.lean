import Qschubert

/-!
Complete axiom check. Every declaration defined in a module of this project (module name `Qschubert` or
`Qschubert.*`; theorems, definitions and auxiliary declarations, in any namespace) is checked with
`Lean.collectAxioms`, the function behind `#print axioms`. Expected output: no declaration depends on an axiom
other than `propext`, `Classical.choice`, `Quot.sound`. Run: `lake env lean scripts/AxiomsAll.lean`.
-/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mods := env.header.moduleNames
  let mut n : Nat := 0
  let mut nThm : Nat := 0
  let mut nOut : Nat := 0
  let mut used : NameSet := {}
  let mut bad : Array (Name × List Name) := #[]
  for (c, info) in env.constants.toList do
    let inProject : Bool := match env.getModuleIdxFor? c with
      | some idx => (`Qschubert).isPrefixOf mods[idx.toNat]!
      | none => false
    if inProject then
      n := n + 1
      if info matches .thmInfo _ then nThm := nThm + 1
      if !(`Qschubert).isPrefixOf c then nOut := nOut + 1
      let axs ← Lean.collectAxioms c
      for a in axs do used := used.insert a
      let extra := axs.toList.filter (fun a => !allowed.contains a)
      if !extra.isEmpty then bad := bad.push (c, extra)
  logInfo m!"AXIOMS-ALL: {n} declarations in the modules of this project ({nThm} theorems; {nOut} outside the namespace Qschubert); axioms used anywhere: {used.toList}; declarations with another axiom: {bad.size}"
  for (c, e) in bad do logInfo m!"BAD {c}: {e}"
  if !bad.isEmpty then throwError "non-standard axioms found"
