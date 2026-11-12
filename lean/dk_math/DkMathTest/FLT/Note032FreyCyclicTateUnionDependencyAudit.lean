/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCyclicTateUnion

#print "file: DkMathTest.FLT.Note032FreyCyclicTateUnionDependencyAudit"

namespace Note032FreyCyclicTateUnionDependencyAudit

open Lean Elab Command

private def forbidden (n : Name) : Bool :=
  let s := (privateToUserName n).toString
  n == ``sorryAx || s.startsWith "P2M." || s.startsWith "P2MW." ||
    s.startsWith "FltRegular." || s.startsWith "FreyPackage." ||
    s.startsWith "DkMath.FLT.Kummer." || s.contains "fermatLastTheorem" ||
    s.contains "fermat_last_theorem" || s.contains "fermatFive_no_positive_solution"

private def checkRoot (root : Name) (required : Array Name) : CommandElabM Unit := do
  let env ← getEnv
  let mut pending := #[root]
  let mut visited : NameSet := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    if visited.contains n then continue
    visited := visited.insert n
    if forbidden n then throwError "Forbidden dependency: {n}"
    let some info := env.checked.get.find? n | throwError "Missing constant: {n}"
    pending := pending ++ info.type.getUsedConstants
    if let .inductInfo v := info then pending := pending ++ v.ctors.toArray
    if let .axiomInfo _ := info then
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains n do
        throwError "Unexpected axiom: {n}"
    if let some value := info.value? (allowOpaque := true) then
      pending := pending ++ value.getUsedConstants
  for n in required do
    unless visited.contains n do throwError "Required theorem absent: {n}"
  logInfo m!"PASS: {root}; {visited.size} reachable constants; required actual theorems present."

private def binderNames : Expr → List Name
  | .forallE n _ b _ => n :: binderNames b
  | .letE n _ _ b _ => n :: binderNames b
  | _ => []

private def checkInputs (root : Name) (required banned : Array Name) : CommandElabM Unit := do
  let env ← getEnv
  let some info := env.checked.get.find? root | throwError "Missing constant: {root}"
  let names := binderNames info.type
  for n in required do
    unless names.contains n do throwError "Required input absent in {root}: {n}"
  for n in banned do
    if names.contains n then throwError "Unexpected input in {root}: {n}"
  logInfo m!"PASS inputs: {root}; remaining arithmetic inputs explicit."

set_option maxHeartbeats 0 in
-- Thirteen finite traversals inspect types, constructors and opaque proof bodies.
run_cmd do
  checkRoot ``DkMath.Lib.Algebra.CyclicPrimePowerTorsion.mem_iff_killed #[``IsAddCyclic.card_nsmulAddMonoidHom_ker]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.mem_iff_killed_in_later #[``DkMath.Lib.Algebra.CyclicPrimePowerTorsion.mem_iff_killed]
  checkRoot ``DkMath.FLT.Frey.Source.residualCyclicTowerUnion_torsion #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.mem_iff_killed_in_later, ``DkMath.FLT.Frey.Source.mem_residualCyclicTowerUnion, ``DkMath.FLT.Frey.Source.residualCyclicTower_monotone]
  checkRoot ``DkMath.FLT.Frey.Source.residualUnionTate_inclusion #[``DkMath.Lib.Algebra.PrimePowerTateSequence.mapLinear]
  checkRoot ``DkMath.FLT.Frey.Source.residualUnionTate_inclusion_injective #[``DkMath.Lib.Algebra.PrimePowerTateSequence.map_injective]
  checkRoot ``DkMath.FLT.Frey.Source.residualUnionTateToLine #[``DkMath.FLT.Frey.Source.residualCyclicTowerUnion_torsion, ``DkMath.Lib.Algebra.PrimePowerTateSequence.killed]
  checkRoot ``DkMath.FLT.Frey.Source.residualUnionTateLineEquiv #[``DkMath.FLT.Frey.Source.residualUnionTateToLine, ``DkMath.FLT.Frey.Source.mem_residualCyclicTowerUnion]
  checkRoot ``DkMath.FLT.Frey.Source.residualUnionTateEquiv #[``DkMath.FLT.Frey.Source.residualUnionTateLineEquiv, ``DkMath.FLT.Frey.Source.residualCyclicTateLineEquiv]
  checkRoot ``DkMath.FLT.Frey.Source.residualUnionTateLineEquiv_inclusion #[``DkMath.FLT.Frey.Source.residualUnionTateLineEquiv, ``DkMath.FLT.Frey.Source.residualUnionTate_inclusion]
  checkRoot ``DkMath.FLT.Frey.Source.residualTowerUnionAction #[``DkMath.FLT.Frey.Source.residualCyclicTowerUnion_stable]
  checkRoot ``DkMath.FLT.Frey.Source.residualUnionTate_inclusion_equivariant #[``DkMath.FLT.Frey.Source.residualTowerUnionAction, ``DkMath.Lib.Algebra.PrimePowerTateSequence.actionLinear]
  checkRoot ``DkMath.FLT.Frey.Source.residualUnionTate_action_scalar #[``DkMath.FLT.Frey.Source.residualCyclicTateLine_action_scalar, ``DkMath.FLT.Frey.Source.residualUnionTate_inclusion_injective, ``DkMath.FLT.Frey.Source.residualUnionTate_inclusion_equivariant]
  checkRoot ``DkMath.FLT.Frey.Source.residualCyclicTateVector_not_p_multiple #[``DkMath.FLT.Frey.Source.residualTateSeed_ne_zero, ``DkMath.Lib.Algebra.PrimePowerTateSequence.killed, ``DkMath.Lib.Algebra.PrimePowerTateSequence.nsmul_eq_of_residue]
  checkInputs ``DkMath.Lib.Algebra.CyclicPrimePowerTorsion.mem_iff_killed #[`hab, `K, `B, `hK, `hBK, `hB, `hkill] #[`hp, `hclass, `hbad, `heq]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.mem_iff_killed_in_later #[`T, `V, `hnm, `hTV, `x] #[`hclass, `hbad, `heq]
  checkInputs ``DkMath.FLT.Frey.Source.residualCyclicTowerUnion_torsion #[`S, `L, `hline, `hcofixed, `hζ, `hp5, `hclass, `hbad, `n, `x] #[`htorsion, `hdescent]
  checkInputs ``DkMath.FLT.Frey.Source.residualUnionTateToLine #[`S, `L, `hline, `hcofixed, `hζ, `hp5, `hclass, `hbad] #[`htorsion, `hmap]
  checkInputs ``DkMath.FLT.Frey.Source.residualUnionTateLineEquiv #[`S, `L, `hline, `hcofixed, `hζ, `hp5, `hclass, `hbad] #[`hequiv, `hsurj, `hinj]
  checkInputs ``DkMath.FLT.Frey.Source.residualUnionTateEquiv #[`S, `L, `hline, `hcofixed, `hζ, `hp5, `hclass, `hbad] #[`hrank, `hfree, `hequiv]
  checkInputs ``DkMath.FLT.Frey.Source.residualTowerUnionAction #[`S, `L, `hline, `hcofixed, `hζ, `hp5, `hclass, `hbad] #[`hact, `hstable]
  checkInputs ``DkMath.FLT.Frey.Source.residualUnionTate_inclusion_equivariant #[`S, `L, `hline, `hcofixed, `hζ, `hp5, `hclass, `hbad, `σ, `x] #[`hequivariance]
  checkInputs ``DkMath.FLT.Frey.Source.residualUnionTate_action_scalar #[`S, `L, `hline, `hcofixed, `hζ, `hp5, `hclass, `hbad, `σ, `x] #[`hchar, `hscalar, `hfixed]
  checkInputs ``DkMath.FLT.Frey.Source.residualCyclicTateVector_not_p_multiple #[`S, `L, `hline, `hcofixed, `hζ, `hp5, `hclass, `hbad, `w] #[`hprimitive, `hrank, `hfree]

end Note032FreyCyclicTateUnionDependencyAudit
