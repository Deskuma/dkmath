/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCyclotomicConditionalTower

#print "file: DkMathTest.FLT.Note032FreyCyclotomicConditionalTowerDependencyAudit"

namespace Note032FreyCyclotomicConditionalTowerDependencyAudit

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
-- Fifteen finite traversals inspect types, constructors and opaque proof bodies.
run_cmd do
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.finite #[]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.killed #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.finite]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.socle_mem_base #[``DkMath.FLT.Frey.Source.residual_cyclic_tower_socle_mem_base]
  checkRoot ``DkMath.FLT.Frey.Source.residual_cyclic_stage_successor #[``DkMath.FLT.Frey.Source.residual_cyclic_extension_has_stable_complement_of_class_vanishing, ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.exists_tower_step_of_stable_complement, ``DkMath.Lib.NumberTheory.CyclotomicOmegaSquareTrace.primaryWeightSquareSpace_eq_bot]
  checkRoot ``DkMath.FLT.Frey.Source.residualCyclicNext_spec #[``DkMath.FLT.Frey.Source.residual_cyclic_stage_successor]
  checkRoot ``DkMath.FLT.Frey.Source.residualCyclicTower #[``DkMath.FLT.Frey.Source.residualCyclicStageZero, ``DkMath.FLT.Frey.Source.residual_cyclic_stage_successor]
  checkRoot ``DkMath.FLT.Frey.Source.residualCyclicTower_monotone #[``DkMath.FLT.Frey.Source.residualCyclicNext_spec]
  checkRoot ``DkMath.FLT.Frey.Source.residualCyclicTower_profile #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.socle_mem_base, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.killed]
  checkRoot ``DkMath.FLT.Frey.Source.residualCyclicTower_lift #[``DkMath.Lib.Algebra.CyclicPrimePowerScalar.range_nsmul_eq_ker, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.killed]
  checkRoot ``DkMath.FLT.Frey.Source.mem_residualCyclicTowerUnion #[``DkMath.FLT.Frey.Source.residualCyclicTower_monotone]
  checkRoot ``DkMath.FLT.Frey.Source.residualCyclicTowerUnion_primary #[``DkMath.FLT.Frey.Source.mem_residualCyclicTowerUnion, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.killed]
  checkRoot ``DkMath.FLT.Frey.Source.residualCyclicTowerUnion_divisible #[``DkMath.FLT.Frey.Source.residualCyclicTower_lift]
  checkRoot ``DkMath.FLT.Frey.Source.residualCyclicTowerUnion_stable #[``DkMath.FLT.Frey.Source.mem_residualCyclicTowerUnion]
  checkRoot ``DkMath.FLT.Frey.Source.residualCyclicTowerUnion_socle #[``DkMath.FLT.Frey.Source.mem_residualCyclicTowerUnion, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.socle_mem_base]
  checkRoot ``DkMath.FLT.Frey.Source.residualCyclicTowerUnion_infinite #[``DkMath.FLT.Frey.Source.mem_residualCyclicTowerUnion]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.finite #[`T] #[`hclass, `hbad, `hfinite]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.killed #[`T, `x, `hx] #[`hclass, `hbad, `hkill]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.socle_mem_base #[`T, `hline, `hx, `hpx] #[`hclass, `hbad, `hcofixed]
  checkInputs ``DkMath.FLT.Frey.Source.residual_cyclic_stage_successor #[`S, `L, `hline, `hcofixed, `hζ, `hp5, `T, `hbad, `hclass] #[`D, `hcompl, `hzero, `hrank, `htrace, `hunit, `hnext]
  checkInputs ``DkMath.FLT.Frey.Source.residualCyclicTower #[`S, `L, `hline, `hcofixed, `hζ, `hp5, `hclass, `hbad] #[`K, `hnext, `hzero, `hrank, `htrace, `hunit]
  checkInputs ``DkMath.FLT.Frey.Source.residualCyclicTower_lift #[`S, `hclass, `hbad, `n, `x, `hx] #[`hlift, `hnext]
  checkInputs ``DkMath.FLT.Frey.Source.residualCyclicTowerUnion_socle #[`S, `hclass, `hbad, `x] #[`hdown, `hnext]
  checkInputs ``DkMath.FLT.Frey.Source.residualCyclicTowerUnion_infinite #[`S, `L, `hline, `hcofixed, `hζ, `hp5, `hclass, `hbad] #[`hinfinite, `habsorb, `hCH, `hnext]

end Note032FreyCyclotomicConditionalTowerDependencyAudit
