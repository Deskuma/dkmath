/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCandidateCofixedExclusion

#print "file: DkMathTest.FLT.Note032FreyArithmeticObstructionDependencyAudit"

namespace Note032FreyArithmeticObstructionDependencyAudit

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
-- Inspect checked types, constructors and opaque proof values.
run_cmd do
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.le_iff_generator_mem #[]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.eq_smooth_torsion_of_le #[``DkMath.Lib.NumberTheory.EllipticNodalTorsionBound.card_le_of_injective_smooth_torsion]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.preimage_absorbs_of_smooth #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.eq_smooth_torsion_of_le, ``DkMath.FLT.Frey.Source.residual_fixed_of_smooth_reduction, ``DkMath.FLT.Frey.Source.inertia_difference_smooth_at_bad_address]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.narrow_failure_profile #[``DkMath.FLT.Frey.Source.inertia_difference_smooth_at_bad_address, ``DkMath.Lib.NumberTheory.EllipticSmoothReductionInertia.fixed_of_inertia_of_smooth_reduction]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.generator_not_smooth_of_narrow_failure #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.preimage_absorbs_of_smooth, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.le_iff_generator_mem]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.exists_generator_depth_of_narrow_failure #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.generator_not_smooth_of_narrow_failure, ``DkMath.Lib.NumberTheory.EllipticNodalReduction.not_hasSmoothReduction_some_iff_of_model]
  checkRoot ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction #[]
  checkRoot ``DkMath.FLT.Frey.Source.residual_exists_narrow_geometric_obstruction #[``DkMath.FLT.Frey.Source.residual_exists_narrow_absorption_counterexample, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.narrow_failure_profile, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.exists_generator_depth_of_narrow_failure]
  checkRoot ``DkMath.FLT.Frey.Source.residual_no_cofixed_of_candidate_absorption #[``DkMath.FLT.Frey.Source.residual_not_cofixed_of_class_vanishing_and_resonant_absorption]
  checkRoot ``DkMath.FLT.Frey.Source.residual_hno_of_candidate_absorption #[``DkMath.FLT.Frey.Source.residual_no_cofixed_of_candidate_absorption]
  checkRoot ``DkMath.FLT.Frey.Source.residual_no_cofixed_of_candidate_smooth_generators #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.preimage_absorbs_of_smooth, ``DkMath.FLT.Frey.Source.residual_no_cofixed_of_candidate_absorption]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.le_iff_generator_mem #[`T, `H] #[`hgenerator]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.eq_smooth_torsion_of_le #[`T, `hp5, `hq, `hqp, `haddr, `A, `hA, `hsm] #[`hclass, `hbad, `hcofixed, `hhigh, `hno, `heq]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.preimage_absorbs_of_smooth #[`T, `hp5, `hq, `hqp, `haddr, `A, `hA, `hsm, `τ, `hτ, `hy] #[`hclass, `hbad, `hcofixed, `hhigh, `hno, `habsorb]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.narrow_failure_profile #[`T, `hp5, `hq, `hqp, `haddr, `A, `hA, `τ, `hτ, `hy, `hfail] #[`hclass, `hbad, `hcofixed, `hhigh, `hno, `hsmooth, `hfixed]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.generator_not_smooth_of_narrow_failure #[`T, `hp5, `hq, `hqp, `haddr, `A, `hA, `τ, `hτ, `hy, `hfail] #[`hclass, `hbad, `hcofixed, `hhigh, `hno, `hgen]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.exists_generator_depth_of_narrow_failure #[`T, `hp5, `hq, `hqp, `haddr, `A, `hA, `τ, `hτ, `hy, `hfail] #[`hclass, `hbad, `hcofixed, `hhigh, `hno, `hdepth]
  checkInputs ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction #[`S, `L, `T, `q, `A, `τ, `y] #[`hclass, `hbad]
  checkInputs ``DkMath.FLT.Frey.Source.residual_exists_narrow_geometric_obstruction #[`S, `L, `hline, `hζ, `hp5, `hclass, `hcofixed] #[`hbad, `hbadAll, `hplacement, `hwitness]
  checkInputs ``DkMath.FLT.Frey.Source.residual_no_cofixed_of_candidate_absorption #[`S, `hζ, `hp5, `hclass, `hbadCandidate] #[`L, `hline, `hcofixed, `hbadAll, `hno]
  checkInputs ``DkMath.FLT.Frey.Source.residual_hno_of_candidate_absorption #[`S, `hζ, `hp5, `hclass, `hbadCandidate] #[`L, `hline, `hcofixed, `hbadAll, `hno]
  checkInputs ``DkMath.FLT.Frey.Source.residual_no_cofixed_of_candidate_smooth_generators #[`S, `hζ, `hp5, `hclass, `hplacement] #[`L, `hline, `hcofixed, `hbadAll, `hno]

end Note032FreyArithmeticObstructionDependencyAudit
