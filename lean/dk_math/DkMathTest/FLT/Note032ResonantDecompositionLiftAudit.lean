/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyResonantDecompositionLift

#print "file: DkMathTest.FLT.Note032ResonantDecompositionLiftAudit"

namespace Note032ResonantDecompositionLiftAudit

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
-- Each root traverses the full checked dependency graph, including opaque proofs and types.
run_cmd do
  checkRoot ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.generatorValue_order_eq_prime #[``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixedKernel_order_eq_prime, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.generator_evaluation_injective]
  checkRoot ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.generatorValue_nsmul_mod #[]
  checkRoot ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.generatorValue_q_smul_plus #[]
  checkRoot ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.generatorValue_q_smul_minus #[]
  checkRoot ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.frobenius_fixed_resonant_signs #[``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.frobenius_fixed_criterion, ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.generatorValue_q_smul_plus, ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.generatorValue_q_smul_minus]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fullInertiaCoefficientTopology #[]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fullInertiaCoefficientDiscrete #[]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedQuotientCoefficientTopology #[]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedQuotientCoefficientDiscrete #[]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedDecomposition_orbit_continuous #[]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.quotientDecomposition_orbit_continuous #[]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.kernelDecomposition_orbit_evaluation_continuous #[]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.kernelDecomposition_stabilizer_isClosed #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.kernel_fixed_iff_generator_evaluation, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.kernelDecomposition_orbit_evaluation_continuous]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedDecompositionCoefficientTopology #[]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fullDecompositionCoefficient #[]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.quotientDecompositionCoefficient #[]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.decompositionCoefficientInclusion #[]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.decompositionCoefficientProjection #[]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.decompositionCoefficientSequence #[]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.decompositionCoefficientSequence_shortExact #[]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.decompositionConnecting #[]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.decompositionCosetH0 #[]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.decomposition_difference_mem_fixed #[]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.decompositionConnectingCocycle #[]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.decompositionConnectingCocycle_continuous #[]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.decompositionConnectingCocycle_class #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.decompositionCoefficientSequence_shortExact, ``groupCohomology.δ₀_apply]
  checkRoot ``DkMath.FLT.Frey.Source.inertiaToDecomposition #[]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.decompositionInertiaCoefficient #[]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.decompositionInertiaRestriction #[]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.decompositionCocycle_restrict #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.continuousCocycle_global_restriction]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.decompositionClass_restrict_kernel #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.decompositionCocycle_restrict, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedCosetKernelElement_val]
  checkRoot ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.exists_prime_sign_frobenius_criterion #[]
  checkRoot ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.decomposition_lift_of_kernel_fixed #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.kernel_fixed_iff_quotient_fixed, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.decompositionClass_restrict_kernel, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.decompositionConnectingCocycle_continuous, ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixed_H1_nonzero]
  checkInputs ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.generatorValue_order_eq_prime #[`h, `hp5] #[`hclass, `hcofixed, `hglobal, `hselmer, `hgen, `hcyclic, `hherbrand, `hreflect, `heigen]
  checkInputs ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.generatorValue_nsmul_mod #[`h, `hp5] #[`hclass, `hcofixed, `hglobal, `hselmer, `hgen, `hcyclic, `hherbrand, `hreflect, `heigen]
  checkInputs ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.generatorValue_q_smul_plus #[`h, `hp5] #[`hclass, `hcofixed, `hglobal, `hselmer, `hgen, `hcyclic, `hherbrand, `hreflect, `heigen]
  checkInputs ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.generatorValue_q_smul_minus #[`h, `hp5] #[`hclass, `hcofixed, `hglobal, `hselmer, `hgen, `hcyclic, `hherbrand, `hreflect, `heigen]
  checkInputs ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.frobenius_fixed_resonant_signs #[`h, `hp5] #[`hclass, `hcofixed, `hglobal, `hselmer, `hgen, `hcyclic, `hherbrand, `hreflect, `heigen]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fullInertiaCoefficientTopology #[`T, `A] #[`hclass, `hcofixed, `hglobal, `hselmer, `hgen, `hcyclic, `hherbrand, `hreflect, `heigen]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fullInertiaCoefficientDiscrete #[`T, `A] #[`hclass, `hcofixed, `hglobal, `hselmer, `hgen, `hcyclic, `hherbrand, `hreflect, `heigen]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedQuotientCoefficientTopology #[`T, `A] #[`hclass, `hcofixed, `hglobal, `hselmer, `hgen, `hcyclic, `hherbrand, `hreflect, `heigen]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedQuotientCoefficientDiscrete #[`T, `A] #[`hclass, `hcofixed, `hglobal, `hselmer, `hgen, `hcyclic, `hherbrand, `hreflect, `heigen]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedDecomposition_orbit_continuous #[`T, `A] #[`hclass, `hcofixed, `hglobal, `hselmer, `hgen, `hcyclic, `hherbrand, `hreflect, `heigen]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.quotientDecomposition_orbit_continuous #[`T, `A] #[`hclass, `hcofixed, `hglobal, `hselmer, `hgen, `hcyclic, `hherbrand, `hreflect, `heigen]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.kernelDecomposition_orbit_evaluation_continuous #[`T, `A] #[`hclass, `hcofixed, `hglobal, `hselmer, `hgen, `hcyclic, `hherbrand, `hreflect, `heigen]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.kernelDecomposition_stabilizer_isClosed #[`T, `A] #[`hclass, `hcofixed, `hglobal, `hselmer, `hgen, `hcyclic, `hherbrand, `hreflect, `heigen]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedDecompositionCoefficientTopology #[`T, `A] #[`hclass, `hcofixed, `hglobal, `hselmer, `hgen, `hcyclic, `hherbrand, `hreflect, `heigen]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fullDecompositionCoefficient #[`T, `A] #[`hclass, `hcofixed, `hglobal, `hselmer, `hgen, `hcyclic, `hherbrand, `hreflect, `heigen]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.quotientDecompositionCoefficient #[`T, `A] #[`hclass, `hcofixed, `hglobal, `hselmer, `hgen, `hcyclic, `hherbrand, `hreflect, `heigen]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.decompositionCoefficientInclusion #[`T, `A] #[`hclass, `hcofixed, `hglobal, `hselmer, `hgen, `hcyclic, `hherbrand, `hreflect, `heigen]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.decompositionCoefficientProjection #[`T, `A] #[`hclass, `hcofixed, `hglobal, `hselmer, `hgen, `hcyclic, `hherbrand, `hreflect, `heigen]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.decompositionCoefficientSequence #[`T, `A] #[`hclass, `hcofixed, `hglobal, `hselmer, `hgen, `hcyclic, `hherbrand, `hreflect, `heigen]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.decompositionCoefficientSequence_shortExact #[`T, `A] #[`hclass, `hcofixed, `hglobal, `hselmer, `hgen, `hcyclic, `hherbrand, `hreflect, `heigen]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.decompositionConnecting #[`T, `A] #[`hclass, `hcofixed, `hglobal, `hselmer, `hgen, `hcyclic, `hherbrand, `hreflect, `heigen]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.decompositionCosetH0 #[`T, `A, `x, `hz] #[`hclass, `hcofixed, `hglobal, `hselmer, `hgen, `hcyclic, `hherbrand, `hreflect, `heigen]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.decomposition_difference_mem_fixed #[`T, `A, `x, `hz] #[`hclass, `hcofixed, `hglobal, `hselmer, `hgen, `hcyclic, `hherbrand, `hreflect, `heigen]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.decompositionConnectingCocycle #[`T, `A, `x, `hz] #[`hclass, `hcofixed, `hglobal, `hselmer, `hgen, `hcyclic, `hherbrand, `hreflect, `heigen]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.decompositionConnectingCocycle_continuous #[`T, `A, `x, `hz] #[`hclass, `hcofixed, `hglobal, `hselmer, `hgen, `hcyclic, `hherbrand, `hreflect, `heigen]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.decompositionConnectingCocycle_class #[`T, `A, `x, `hz] #[`hclass, `hcofixed, `hglobal, `hselmer, `hgen, `hcyclic, `hherbrand, `hreflect, `heigen]
  checkInputs ``DkMath.FLT.Frey.Source.inertiaToDecomposition #[`A] #[`hclass, `hcofixed, `hglobal, `hselmer, `hgen, `hcyclic, `hherbrand, `hreflect, `heigen]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.decompositionInertiaCoefficient #[`T, `A] #[`hclass, `hcofixed, `hglobal, `hselmer, `hgen, `hcyclic, `hherbrand, `hreflect, `heigen]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.decompositionInertiaRestriction #[`T, `A] #[`hclass, `hcofixed, `hglobal, `hselmer, `hgen, `hcyclic, `hherbrand, `hreflect, `heigen]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.decompositionCocycle_restrict #[`T, `A, `x, `hz] #[`hclass, `hcofixed, `hglobal, `hselmer, `hgen, `hcyclic, `hherbrand, `hreflect, `heigen]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.decompositionClass_restrict_kernel #[`T, `A, `x, `hz] #[`hclass, `hcofixed, `hglobal, `hselmer, `hgen, `hcyclic, `hherbrand, `hreflect, `heigen]
  checkInputs ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.exists_prime_sign_frobenius_criterion #[`h, `hp5] #[`hclass, `hcofixed, `hglobal, `hselmer, `hgen, `hcyclic, `hherbrand, `hreflect, `heigen]
  checkInputs ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.decomposition_lift_of_kernel_fixed #[`h, `hp5, `hD] #[`hclass, `hcofixed, `hglobal, `hselmer, `hgen, `hcyclic, `hherbrand, `hreflect, `heigen]

end Note032ResonantDecompositionLiftAudit
