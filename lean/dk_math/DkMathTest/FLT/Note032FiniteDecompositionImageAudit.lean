/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyFiniteImageResonantLift

#print "file: DkMathTest.FLT.Note032FiniteDecompositionImageAudit"

namespace Note032FiniteDecompositionImageAudit

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
-- Each root traverses the full checked graph, including opaque proofs, types and constructors.
run_cmd do
  checkRoot ``DkMath.Lib.NumberTheory.FiniteFieldFrobeniusImage.exists_bounded_power #[``FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow]
  checkRoot ``DkMath.Lib.NumberTheory.FiniteFieldFrobeniusImage.factor_image_bounded_power #[``DkMath.Lib.NumberTheory.FiniteFieldFrobeniusImage.exists_bounded_power]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.kernelDecompositionUnits #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.kernelDecompositionAction]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.kernelDecompositionUnits_ker #[]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.finiteDecompositionImage #[]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.finiteDecompositionProjection #[]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.finiteDecompositionEmbedding #[]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.finiteDecompositionEmbedding_injective #[``QuotientGroup.rangeKerLift_injective]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.finiteDecompositionImage_finite #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernel_finite, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.finiteDecompositionEmbedding_injective]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.kernelDecomposition_stabilizer_isOpen #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.kernel_fixed_iff_generator_evaluation, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.kernelDecomposition_orbit_evaluation_continuous]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.kernelDecompositionUnits_kernel_isOpen #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernel_finite, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.kernelDecomposition_stabilizer_isOpen]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.finiteDecompositionImage_discrete #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.kernelDecompositionUnits_kernel_isOpen]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.inertia_le_finiteDecompositionProjection_kernel #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.kernelDecompositionUnits_ker, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.inertia_le_kernelDecomposition_kernel]
  checkRoot ``DkMath.Lib.RepresentationTheory.DenseFiniteImageGeneration.mem_zpowers_of_dense #[``DkMath.Lib.RepresentationTheory.ClosedFixedSubgroup.eq_top_of_dense_join]
  checkRoot ``DkMath.Lib.RepresentationTheory.DenseFiniteImageGeneration.bounded_power_of_mem_zpowers #[]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.finiteDecomposition_generated_of_dense #[``DkMath.Lib.RepresentationTheory.DenseFiniteImageGeneration.mem_zpowers_of_dense, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.inertia_le_finiteDecompositionProjection_kernel, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.finiteDecompositionImage_discrete]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.finiteDecomposition_generated_of_field_factor #[``DkMath.Lib.NumberTheory.FiniteFieldFrobeniusImage.factor_image_bounded_power]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.finiteDecomposition_bounded_action_power #[``DkMath.Lib.RepresentationTheory.DenseFiniteImageGeneration.bounded_power_of_mem_zpowers, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.finiteDecompositionEmbedding, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.finiteDecompositionImage_finite]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.kernel_fixed_of_finite_image #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.finiteDecomposition_bounded_action_power]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.decomposition_fixed_iff_eigenvalue_of_finite_image #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.kernel_fixed_of_finite_image, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.kernelFrobenius_fixed_iff]
  checkRoot ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.decomposition_fixed_iff_resonant_sign_of_finite_image #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.decomposition_fixed_iff_eigenvalue_of_finite_image, ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.generatorValue_q_smul_plus, ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.generatorValue_q_smul_minus]
  checkRoot ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.decomposition_lift_of_finite_image_sign #[``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.decomposition_fixed_iff_resonant_sign_of_finite_image, ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.decomposition_lift_of_kernel_fixed]
  checkInputs ``DkMath.Lib.NumberTheory.FiniteFieldFrobeniusImage.exists_bounded_power #[`k, `E, `σ] #[`hD, `hz, `hclass, `hcofixed, `hglobal, `hselmer, `hherbrand, `hreflect]
  checkInputs ``DkMath.Lib.NumberTheory.FiniteFieldFrobeniusImage.factor_image_bounded_power #[`k, `E, `π, `a, `φ, `hφ, `g] #[`hD, `hz, `hclass, `hcofixed, `hglobal, `hselmer, `hherbrand, `hreflect]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.kernelDecompositionUnits #[`T, `A] #[`hD, `hz, `hclass, `hcofixed, `hglobal, `hselmer, `hherbrand, `hreflect]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.kernelDecompositionUnits_ker #[`T, `A] #[`hD, `hz, `hclass, `hcofixed, `hglobal, `hselmer, `hherbrand, `hreflect]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.finiteDecompositionImage #[`T, `A] #[`hD, `hz, `hclass, `hcofixed, `hglobal, `hselmer, `hherbrand, `hreflect]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.finiteDecompositionProjection #[`T, `A] #[`hD, `hz, `hclass, `hcofixed, `hglobal, `hselmer, `hherbrand, `hreflect]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.finiteDecompositionEmbedding #[`T, `A] #[`hD, `hz, `hclass, `hcofixed, `hglobal, `hselmer, `hherbrand, `hreflect]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.finiteDecompositionEmbedding_injective #[`T, `A] #[`hD, `hz, `hclass, `hcofixed, `hglobal, `hselmer, `hherbrand, `hreflect]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.finiteDecompositionImage_finite #[`T, `A] #[`hD, `hz, `hclass, `hcofixed, `hglobal, `hselmer, `hherbrand, `hreflect]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.kernelDecomposition_stabilizer_isOpen #[`T, `A] #[`hD, `hz, `hclass, `hcofixed, `hglobal, `hselmer, `hherbrand, `hreflect]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.kernelDecompositionUnits_kernel_isOpen #[`T, `A] #[`hD, `hz, `hclass, `hcofixed, `hglobal, `hselmer, `hherbrand, `hreflect]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.finiteDecompositionImage_discrete #[`T, `A] #[`hD, `hz, `hclass, `hcofixed, `hglobal, `hselmer, `hherbrand, `hreflect]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.inertia_le_finiteDecompositionProjection_kernel #[`T, `A] #[`hD, `hz, `hclass, `hcofixed, `hglobal, `hselmer, `hherbrand, `hreflect]
  checkInputs ``DkMath.Lib.RepresentationTheory.DenseFiniteImageGeneration.mem_zpowers_of_dense #[`ρ, `hρ, `N, `hN, `φ, `hdense, `g] #[`hD, `hz, `hclass, `hcofixed, `hglobal, `hselmer, `hherbrand, `hreflect]
  checkInputs ``DkMath.Lib.RepresentationTheory.DenseFiniteImageGeneration.bounded_power_of_mem_zpowers #[`a, `b, `hb] #[`hD, `hz, `hclass, `hcofixed, `hglobal, `hselmer, `hherbrand, `hreflect]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.finiteDecomposition_generated_of_dense #[`T, `A, `hdense] #[`hD, `hz, `hclass, `hcofixed, `hglobal, `hselmer, `hherbrand, `hreflect]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.finiteDecomposition_generated_of_field_factor #[`T, `A, `k, `E, `π, `a, `hfactor, `hφ] #[`hD, `hz, `hclass, `hcofixed, `hglobal, `hselmer, `hherbrand, `hreflect]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.finiteDecomposition_bounded_action_power #[`T, `A, `himage] #[`hD, `hz, `hclass, `hcofixed, `hglobal, `hselmer, `hherbrand, `hreflect]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.kernel_fixed_of_finite_image #[`T, `A, `himage] #[`hD, `hz, `hclass, `hcofixed, `hglobal, `hselmer, `hherbrand, `hreflect]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.decomposition_fixed_iff_eigenvalue_of_finite_image #[`T, `A, `himage] #[`hD, `hz, `hclass, `hcofixed, `hglobal, `hselmer, `hherbrand, `hreflect]
  checkInputs ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.decomposition_fixed_iff_resonant_sign_of_finite_image #[`h, `hp5, `φ, `hφ, `himage] #[`hD, `hz, `hclass, `hcofixed, `hglobal, `hselmer, `hherbrand, `hreflect]
  checkInputs ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.decomposition_lift_of_finite_image_sign #[`h, `hp5, `φ, `hφ, `himage, `hsign] #[`hD, `hz, `hclass, `hcofixed, `hglobal, `hselmer, `hherbrand, `hreflect, `hdense, `hfactor]

end Note032FiniteDecompositionImageAudit
