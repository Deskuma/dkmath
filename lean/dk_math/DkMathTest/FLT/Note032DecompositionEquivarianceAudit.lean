/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyDecompositionInvariantObstruction

#print "file: DkMathTest.FLT.Note032DecompositionEquivarianceAudit"

namespace Note032DecompositionEquivarianceAudit

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
-- Inspect all new checked actions, descent maps, proof values and constructors.
run_cmd do
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.quotientDecompositionAction #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.decomposition_preserves_fixed]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.quotientDecompositionAction_mk #[]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.quotientDecompositionAction_coset #[]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.kernelDecompositionAction #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.quotientConnectingKernelEquiv, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.quotientDecompositionAction]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.quotientKernelEquiv_decomposition #[]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.kernelDecompositionAction_coset #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.quotientKernelEquiv_coset, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.quotientKernelEquiv_decomposition]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.kernelDecompositionEvaluation #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.continuousCocycle_decomposition_conjugate, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.exists_torsion_fixedKernelElement, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.kernelDecompositionAction_coset]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.kernel_fixed_iff_generator_evaluation #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.generator_evaluation_injective]
  checkRoot ``DkMath.FLT.Frey.Source.inertiaNormalInDecomposition #[]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.inertia_le_fixedDecomposition_kernel #[]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.inertia_le_quotientDecomposition_kernel #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedQuotient_action_trivial]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.inertia_le_kernelDecomposition_kernel #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.inertia_le_quotientDecomposition_kernel]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedResidueAction #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.inertia_le_fixedDecomposition_kernel]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.quotientResidueAction #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.inertia_le_quotientDecomposition_kernel]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.kernelResidueAction #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.inertia_le_kernelDecomposition_kernel]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.quotientKernelEquiv_residue #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.quotientKernelEquiv_decomposition]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.kernelEvaluation_frobenius_conjugate #[``DkMath.FLT.Frey.Source.tameInertia_frobenius_power, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelTameCharacter]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.kernelFrobenius_evaluation_relation #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.kernelDecompositionEvaluation, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.kernelEvaluation_frobenius_conjugate]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixed_q_nsmul_injective #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernel_card_mul_fixed, ``powCoprime]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.kernelFrobenius_fixed_iff #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.kernelFrobenius_evaluation_relation, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixed_q_nsmul_injective, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.generator_evaluation_injective]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.kernel_fixed_iff_quotient_fixed #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.quotientKernelEquiv_decomposition]
  checkRoot ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.frobenius_fixed_criterion #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.kernelFrobenius_fixed_iff]
  checkRoot ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.exists_frobenius_fixed_criterion #[``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.frobenius_fixed_criterion, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.generator_evaluation_injective, ``DkMath.Lib.NumberTheory.ValuationFrobenius.exists_isFrobeniusAt_of_liesOverPrime, ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixed_H1_nonzero]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.quotientDecompositionAction #[`T, `A] #[`hclass, `hcofixed, `hcompare, `hcyclic, `hgen, `hfinite, `hcontinuous, `hglobal, `hselmer, `hFstable, `horigin, `hvanish, `hreflect, `hherbrand, `heigen, `hfixed]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.quotientDecompositionAction_mk #[`T, `A] #[`hclass, `hcofixed, `hcompare, `hcyclic, `hgen, `hfinite, `hcontinuous, `hglobal, `hselmer, `hFstable, `horigin, `hvanish, `hreflect, `hherbrand, `heigen, `hfixed]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.quotientDecompositionAction_coset #[`T, `A] #[`hclass, `hcofixed, `hcompare, `hcyclic, `hgen, `hfinite, `hcontinuous, `hglobal, `hselmer, `hFstable, `horigin, `hvanish, `hreflect, `hherbrand, `heigen, `hfixed]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.kernelDecompositionAction #[`T, `A] #[`hclass, `hcofixed, `hcompare, `hcyclic, `hgen, `hfinite, `hcontinuous, `hglobal, `hselmer, `hFstable, `horigin, `hvanish, `hreflect, `hherbrand, `heigen, `hfixed]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.quotientKernelEquiv_decomposition #[`T, `A] #[`hclass, `hcofixed, `hcompare, `hcyclic, `hgen, `hfinite, `hcontinuous, `hglobal, `hselmer, `hFstable, `horigin, `hvanish, `hreflect, `hherbrand, `heigen, `hfixed]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.kernelDecompositionAction_coset #[`T, `A] #[`hclass, `hcofixed, `hcompare, `hcyclic, `hgen, `hfinite, `hcontinuous, `hglobal, `hselmer, `hFstable, `horigin, `hvanish, `hreflect, `hherbrand, `heigen, `hfixed]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.kernelDecompositionEvaluation #[`T, `A] #[`hclass, `hcofixed, `hcompare, `hcyclic, `hgen, `hfinite, `hcontinuous, `hglobal, `hselmer, `hFstable, `horigin, `hvanish, `hreflect, `hherbrand, `heigen, `hfixed]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.kernel_fixed_iff_generator_evaluation #[`T, `A] #[`hclass, `hcofixed, `hcompare, `hcyclic, `hgen, `hfinite, `hcontinuous, `hglobal, `hselmer, `hFstable, `horigin, `hvanish, `hreflect, `hherbrand, `heigen, `hfixed]
  checkInputs ``DkMath.FLT.Frey.Source.inertiaNormalInDecomposition #[`A] #[`hclass, `hcofixed, `hcompare, `hcyclic, `hgen, `hfinite, `hcontinuous, `hglobal, `hselmer, `hFstable, `horigin, `hvanish, `hreflect, `hherbrand, `heigen, `hfixed]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.inertia_le_fixedDecomposition_kernel #[`T, `A] #[`hclass, `hcofixed, `hcompare, `hcyclic, `hgen, `hfinite, `hcontinuous, `hglobal, `hselmer, `hFstable, `horigin, `hvanish, `hreflect, `hherbrand, `heigen, `hfixed]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.inertia_le_quotientDecomposition_kernel #[`T, `A] #[`hclass, `hcofixed, `hcompare, `hcyclic, `hgen, `hfinite, `hcontinuous, `hglobal, `hselmer, `hFstable, `horigin, `hvanish, `hreflect, `hherbrand, `heigen, `hfixed]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.inertia_le_kernelDecomposition_kernel #[`T, `A] #[`hclass, `hcofixed, `hcompare, `hcyclic, `hgen, `hfinite, `hcontinuous, `hglobal, `hselmer, `hFstable, `horigin, `hvanish, `hreflect, `hherbrand, `heigen, `hfixed]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedResidueAction #[`T, `A] #[`hclass, `hcofixed, `hcompare, `hcyclic, `hgen, `hfinite, `hcontinuous, `hglobal, `hselmer, `hFstable, `horigin, `hvanish, `hreflect, `hherbrand, `heigen, `hfixed]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.quotientResidueAction #[`T, `A] #[`hclass, `hcofixed, `hcompare, `hcyclic, `hgen, `hfinite, `hcontinuous, `hglobal, `hselmer, `hFstable, `horigin, `hvanish, `hreflect, `hherbrand, `heigen, `hfixed]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.kernelResidueAction #[`T, `A] #[`hclass, `hcofixed, `hcompare, `hcyclic, `hgen, `hfinite, `hcontinuous, `hglobal, `hselmer, `hFstable, `horigin, `hvanish, `hreflect, `hherbrand, `heigen, `hfixed]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.quotientKernelEquiv_residue #[`T, `A] #[`hclass, `hcofixed, `hcompare, `hcyclic, `hgen, `hfinite, `hcontinuous, `hglobal, `hselmer, `hFstable, `horigin, `hvanish, `hreflect, `hherbrand, `heigen, `hfixed]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.kernelEvaluation_frobenius_conjugate #[`T, `A] #[`hclass, `hcofixed, `hcompare, `hcyclic, `hgen, `hfinite, `hcontinuous, `hglobal, `hselmer, `hFstable, `horigin, `hvanish, `hreflect, `hherbrand, `heigen, `hfixed]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.kernelFrobenius_evaluation_relation #[`T, `A] #[`hclass, `hcofixed, `hcompare, `hcyclic, `hgen, `hfinite, `hcontinuous, `hglobal, `hselmer, `hFstable, `horigin, `hvanish, `hreflect, `hherbrand, `heigen, `hfixed]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixed_q_nsmul_injective #[`T, `A] #[`hclass, `hcofixed, `hcompare, `hcyclic, `hgen, `hfinite, `hcontinuous, `hglobal, `hselmer, `hFstable, `horigin, `hvanish, `hreflect, `hherbrand, `heigen, `hfixed]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.kernelFrobenius_fixed_iff #[`T, `A] #[`hclass, `hcofixed, `hcompare, `hcyclic, `hgen, `hfinite, `hcontinuous, `hglobal, `hselmer, `hFstable, `horigin, `hvanish, `hreflect, `hherbrand, `heigen, `hfixed]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.kernel_fixed_iff_quotient_fixed #[`T, `A] #[`hclass, `hcofixed, `hcompare, `hcyclic, `hgen, `hfinite, `hcontinuous, `hglobal, `hselmer, `hFstable, `horigin, `hvanish, `hreflect, `hherbrand, `heigen, `hfixed]
  checkInputs ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.frobenius_fixed_criterion #[`h, `hp5] #[`hclass, `hcofixed, `hcompare, `hcyclic, `hgen, `hfinite, `hcontinuous, `hglobal, `hselmer, `hFstable, `horigin, `hvanish, `hreflect, `hherbrand, `heigen, `hfixed]
  checkInputs ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.exists_frobenius_fixed_criterion #[`h, `hp5] #[`hclass, `hcofixed, `hcompare, `hcyclic, `hgen, `hfinite, `hcontinuous, `hglobal, `hselmer, `hFstable, `horigin, `hvanish, `hreflect, `hherbrand, `heigen, `hfixed]

end Note032DecompositionEquivarianceAudit
