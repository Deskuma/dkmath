/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyKernelFiniteDetector

#print "file: DkMathTest.FLT.Note032FreyDetectorDependencyAudit"

namespace Note032FreyDetectorDependencyAudit

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
-- Traverse checked types, constructors and opaque values for all twenty-eight roots.
run_cmd do
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedEvaluation_image_card_dvd #[``AddSubgroup.card_addSubgroup_dvd_card]
  checkRoot ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixed_evaluation_constrained_profile #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedEvaluation_image_card_dvd, ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixed_evaluation_balanced_profile]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCharacter #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelEvaluation, ``groupCohomology.H1IsoOfIsTrivial]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCharacter_apply #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCharacter]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.exists_torsion_fixedKernelElement #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.quotientConnectingKernelEquiv, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.quotientKernelEquiv_coset]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCharacter_coset #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelEvaluation_coset]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCharacter_continuous #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.exists_torsion_fixedKernelElement, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.inertiaFixedDifferenceCharacter_continuous]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.wild_le_fixedKernelCharacter_kernel #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.exists_torsion_fixedKernelElement, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.wildInertia_le_fixed_character_kernel]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelTameCharacter #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.wild_le_fixedKernelCharacter_kernel]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelTameCharacter_mk #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelTameCharacter]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelTameCharacter_continuous #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCharacter_continuous]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelTameCharacter_coset #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCharacter_coset]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelTameClass #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelTameCharacter]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelTameClass_inflation #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedTameClass_inflation, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedCosetKernelElement_val, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.exists_torsion_fixedKernelElement]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernel_finite #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernel_prime_power_profile]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelTameFamily #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelTameCharacter]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.mem_fixedKernelTameFamily_kernel #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelTameFamily]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelTameFamily_continuous #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelTameCharacter_continuous]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelTameFamily_kernel_isOpen #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernel_finite, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelTameFamily_continuous]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonTameQuotient #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelTameFamily]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonTameQuotient_finite #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernel_finite, ``QuotientGroup.quotientKerEquivRange]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonTameValues #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelTameFamily]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonTameValues_mk #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonTameValues]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonTameValues_separates #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelEvaluation_separates, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonTameValues]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedFiniteEvaluation #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelEvaluation]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedFiniteEvaluation_card_dvd #[``AddSubgroup.card_dvd_of_injective, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedFiniteEvaluation]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.exists_finite_inertia_detector #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernel_finite, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelEvaluation_separates]
  checkRoot ``DkMath.FLT.Frey.Source.residual_exists_finitely_detected_coefficient_kernel #[``DkMath.FLT.Frey.Source.residual_exists_narrow_geometric_obstruction, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.exists_finite_inertia_detector, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonTameQuotient_finite, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCharacter_continuous, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelTameClass_inflation, ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixed_evaluation_constrained_profile, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedFiniteEvaluation_card_dvd]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedEvaluation_image_card_dvd #[`T, `A] #[`hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hgen, `hcyclic, `hcontinuous, `hwild, `hclass, `hcofixed, `hp5, `hq, `hqp, `haddr, `hA, `hinj]
  checkInputs ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixed_evaluation_constrained_profile #[`h, `hp5] #[`hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hgen, `hcyclic, `hcontinuous, `hwild, `hclass, `hcofixed, `hinj]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCharacter #[`T, `A] #[`hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hgen, `hcyclic, `hcontinuous, `hwild, `hclass, `hcofixed, `hp5, `hq, `hqp, `haddr, `hA, `hinj]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCharacter_apply #[`T, `A] #[`hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hgen, `hcyclic, `hcontinuous, `hwild, `hclass, `hcofixed, `hp5, `hq, `hqp, `haddr, `hA, `hinj]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.exists_torsion_fixedKernelElement #[`T, `A, `hp5, `hq, `hqp, `haddr, `hA] #[`hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hgen, `hcyclic, `hcontinuous, `hwild, `hclass, `hcofixed, `hinj]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCharacter_coset #[`T, `A, `hp5, `hq, `hqp, `haddr, `hA] #[`hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hgen, `hcyclic, `hcontinuous, `hwild, `hclass, `hcofixed, `hinj]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCharacter_continuous #[`T, `A, `hp5, `hq, `hqp, `haddr, `hA] #[`hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hgen, `hcyclic, `hcontinuous, `hwild, `hclass, `hcofixed, `hinj]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.wild_le_fixedKernelCharacter_kernel #[`T, `A, `hp5, `hq, `hqp, `haddr, `hA] #[`hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hgen, `hcyclic, `hcontinuous, `hwild, `hclass, `hcofixed, `hinj]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelTameCharacter #[`T, `A, `hp5, `hq, `hqp, `haddr, `hA] #[`hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hgen, `hcyclic, `hcontinuous, `hwild, `hclass, `hcofixed, `hinj]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelTameCharacter_mk #[`T, `A, `hp5, `hq, `hqp, `haddr, `hA] #[`hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hgen, `hcyclic, `hcontinuous, `hwild, `hclass, `hcofixed, `hinj]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelTameCharacter_continuous #[`T, `A, `hp5, `hq, `hqp, `haddr, `hA] #[`hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hgen, `hcyclic, `hcontinuous, `hwild, `hclass, `hcofixed, `hinj]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelTameCharacter_coset #[`T, `A, `hp5, `hq, `hqp, `haddr, `hA] #[`hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hgen, `hcyclic, `hcontinuous, `hwild, `hclass, `hcofixed, `hinj]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelTameClass #[`T, `A, `hp5, `hq, `hqp, `haddr, `hA] #[`hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hgen, `hcyclic, `hcontinuous, `hwild, `hclass, `hcofixed, `hinj]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelTameClass_inflation #[`T, `A, `hp5, `hq, `hqp, `haddr, `hA] #[`hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hgen, `hcyclic, `hcontinuous, `hwild, `hclass, `hcofixed, `hinj]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernel_finite #[`T, `A, `hp5, `hq, `hqp, `haddr, `hA] #[`hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hgen, `hcyclic, `hcontinuous, `hwild, `hclass, `hcofixed, `hinj]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelTameFamily #[`T, `A, `hp5, `hq, `hqp, `haddr, `hA] #[`hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hgen, `hcyclic, `hcontinuous, `hwild, `hclass, `hcofixed, `hinj]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.mem_fixedKernelTameFamily_kernel #[`T, `A, `hp5, `hq, `hqp, `haddr, `hA] #[`hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hgen, `hcyclic, `hcontinuous, `hwild, `hclass, `hcofixed, `hinj]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelTameFamily_continuous #[`T, `A, `hp5, `hq, `hqp, `haddr, `hA] #[`hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hgen, `hcyclic, `hcontinuous, `hwild, `hclass, `hcofixed, `hinj]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelTameFamily_kernel_isOpen #[`T, `A, `hp5, `hq, `hqp, `haddr, `hA] #[`hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hgen, `hcyclic, `hcontinuous, `hwild, `hclass, `hcofixed, `hinj]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonTameQuotient #[`T, `A, `hp5, `hq, `hqp, `haddr, `hA] #[`hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hgen, `hcyclic, `hcontinuous, `hwild, `hclass, `hcofixed, `hinj]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonTameQuotient_finite #[`T, `A, `hp5, `hq, `hqp, `haddr, `hA] #[`hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hgen, `hcyclic, `hcontinuous, `hwild, `hclass, `hcofixed, `hinj]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonTameValues #[`T, `A, `hp5, `hq, `hqp, `haddr, `hA] #[`hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hgen, `hcyclic, `hcontinuous, `hwild, `hclass, `hcofixed, `hinj]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonTameValues_mk #[`T, `A, `hp5, `hq, `hqp, `haddr, `hA] #[`hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hgen, `hcyclic, `hcontinuous, `hwild, `hclass, `hcofixed, `hinj]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonTameValues_separates #[`T, `A, `hp5, `hq, `hqp, `haddr, `hA] #[`hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hgen, `hcyclic, `hcontinuous, `hwild, `hclass, `hcofixed, `hinj]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedFiniteEvaluation #[`T, `A] #[`hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hgen, `hcyclic, `hcontinuous, `hwild, `hclass, `hcofixed, `hp5, `hq, `hqp, `haddr, `hA, `hinj]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedFiniteEvaluation_card_dvd #[`T, `A, `Ω, `hinj] #[`hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hgen, `hcyclic, `hcontinuous, `hwild, `hclass, `hcofixed, `hp5, `hq, `hqp, `haddr, `hA]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.exists_finite_inertia_detector #[`T, `A, `hp5, `hq, `hqp, `haddr, `hA] #[`hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hgen, `hcyclic, `hcontinuous, `hwild, `hclass, `hcofixed, `hinj]
  checkInputs ``DkMath.FLT.Frey.Source.residual_exists_finitely_detected_coefficient_kernel #[`S, `L, `hline, `hζ, `hp5, `hclass, `hcofixed] #[`hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hgen, `hcyclic, `hcontinuous, `hwild, `hinj]

end Note032FreyDetectorDependencyAudit
