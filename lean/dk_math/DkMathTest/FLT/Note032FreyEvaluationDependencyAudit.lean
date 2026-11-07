/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyKernelEvaluationCertificate

#print "file: DkMathTest.FLT.Note032FreyEvaluationDependencyAudit"

namespace Note032FreyEvaluationDependencyAudit

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
-- Traverse checked types, constructors and opaque values for all eighteen roots.
run_cmd do
  checkRoot ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixedDifference #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.inertiaFixedDifferenceCharacter]
  checkRoot ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixedDifference_order_eq_prime #[``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixed_character_values_killed, ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.inertia_character_nontrivial]
  checkRoot ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixedDifference_cyclic_card #[``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixedDifference_order_eq_prime]
  checkRoot ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.prime_dvd_fixed_card #[``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixedDifference_cyclic_card]
  checkRoot ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixed_positive_profile #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernel_card_mul_fixed, ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.prime_dvd_fixed_card]
  checkRoot ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixed_kernel_balanced_profile #[``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixed_positive_profile, ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixedKernel_positive_profile]
  checkRoot ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixed_kernel_sharp_profile #[``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixed_kernel_balanced_profile]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelEvaluation #[``groupCohomology.H1IsoOfIsTrivial]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelEvaluation_separates #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelEvaluation, ``groupCohomology.H1IsoOfIsTrivial]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelEvaluation_coset #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedCosetKernelElement_val, ``DkMath.Lib.RepresentationTheory.TrivialCharacterH1.class_evaluate]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelEvaluation_card #[``LinearMap.quotKerEquivRange, ``Submodule.card_eq_card_quotient_mul_card]
  checkRoot ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixedKernelEvaluation_obstruction #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelEvaluation_coset]
  checkRoot ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixedEvaluationImageElement #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedCosetKernelElement, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelEvaluation]
  checkRoot ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixedEvaluationImageElement_val #[``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixedKernelEvaluation_obstruction]
  checkRoot ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixedEvaluationImage_order_eq_prime #[``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixedEvaluationImageElement_val, ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixedDifference_order_eq_prime]
  checkRoot ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.prime_dvd_evaluation_image_card #[``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixedEvaluationImage_order_eq_prime]
  checkRoot ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixed_evaluation_balanced_profile #[``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixed_kernel_sharp_profile, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelEvaluation_card, ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.prime_dvd_evaluation_image_card]
  checkRoot ``DkMath.FLT.Frey.Source.residual_exists_evaluated_coefficient_kernel #[``DkMath.FLT.Frey.Source.residual_exists_narrow_geometric_obstruction, ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixed_evaluation_balanced_profile, ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixedKernel_order_eq_prime, ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixedKernelEvaluation_obstruction, ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixedEvaluationImage_order_eq_prime]
  checkInputs ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixedDifference #[`h, `hp5] #[`hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hclass, `hcofixed]
  checkInputs ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixedDifference_order_eq_prime #[`h, `hp5] #[`hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hclass, `hcofixed]
  checkInputs ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixedDifference_cyclic_card #[`h, `hp5] #[`hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hclass, `hcofixed]
  checkInputs ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.prime_dvd_fixed_card #[`h, `hp5] #[`hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hclass, `hcofixed]
  checkInputs ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixed_positive_profile #[`h, `hp5] #[`hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hclass, `hcofixed]
  checkInputs ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixed_kernel_balanced_profile #[`h, `hp5] #[`hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hclass, `hcofixed]
  checkInputs ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixed_kernel_sharp_profile #[`h, `hp5] #[`hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hclass, `hcofixed]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelEvaluation #[`T, `A] #[`hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hclass, `hcofixed, `hp5, `hq, `hqp, `haddr, `hA]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelEvaluation_separates #[`T, `A] #[`hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hclass, `hcofixed, `hp5, `hq, `hqp, `haddr, `hA]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelEvaluation_coset #[`T, `A, `hp5, `hq, `hqp, `haddr, `hA, `x, `σ] #[`hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hclass, `hcofixed]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelEvaluation_card #[`T, `A] #[`hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hclass, `hcofixed, `hp5, `hq, `hqp, `haddr, `hA]
  checkInputs ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixedKernelEvaluation_obstruction #[`h, `hp5] #[`hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hclass, `hcofixed]
  checkInputs ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixedEvaluationImageElement #[`h, `hp5] #[`hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hclass, `hcofixed]
  checkInputs ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixedEvaluationImageElement_val #[`h, `hp5] #[`hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hclass, `hcofixed]
  checkInputs ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixedEvaluationImage_order_eq_prime #[`h, `hp5] #[`hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hclass, `hcofixed]
  checkInputs ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.prime_dvd_evaluation_image_card #[`h, `hp5] #[`hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hclass, `hcofixed]
  checkInputs ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixed_evaluation_balanced_profile #[`h, `hp5] #[`hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hclass, `hcofixed]
  checkInputs ``DkMath.FLT.Frey.Source.residual_exists_evaluated_coefficient_kernel #[`S, `L, `hline, `hζ, `hp5, `hclass, `hcofixed] #[`hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile]

end Note032FreyEvaluationDependencyAudit
