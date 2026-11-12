/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCommonTameStructureCertificate

#print "file: DkMathTest.FLT.Note032FreyCommonStructureDependencyAudit"

namespace Note032FreyCommonStructureDependencyAudit

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
-- Traverse checked types, constructors and opaque values for all thirty roots.
run_cmd do
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonTameValues_injective #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonTameValues]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonTame_mul_comm #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonTameValues_injective]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonTameCommGroup #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonTame_mul_comm]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonProjection #[``QuotientGroup.mk']
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonProjection_surjective #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonProjection]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonProjection_value #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonProjection, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonTameValues]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonTame_card_dvd #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonTameValues_injective, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernel_finite]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonTame_pow_card_fixed #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonTameValues_injective, ``pow_card_eq_one']
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonTame_prime_power_profile #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonTame_card_dvd, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernel_card_mul_fixed]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonTame_isPGroup #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonTame_prime_power_profile, ``IsPGroup.of_card]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonTame_exponent_profile #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonTame_prime_power_profile, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonTame_pow_card_fixed]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonTame_pow_stage #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonTame_exponent_profile]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonEvaluation #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonProjection_surjective, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelEvaluation]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonEvaluation_projection #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonEvaluation]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonEvaluation_one #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonEvaluation]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonCharacter #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonTameValues]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonCharacter_apply #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonCharacter, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonEvaluation]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonEvaluation_separates_kernel #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonTameValues_separates]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonEvaluation_separates_quotient #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonTameValues_injective]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommon_generator_evaluation_injective #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonTameValues_separates, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonCharacter]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.exists_single_evaluation_of_common_isCyclic #[``IsCyclic.exists_generator, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonProjection_surjective, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommon_generator_evaluation_injective]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.commonProjection_generates_of_power_decomposition #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonTame_pow_stage, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonProjection_surjective]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.common_isCyclic_of_power_decomposition #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.commonProjection_generates_of_power_decomposition]
  checkRoot ``DkMath.FLT.Frey.Source.ResidualCyclicStage.single_evaluation_of_power_decomposition #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.commonProjection_generates_of_power_decomposition, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommon_generator_evaluation_injective]
  checkRoot ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.commonInertiaElement #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonProjection]
  checkRoot ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.commonInertiaElement_evaluation #[``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixedKernelEvaluation_obstruction]
  checkRoot ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.commonInertiaElement_ne_one #[``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.commonInertiaElement_evaluation, ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixedDifference_order_eq_prime, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonEvaluation_one]
  checkRoot ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.commonTame_positive_profile #[``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.commonInertiaElement_ne_one, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonTame_card_dvd, ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixed_kernel_sharp_profile]
  checkRoot ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.single_evaluation_profile_of_common_isCyclic #[``DkMath.FLT.Frey.Source.ResidualCyclicStage.exists_single_evaluation_of_common_isCyclic, ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.fixed_kernel_balanced_profile]
  checkRoot ``DkMath.FLT.Frey.Source.residual_exists_nontrivial_common_tame_pGroup #[``DkMath.FLT.Frey.Source.residual_exists_narrow_geometric_obstruction, ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.commonTame_positive_profile, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonTame_mul_comm, ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonTame_isPGroup, ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.single_evaluation_profile_of_common_isCyclic]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonTameValues_injective #[`T, `A, `hp5, `hq, `hqp, `haddr, `hA] #[`hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hcomm, `hpgroup, `hexponent, `hinj, `hclass, `hcofixed, `hg, `hgen, `hcyclic]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonTame_mul_comm #[`T, `A, `hp5, `hq, `hqp, `haddr, `hA] #[`hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hcomm, `hpgroup, `hexponent, `hinj, `hclass, `hcofixed, `hg, `hgen, `hcyclic]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonTameCommGroup #[`T, `A, `hp5, `hq, `hqp, `haddr, `hA] #[`hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hcomm, `hpgroup, `hexponent, `hinj, `hclass, `hcofixed, `hg, `hgen, `hcyclic]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonProjection #[`T, `A, `hp5, `hq, `hqp, `haddr, `hA] #[`hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hcomm, `hpgroup, `hexponent, `hinj, `hclass, `hcofixed, `hg, `hgen, `hcyclic]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonProjection_surjective #[`T, `A, `hp5, `hq, `hqp, `haddr, `hA] #[`hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hcomm, `hpgroup, `hexponent, `hinj, `hclass, `hcofixed, `hg, `hgen, `hcyclic]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonProjection_value #[`T, `A, `hp5, `hq, `hqp, `haddr, `hA] #[`hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hcomm, `hpgroup, `hexponent, `hinj, `hclass, `hcofixed, `hg, `hgen, `hcyclic]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonTame_card_dvd #[`T, `A, `hp5, `hq, `hqp, `haddr, `hA] #[`hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hcomm, `hpgroup, `hexponent, `hinj, `hclass, `hcofixed, `hg, `hgen, `hcyclic]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonTame_pow_card_fixed #[`T, `A, `hp5, `hq, `hqp, `haddr, `hA] #[`hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hcomm, `hpgroup, `hexponent, `hinj, `hclass, `hcofixed, `hg, `hgen, `hcyclic]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonTame_prime_power_profile #[`T, `A, `hp5, `hq, `hqp, `haddr, `hA] #[`hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hcomm, `hpgroup, `hexponent, `hinj, `hclass, `hcofixed, `hg, `hgen, `hcyclic]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonTame_isPGroup #[`T, `A, `hp5, `hq, `hqp, `haddr, `hA] #[`hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hcomm, `hpgroup, `hexponent, `hinj, `hclass, `hcofixed, `hg, `hgen, `hcyclic]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonTame_exponent_profile #[`T, `A, `hp5, `hq, `hqp, `haddr, `hA] #[`hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hcomm, `hpgroup, `hexponent, `hinj, `hclass, `hcofixed, `hg, `hgen, `hcyclic]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonTame_pow_stage #[`T, `A, `hp5, `hq, `hqp, `haddr, `hA] #[`hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hcomm, `hpgroup, `hexponent, `hinj, `hclass, `hcofixed, `hg, `hgen, `hcyclic]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonEvaluation #[`T, `A, `hp5, `hq, `hqp, `haddr, `hA] #[`hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hcomm, `hpgroup, `hexponent, `hinj, `hclass, `hcofixed, `hg, `hgen, `hcyclic]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonEvaluation_projection #[`T, `A, `hp5, `hq, `hqp, `haddr, `hA] #[`hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hcomm, `hpgroup, `hexponent, `hinj, `hclass, `hcofixed, `hg, `hgen, `hcyclic]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonEvaluation_one #[`T, `A, `hp5, `hq, `hqp, `haddr, `hA] #[`hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hcomm, `hpgroup, `hexponent, `hinj, `hclass, `hcofixed, `hg, `hgen, `hcyclic]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonCharacter #[`T, `A, `hp5, `hq, `hqp, `haddr, `hA] #[`hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hcomm, `hpgroup, `hexponent, `hinj, `hclass, `hcofixed, `hg, `hgen, `hcyclic]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonCharacter_apply #[`T, `A, `hp5, `hq, `hqp, `haddr, `hA] #[`hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hcomm, `hpgroup, `hexponent, `hinj, `hclass, `hcofixed, `hg, `hgen, `hcyclic]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonEvaluation_separates_kernel #[`T, `A, `hp5, `hq, `hqp, `haddr, `hA] #[`hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hcomm, `hpgroup, `hexponent, `hinj, `hclass, `hcofixed, `hg, `hgen, `hcyclic]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommonEvaluation_separates_quotient #[`T, `A, `hp5, `hq, `hqp, `haddr, `hA] #[`hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hcomm, `hpgroup, `hexponent, `hinj, `hclass, `hcofixed, `hg, `hgen, `hcyclic]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.fixedKernelCommon_generator_evaluation_injective #[`T, `A, `hp5, `hq, `hqp, `haddr, `hA, `hg] #[`hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hcomm, `hpgroup, `hexponent, `hinj, `hclass, `hcofixed, `hgen, `hcyclic]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.exists_single_evaluation_of_common_isCyclic #[`T, `A, `hp5, `hq, `hqp, `haddr, `hA, `hcyclic] #[`hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hcomm, `hpgroup, `hexponent, `hinj, `hclass, `hcofixed, `hg, `hgen]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.commonProjection_generates_of_power_decomposition #[`T, `A, `hp5, `hq, `hqp, `haddr, `hA, `hgen] #[`hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hcomm, `hpgroup, `hexponent, `hinj, `hclass, `hcofixed, `hg, `hcyclic]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.common_isCyclic_of_power_decomposition #[`T, `A, `hp5, `hq, `hqp, `haddr, `hA, `hgen] #[`hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hcomm, `hpgroup, `hexponent, `hinj, `hclass, `hcofixed, `hg, `hcyclic]
  checkInputs ``DkMath.FLT.Frey.Source.ResidualCyclicStage.single_evaluation_of_power_decomposition #[`T, `A, `hp5, `hq, `hqp, `haddr, `hA, `hgen] #[`hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hcomm, `hpgroup, `hexponent, `hinj, `hclass, `hcofixed, `hg, `hcyclic]
  checkInputs ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.commonInertiaElement #[`h, `hp5] #[`hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hcomm, `hpgroup, `hexponent, `hinj, `hclass, `hcofixed, `hg, `hgen, `hcyclic]
  checkInputs ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.commonInertiaElement_evaluation #[`h, `hp5] #[`hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hcomm, `hpgroup, `hexponent, `hinj, `hclass, `hcofixed, `hg, `hgen, `hcyclic]
  checkInputs ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.commonInertiaElement_ne_one #[`h, `hp5] #[`hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hcomm, `hpgroup, `hexponent, `hinj, `hclass, `hcofixed, `hg, `hgen, `hcyclic]
  checkInputs ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.commonTame_positive_profile #[`h, `hp5] #[`hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hcomm, `hpgroup, `hexponent, `hinj, `hclass, `hcofixed, `hg, `hgen, `hcyclic]
  checkInputs ``DkMath.FLT.Frey.Source.NarrowAbsorptionObstruction.single_evaluation_profile_of_common_isCyclic #[`h, `hp5, `hcyclic] #[`hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hcomm, `hpgroup, `hexponent, `hinj, `hclass, `hcofixed, `hg, `hgen]
  checkInputs ``DkMath.FLT.Frey.Source.residual_exists_nontrivial_common_tame_pGroup #[`S, `L, `hline, `hζ, `hp5, `hclass, `hcofixed] #[`hbad, `hinjective, `hequiv, `hrange, `horder, `hcard, `hfinite, `hfixed, `htrivial, `hplacement, `heval, `hprofile, `hcontinuous, `hwild, `hcomm, `hpgroup, `hexponent, `hinj, `hg, `hgen, `hcyclic]

end Note032FreyCommonStructureDependencyAudit
