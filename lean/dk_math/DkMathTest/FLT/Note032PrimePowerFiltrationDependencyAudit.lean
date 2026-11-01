/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyPrimePowerFiltration

/-!
# `p` 上の局所群と補直線の存在を、実際の算術への依存で監査する

有限円分体の完全分岐、実際の慣性持ち上げ、整な捩れ点、倍写像、還元を要求する。
局所フィルトレーションの位数や局所分裂を仮定へ移した証明を成功として扱わない。
-/

namespace Note032PrimePowerFiltrationDependencyAudit

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
-- Finite traversal includes imported types, constructors and opaque proof bodies.
run_cmd do
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicInertia.exists_inertia_cyclotomic_eq
    #[``IsCyclotomicExtension.Rat.ramificationIdx_eq_of_prime,
      ``DkMath.Lib.NumberTheory.IntegralClosureInertiaLift.exists_lift_mem_inertia_integralClosure,
      ``DkMath.Lib.NumberTheory.ValuationInertiaLift.exists_valuation_inertia_of_integral_congruence,
      ``DkMath.Lib.NumberTheory.ValuationPlaceConjugacy.exists_smul_eq]
  checkRoot ``DkMath.FLT.Frey.Source.primePowerReductionFiltration_cyclic_and_card
    #[``DkMath.Lib.Algebra.AbsorbingTorsionFiltration.cyclic_and_card,
      ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.multiplication_surjective,
      ``DkMath.Lib.NumberTheory.CyclotomicInertia.exists_inertia_cyclotomic_eq,
      ``DkMath.FLT.Frey.Source.exists_integral_torsion_of_stable_line,
      ``DkMath.Lib.NumberTheory.EllipticNodalReductionKernel.pole_of_smooth_prime_power_torsion_of_model]
  checkRoot ``DkMath.FLT.Frey.Source.cyclic_tower_eq_primePowerReductionFiltration
    #[``DkMath.Lib.Algebra.AbsorbingTorsionFiltration.le_of_nontrivial_socle,
      ``DkMath.FLT.Frey.Source.residual_cofixed_inertia_moves_base_at_p,
      ``DkMath.FLT.Frey.Source.primePowerReductionFiltration_cyclic_and_card]
  checkRoot ``DkMath.FLT.Frey.Source.residual_cofixed_cyclic_extension_locally_split_at_p
    #[``DkMath.FLT.Frey.Source.cyclic_tower_eq_primePowerReductionFiltration,
      ``DkMath.Lib.Algebra.TorsionPreimageQuotient.isCompl_imageSubmodule,
      ``DkMath.Lib.Algebra.TorsionPreimageQuotient.lift_imageSubmodule,
      ``DkMath.Lib.NumberTheory.EllipticNodalReductionKernel.pole_of_smooth_prime_power_torsion_of_model,
      ``DkMath.Lib.NumberTheory.EllipticGoodReductionKernel.inertia_difference_mem]
  checkRoot ``DkMath.FLT.Frey.Source.residual_cofixed_cyclic_tower_inertia_frobenius_impossible
    #[``DkMath.FLT.Frey.Source.prime_power_pointAction_sub_mem_cyclic_tower_at_p,
      ``DkMath.FLT.Frey.Source.cyclic_tower_eq_primePowerReductionFiltration,
      ``DkMath.Lib.NumberTheory.AbsoluteInertiaGeneration.subgroup_eq_top_of_inertia_le,
      ``DkMath.Lib.Algebra.TorsionTowerFrobenius.nsmul_mem_of_frobenius_relation]
  checkInputs ``DkMath.Lib.NumberTheory.CyclotomicInertia.exists_inertia_cyclotomic_eq
    #[`A, `hA, `a] #[`hsurj, `hlift, `hconj, `hno]
  checkInputs ``DkMath.FLT.Frey.Source.prime_power_reductionKernel_absorbs_at_p
    #[`hp2, `A, `hA, `m, `hτ, `hy] #[`hbad, `hgood, `hkernel, `hno]
  checkInputs ``DkMath.FLT.Frey.Source.primePowerReductionFiltration_cyclic_and_card
    #[`hp5, `L, `hline, `hcofixed, `A, `hA, `hm]
    #[`hcard, `hsocle, `habs, `hnontriv, `hFcard, `hno]
  checkInputs ``DkMath.FLT.Frey.Source.cyclic_tower_eq_primePowerReductionFiltration
    #[`hp5, `hline, `hcofixed, `K, `hstable, `hm, `hcard, `hbase, `hA]
    #[`hNontriv, `hFabs, `hFcard, `hno]
  checkInputs ``DkMath.FLT.Frey.Source.residual_cofixed_cyclic_extension_locally_split_at_p
    #[`hp5, `hline, `hcofixed, `K, `hstable, `hm, `hcard, `hbase, `A, `hA]
    #[`F, `hFcard, `hFP, `hFdown, `hFstable, `hcompl, `hEXT, `hno]
  checkInputs ``DkMath.FLT.Frey.Source.residual_cofixed_cyclic_tower_inertia_frobenius_impossible
    #[`hp5, `hline, `hcofixed, `hstable, `hN, `hcard, `hbase, `hbad, `hCH]
    #[`hdown, `hfixed, `hpabs, `hSp, `hcompl, `hEXT, `hno]

end Note032PrimePowerFiltrationDependencyAudit
