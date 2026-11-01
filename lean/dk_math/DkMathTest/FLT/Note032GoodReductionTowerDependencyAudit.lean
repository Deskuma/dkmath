/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyGoodReductionTowerObstruction

/-!
# 特性方程式を使わない最終計数矛盾の依存監査

実際の Frobenius・良還元単射・素体への降下・全捩れの濃度へ到達することを要求する。
旧 hCH 経路を消費せず、点数と塔の指数の一致および残る局所入力を公開型で保持する。
-/

namespace Note032GoodReductionTowerDependencyAudit

open Lean Elab Command

private def forbidden (n : Name) : Bool :=
  let s := (privateToUserName n).toString
  n == ``sorryAx || s.startsWith "FrobeniusEndo." ||
    s.startsWith "DkMath.Lib.Algebra.TorsionTowerFrobenius." ||
    s.endsWith "_inertia_frobenius_impossible" || s.startsWith "P2M." || s.startsWith "P2MW." ||
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
-- Seven finite traversals include imported types, constructors and opaque proof bodies.
run_cmd do
  checkRoot ``DkMath.Lib.NumberTheory.FiniteFieldFrobeniusFixed.exists_preimage_of_pow_card_eq
    #[``Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero,
      ``FiniteField.X_pow_card_sub_X_ne_zero]
  checkRoot ``DkMath.Lib.NumberTheory.EllipticFrobeniusFixedReduction.exists_finite_point_of_fixed_torsion
    #[``DkMath.Lib.NumberTheory.FiniteFieldFrobeniusFixed.exists_preimage_of_pow_card_eq,
      ``DkMath.Lib.NumberTheory.EllipticTorsionValuationIntegrality.torsion_coordinates_mem,
      ``DkMath.Lib.NumberTheory.ValuationFrobenius.IsFrobeniusAt.smul_residue_eq]
  checkRoot ``DkMath.Lib.NumberTheory.EllipticFrobeniusFixedReduction.card_fixed_torsion_le_finite_points
    #[``DkMath.Lib.NumberTheory.EllipticFrobeniusFixedReduction.exists_finite_point_of_fixed_torsion,
      ``DkMath.Lib.NumberTheory.EllipticFrobeniusFixedReduction.integerReduction_injOn_torsion,
      ``DkMath.Lib.NumberTheory.EllipticSmoothTorsionReduction.reduce_injOn_torsion]
  checkRoot ``DkMath.Lib.NumberTheory.EllipticFrobeniusFixedReduction.torsion_index_le_finite_point_count_of_absorbing
    #[``DkMath.Lib.Algebra.FiniteFixedQuotient.card_le_card_fixed_mul,
      ``DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.card_torsion_sq,
      ``DkMath.Lib.NumberTheory.EllipticFrobeniusFixedReduction.card_fixed_torsion_le_finite_points]
  checkRoot ``DkMath.FLT.Frey.Source.exists_good_prime_ne
    #[``Nat.exists_infinite_primes, ``DkMath.FLT.Frey.Source.curve_discriminant_ne_zero]
  checkRoot ``DkMath.FLT.Frey.Source.prime_power_pointAction_sub_mem_of_resonant_inertia
    #[``DkMath.Lib.NumberTheory.AbsoluteInertiaGeneration.subgroup_eq_top_of_inertia_le,
      ``DkMath.FLT.Frey.Source.prime_power_pointAction_sub_mem_cyclic_tower_at_p,
      ``DkMath.FLT.Frey.Source.prime_power_pointAction_sub_mem_of_nonresonant_bad]
  checkRoot ``DkMath.FLT.Frey.Source.residual_cofixed_point_count_tower_resonant_inertia_impossible
    #[``DkMath.Lib.NumberTheory.EllipticFrobeniusFixedReduction.torsion_index_le_finite_point_count_of_absorbing,
      ``DkMath.Lib.NumberTheory.ValuationFrobenius.exists_isFrobeniusAt_of_liesOverPrime,
      ``DkMath.FLT.Frey.Source.goodReductionPointCount_pos,
      ``DkMath.FLT.Frey.Source.prime_power_pointAction_sub_mem_of_resonant_inertia]
  checkInputs ``DkMath.Lib.NumberTheory.FiniteFieldFrobeniusFixed.exists_preimage_of_pow_card_eq
    #[`F, `K, `x, `hx] #[`hdesc, `hCH]
  checkInputs ``DkMath.Lib.NumberTheory.EllipticFrobeniusFixedReduction.exists_finite_point_of_fixed_torsion
    #[`hW, `hq, `hgood, `hqn, `hA, `hσ, `hP, `hfix]
    #[`hdesc, `hCH, `hinj, `hno]
  checkInputs ``DkMath.Lib.NumberTheory.EllipticFrobeniusFixedReduction.card_fixed_torsion_le_finite_points
    #[`hW, `hq, `hgood, `hqn, `hA, `hσ]
    #[`hcount, `hCH, `hinj, `hno]
  checkInputs ``DkMath.Lib.NumberTheory.EllipticFrobeniusFixedReduction.torsion_index_le_finite_point_count_of_absorbing
    #[`hW, `hq, `hn, `hgood, `hqn, `hA, `hσ, `hK, `habs]
    #[`hCH, `hcardT, `hno]
  checkInputs ``DkMath.FLT.Frey.Source.exists_good_prime_ne
    #[`S] #[`hell, `hgood, `hCH, `hno]
  checkInputs ``DkMath.FLT.Frey.Source.prime_power_pointAction_sub_mem_of_resonant_inertia
    #[`hp5, `hcofixed, `hstable, `hN, `hcard, `hbase, `hbad, `hy]
    #[`hfixed, `hCH, `hEXT, `hno]
  checkInputs ``DkMath.FLT.Frey.Source.residual_cofixed_point_count_tower_resonant_inertia_impossible
    #[`hp5, `hell, `hellp, `hgood, `hcofixed, `hstable, `hcard, `hbase, `hbad]
    #[`N, `hN, `σ, `hσ, `A, `hA, `hfixed, `hCH, `hEXT, `hno]
  let env ← getEnv
  let some info := env.checked.get.find?
    ``DkMath.FLT.Frey.Source.residual_cofixed_point_count_tower_resonant_inertia_impossible
    | throwError "Missing final endpoint"
  unless info.type.getUsedConstants.contains ``DkMath.FLT.Frey.Source.goodReductionPointCount do
    throwError "Actual finite point count absent from final public type"
  logInfo "PASS index: actual finite point count occurs in final public type; no independent N or hCH input."

end Note032GoodReductionTowerDependencyAudit
