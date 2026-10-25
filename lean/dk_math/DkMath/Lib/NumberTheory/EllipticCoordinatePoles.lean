/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticWeilTransport

#print "file: DkMath.Lib.NumberTheory.EllipticCoordinatePoles"

/-!
# NOTE-032-005C₂b: 一般座標の極と定数の正則性

[DkMath.Lib] 構成済みのpointValuationを使い、同じ関数体のx,yのOでの値を
exp(2),exp(3)として計算する。有限点では座標環の元なので値は1以下。
定数もOを含む全点で1以下であり、これが有限核の正規化座標和の極を調べる基礎となる。
値がexp(m)なら極の整数位数は−m。付値の値と加法的な位数の符号を区別する。
-/
namespace DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
open Polynomial WeierstrassCurve WeierstrassCurve.Affine WithZero
open EllipticFunctionField EllipticInfinityValuation
open scoped Polynomial.Bivariate
variable {K : Type*} [Field K] (E : WeierstrassCurve K) [E.IsElliptic]
attribute [local instance] geometricCoordinateRing_isDedekindDomain
noncomputable local instance instDecidableEqEllipticCoordinatePoles : DecidableEq (AlgebraicClosure K) := Classical.decEq _

/-- [DkMath.Lib] 一般x座標のOでの付値はexp(2)。座標環ノルムの次数2を使う。 -/
theorem pointValuation_zero_genericX :
    pointValuation E 0 (genericX E (AlgebraicClosure K)) = exp (2 : ℤ) := by
  rw [pointValuation, dite_eq_left rfl]
  change valuationInfty (E.toAffine⁄(AlgebraicClosure K))
    (algebraMap _ _ (CoordinateRing.mk (E.toAffine⁄(AlgebraicClosure K)) (C X))) = _
  rw [valuationInfty_algebraMap_of_ne_zero _ (InfinityCoordinateRing.mk_C_X_ne_zero' _),
    InfinityCoordinateRing.natDegree_norm_mk_C', natDegree_X]
  norm_num

/-- [DkMath.Lib] 一般y座標のOでの付値はexp(3)。同じ二元座標環のノルム次数を使う。 -/
theorem pointValuation_zero_genericY :
    pointValuation E 0 (genericY E (AlgebraicClosure K)) = exp (3 : ℤ) := by
  rw [pointValuation, dite_eq_left rfl]
  change valuationInfty (E.toAffine⁄(AlgebraicClosure K))
    (algebraMap _ _ (CoordinateRing.mk (E.toAffine⁄(AlgebraicClosure K)) Y)) = _
  rw [valuationInfty_algebraMap_of_ne_zero _ (InfinityCoordinateRing.mk_Y_ne_zero' _),
    InfinityCoordinateRing.natDegree_norm_mk_Y']
  rfl

/-- [DkMath.Lib] 有限点で一般x座標は正則。座標環からの包含の一般的な付値上界を使う。 -/
theorem pointValuation_genericX_le_one (P : Points E) (hP : P ≠ 0) :
    pointValuation E P (genericX E (AlgebraicClosure K)) ≤ 1 := by
  unfold pointValuation
  split_ifs with he
  · exact (hP he).elim
  · exact IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ _

/-- [DkMath.Lib] 有限点で一般y座標も正則。零点を含め、値が1と等しいとは限らない。 -/
theorem pointValuation_genericY_le_one (P : Points E) (hP : P ≠ 0) :
    pointValuation E P (genericY E (AlgebraicClosure K)) ≤ 1 := by
  unfold pointValuation
  split_ifs with he
  · exact (hP he).elim
  · exact IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ _

/-- [DkMath.Lib] 定数は無限遠点でも正則。零定数を許し、値1との等式にはしない。 -/
theorem pointValuation_zero_const_le_one (c : AlgebraicClosure K) :
    pointValuation E 0
      (algebraMap (AlgebraicClosure K) (E.toAffine⁄(AlgebraicClosure K)).FunctionField c) ≤ 1 := by
  rw [pointValuation, dite_eq_left rfl, ← EllipticInfinityValuation.FunctionField.algebraMap_mk_C_C,
    valuationInfty_algebraMap, EllipticInfinityValuation.CoordinateRing.valuationInftyDef]
  split_ifs
  · exact zero_le_one
  · rw [InfinityCoordinateRing.natDegree_norm_mk_C', natDegree_C]
    simp

/-- [DkMath.Lib] 係数体の定数はOを含む全ての点で正則である。 -/
theorem pointValuation_const_le_one (P : Points E) (c : AlgebraicClosure K) :
    pointValuation E P
      (algebraMap (AlgebraicClosure K) (E.toAffine⁄(AlgebraicClosure K)).FunctionField c) ≤ 1 := by
  by_cases hP : P = 0
  · subst P
    exact pointValuation_zero_const_le_one E c
  · unfold pointValuation
    split_ifs with he
    · exact (hP he).elim
    · exact valuation_algebraMap_le_one E (AlgebraicClosure K) P he c

/-- [DkMath.Lib] 非零定数の全点での付値は1。定数とその逆の正則性を併用する。 -/
theorem pointValuation_const_eq_one (P : Points E) {c : AlgebraicClosure K} (hc : c ≠ 0) :
    pointValuation E P
      (algebraMap (AlgebraicClosure K) (E.toAffine⁄(AlgebraicClosure K)).FunctionField c) = 1 := by
  apply le_antisymm (pointValuation_const_le_one E P c)
  have hi := pointValuation_const_le_one E P c⁻¹
  rw [map_inv₀, map_inv₀, inv_le_one₀] at hi
  · exact hi
  · rw [Valuation.pos_iff]
    exact (_root_.map_ne_zero _).mpr hc

/-- [DkMath.Lib] ある点で極を持つ有理関数は係数体上超越的である。
多項式の最高次項が付値で支配するため、非零多項式の代入は零にならない。 -/
theorem transcendental_of_point_pole
    (P : Points E) (f : (E.toAffine⁄(AlgebraicClosure K)).FunctionField)
    (hpole : 1 < pointValuation E P f) : Transcendental (AlgebraicClosure K) f := by
  apply transcendental_iff.mpr
  intro p hp
  by_contra hne
  have hv := (pointValuation E P).map_aeval_eq_pow_of_one_lt
    (fun c hc => pointValuation_const_eq_one E P hc) hpole hne
  rw [hp, map_zero] at hv
  exact (pow_ne_zero _ (ne_of_gt (lt_trans zero_lt_one hpole))) hv.symm

end DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
