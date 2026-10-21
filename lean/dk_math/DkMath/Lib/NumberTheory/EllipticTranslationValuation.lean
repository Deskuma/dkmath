/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from anthropics/fermats-last-theorem,
P2M/Sol/S_WeierstrassCurve_Affine_valuation_transEquiv_le.lean.
Upstream blob: 40979bfb1f6b10e41bc74964bdacaa9ad0107795
Also adapted: valuation_transEquiv_le_self (69bc96ee3ad715d6e8bb140d20e02817466e53d4)
and valuation_transEquiv_weilFun (c0885c4b116e8e30adac07f430e44e2160b3f6f6).
Modified for DkMath: remove export macros and document actual valuation transport.
-/

import DkMath.Lib.NumberTheory.EllipticValuationTransport
import DkMath.Lib.Algebra.DiscreteValuationRigidity

#print "file: DkMath.Lib.NumberTheory.EllipticTranslationValuation"

/-!
# 有限点間の平行移動と付値の一致
異なるx座標の割線と、同一点の接線を分け、移動先の座標への合同を証明する。
局所環の分母を通して得た付値環の包含と、正規化された整数離散付値の剛性を合わせる。
P+S=Oの例外には、別途無限遠点の付値を用いる。
-/
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open scoped Polynomial.Bivariate
namespace DkMath.Lib.NumberTheory.EllipticFunctionField

section TransportTau

variable {R : Type*} [Field R] (W : WeierstrassCurve R) (K : Type*) [Field K] [Algebra R K]
  [DecidableEq K] [IsAlgClosed K] [W.IsElliptic] [IsDedekindDomain (W⁄K).CoordinateRing]

omit [DecidableEq K] [IsAlgClosed K] [W.IsElliptic] [IsDedekindDomain (W⁄K).CoordinateRing] in
/-- 一般x座標は定数ではない。X−cの座標環内での非零性を使う。 -/
theorem genericX_ne_algebraMap (c : K) : genericX W K ≠ algebraMap K (W⁄K).FunctionField c := by
  intro h
  apply CoordinateRing.XClass_ne_zero (W' := W⁄K) c
  apply IsFractionRing.injective (W⁄K).CoordinateRing (W⁄K).FunctionField
  have e1 : algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField (CoordinateRing.mk (W⁄K) (C X)) =
      genericX W K := rfl
  have e2 : algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField (CoordinateRing.mk (W⁄K) (C (C c))) =
      algebraMap K _ c := (IsScalarTower.algebraMap_apply K (W⁄K).CoordinateRing (W⁄K).FunctionField c).symm
  rw [CoordinateRing.XClass, map_sub, map_sub, map_sub, _root_.map_zero, e1, e2, h, sub_self]

omit [DecidableEq K] [IsAlgClosed K] [W.IsElliptic] [IsDedekindDomain (W⁄K).CoordinateRing] in
/-- 二段階の基底変換の係数を、係数体からの像として揃える。 -/
theorem baseChange_a_eq :
    (W⁄(W⁄K).FunctionField).a₁ = algebraMap K _ (W⁄K).a₁ ∧ (W⁄(W⁄K).FunctionField).a₂ = algebraMap K _ (W⁄K).a₂ ∧
    (W⁄(W⁄K).FunctionField).a₃ = algebraMap K _ (W⁄K).a₃ ∧ (W⁄(W⁄K).FunctionField).a₄ = algebraMap K _ (W⁄K).a₄ ∧
    (W⁄(W⁄K).FunctionField).a₆ = algebraMap K _ (W⁄K).a₆ :=
  ⟨IsScalarTower.algebraMap_apply R K _ W.a₁, IsScalarTower.algebraMap_apply R K _ W.a₂,
    IsScalarTower.algebraMap_apply R K _ W.a₃, IsScalarTower.algebraMap_apply R K _ W.a₄,
    IsScalarTower.algebraMap_apply R K _ W.a₆⟩

variable {W K} in
omit [DecidableEq K] [IsAlgClosed K] [W.IsElliptic] in
/-- 傾きと入力座標が合同なら、加法の出力座標も合同になる。 -/
theorem cong_addX_addY {P : (W⁄K).Point} (hP : P ≠ 0) {x₁ x₂ y₁ ℓ : (W⁄K).FunctionField}
    {x₁' x₂' y₁' ℓ' : K}
    (h₁ : ((placeOf W K P hP).valuation _).Cong x₁ (algebraMap K _ x₁'))
    (h₂ : ((placeOf W K P hP).valuation _).Cong x₂ (algebraMap K _ x₂'))
    (h₃ : ((placeOf W K P hP).valuation _).Cong y₁ (algebraMap K _ y₁'))
    (h₄ : ((placeOf W K P hP).valuation _).Cong ℓ (algebraMap K _ ℓ')) :
    ((placeOf W K P hP).valuation _).Cong ((W⁄(W⁄K).FunctionField).addX x₁ x₂ ℓ)
        (algebraMap K _ ((W⁄K).addX x₁' x₂' ℓ')) ∧
      ((placeOf W K P hP).valuation _).Cong ((W⁄(W⁄K).FunctionField).addY x₁ x₂ y₁ ℓ)
        (algebraMap K _ ((W⁄K).addY x₁' x₂' y₁' ℓ')) := by
  set v := (placeOf W K P hP).valuation (W⁄K).FunctionField
  have hc := valuation_algebraMap_le_one W K P hP
  obtain ⟨e1, e2, e3, -, -⟩ := baseChange_a_eq W K
  have hX : v.Cong ((W⁄(W⁄K).FunctionField).addX x₁ x₂ ℓ) (algebraMap K _ ((W⁄K).addX x₁' x₂' ℓ')) := by
    simp only [addX, map_sub, map_add, map_mul, map_pow, e1, e2]
    exact ((((h₄.pow (hc _) 2).add ((Valuation.Cong.refl _).mul h₄ (hc _) (hc _))).sub
      (Valuation.Cong.refl _)).sub h₁).sub h₂
  refine ⟨hX, ?_⟩
  simp only [addY, negY, negAddY, map_sub, map_add, map_mul, map_neg, e1, e3]
  have hX' : v.Cong ((W⁄(W⁄K).FunctionField).addX x₁ x₂ ℓ - x₁)
      (algebraMap K _ ((W⁄K).addX x₁' x₂' ℓ') - algebraMap K _ x₁') := hX.sub h₁
  have hN : v.Cong (ℓ * ((W⁄(W⁄K).FunctionField).addX x₁ x₂ ℓ - x₁) + y₁)
      (algebraMap K _ ℓ' * (algebraMap K _ ((W⁄K).addX x₁' x₂' ℓ') - algebraMap K _ x₁') +
        algebraMap K _ y₁') :=
    (h₄.mul hX' (hc _) (by rw [← map_sub]; exact hc _)).add h₃
  exact ((hN.neg).sub ((Valuation.Cong.refl _).mul hX (hc _) (hc _))).sub (Valuation.Cong.refl _)

/-- 異なるx座標での加法公式により、有限点から有限点への付値上界を輸送する。 -/
theorem valuation_transEquiv_le' {P S : (W⁄K).Point} (hP : P ≠ 0) (hS : S ≠ 0) (hx : P.xc ≠ S.xc)
    (hPS : P + S ≠ 0) (h : (W⁄K).FunctionField) (k : ℕ)
    (hh : (placeOf W K (P + S) hPS).valuation (W⁄K).FunctionField h ≤ exp (-(k : ℤ))) :
    (placeOf W K P hP).valuation (W⁄K).FunctionField (transEquiv W K S h) ≤ exp (-(k : ℤ)) := by
  set v := (placeOf W K P hP).valuation (W⁄K).FunctionField with hv
  have hc := valuation_algebraMap_le_one W K P hP
  rcases P with _ | ⟨a, b, hab⟩
  · exact absurd rfl hP
  rcases S with _ | ⟨xS, yS, hSns⟩
  · exact absurd rfl hS
  simp only [Point.xc_some] at hx
  have hγx : genericX W K ≠ algebraMap K (W⁄K).FunctionField xS := genericX_ne_algebraMap W K xS
  have hγx' : genericX W K ≠ Algebra.ofId K (W⁄K).FunctionField xS := hγx
  have hQx : (genericPoint W K + Point.baseChange K (W⁄K).FunctionField (.some xS yS hSns)).xc =
      (W⁄(W⁄K).FunctionField).addX (genericX W K) (algebraMap K (W⁄K).FunctionField xS)
        ((W⁄(W⁄K).FunctionField).slope (genericX W K) (algebraMap K (W⁄K).FunctionField xS) (genericY W K) (algebraMap K (W⁄K).FunctionField yS)) := by
    rw [genericPoint, Point.baseChange, Point.map_some, Point.add_of_X_ne hγx', Point.xc_some]; rfl
  have hQy : (genericPoint W K + Point.baseChange K (W⁄K).FunctionField (.some xS yS hSns)).yc =
      (W⁄(W⁄K).FunctionField).addY (genericX W K) (algebraMap K (W⁄K).FunctionField xS) (genericY W K)
        ((W⁄(W⁄K).FunctionField).slope (genericX W K) (algebraMap K (W⁄K).FunctionField xS) (genericY W K) (algebraMap K (W⁄K).FunctionField yS)) := by
    rw [genericPoint, Point.baseChange, Point.map_some, Point.add_of_X_ne hγx', Point.yc_some]; rfl
  have hX := cong_genericX W K (.some a b hab) hP
  have hY := cong_genericY W K (.some a b hab) hP
  simp only [Point.xc_some, Point.yc_some] at hX hY
  have hslope : v.Cong ((W⁄(W⁄K).FunctionField).slope (genericX W K) (algebraMap K (W⁄K).FunctionField xS) (genericY W K) (algebraMap K (W⁄K).FunctionField yS))
      (algebraMap K (W⁄K).FunctionField ((W⁄K).slope a xS b yS)) := by
    rw [slope_of_X_ne hγx, slope_of_X_ne hx, map_div₀, map_sub, map_sub]
    refine (hY.sub (Valuation.Cong.refl _)).div (hX.sub (Valuation.Cong.refl _))
      (by rw [← map_sub]; exact hc _) ?_
    rw [← map_sub]
    exact valuation_algebraMap_eq_one W K _ hP (sub_ne_zero.mpr hx)
  obtain ⟨hcx, hcy⟩ := cong_addX_addY (P := .some a b hab) hP (x₂' := xS) hX
    (Valuation.Cong.refl (algebraMap K (W⁄K).FunctionField xS)) hY hslope
  rw [transEquiv_apply, transPull]
  refine valuation_pointPull_le W K _ _ _ hP hPS ?_ ?_ h k hh
  · rw [hQx, Point.add_of_X_ne hx, Point.xc_some]
    exact hcx
  · rw [hQy, Point.add_of_X_ne hx, Point.yc_some]
    exact hcy

end TransportTau

section TransportTauSelf

variable {R : Type*} [Field R] (W : WeierstrassCurve R) (K : Type*) [Field K] [Algebra R K]
  [DecidableEq K] [IsAlgClosed K] [W.IsElliptic] [IsDedekindDomain (W⁄K).CoordinateRing]

/-- y座標を固定したWeierstrass方程式をxの多項式として定義する。 -/
noncomputable def wAtY (b : K) : K[X] :=
  C b ^ 2 + (C (W⁄K).a₁ * X + C (W⁄K).a₃) * C b - (X ^ 3 + C (W⁄K).a₂ * X ^ 2 + C (W⁄K).a₄ * X + C (W⁄K).a₆)

omit [DecidableEq K] [IsAlgClosed K] [W.IsElliptic] [IsDedekindDomain (W⁄K).CoordinateRing] in
/-- 固定したy=bでの方程式を点(a,b)に評価する。 -/
theorem eval_wAtY (a b : K) : (wAtY W K b).eval a =
    b ^ 2 + (W⁄K).a₁ * a * b + (W⁄K).a₃ * b - (a ^ 3 + (W⁄K).a₂ * a ^ 2 + (W⁄K).a₄ * a + (W⁄K).a₆) := by
  simp only [wAtY, eval_add, eval_sub, eval_mul, eval_pow, eval_C, eval_X]
  ring

omit [DecidableEq K] [IsAlgClosed K] [W.IsElliptic] [IsDedekindDomain (W⁄K).CoordinateRing] in
/-- 接線の式に使うx方向微分を計算する。 -/
theorem eval_derivative_wAtY (a b : K) : (derivative (wAtY W K b)).eval a =
    (W⁄K).a₁ * b - (3 * a ^ 2 + 2 * (W⁄K).a₂ * a + (W⁄K).a₄) := by
  simp only [wAtY, derivative_add, derivative_sub, derivative_mul, derivative_pow, derivative_C,
    derivative_X, eval_add, eval_sub, eval_mul, eval_pow, eval_C, eval_X,
    Nat.cast_ofNat, zero_mul, mul_zero, mul_one, zero_add, add_zero]
  ring

omit [DecidableEq K] [IsAlgClosed K] [IsDedekindDomain (W⁄K).CoordinateRing] in
/-- 一般点が曲線上にあることから、固定yの多項式を二つのy差の積に分解する。 -/
theorem eval₂_wAtY_generic (b : K) :
    (wAtY W K b).eval₂ (algebraMap K (W⁄K).FunctionField) (genericX W K) =
      (genericY W K - algebraMap K _ b) *
        ((W⁄(W⁄K).FunctionField).negY (genericX W K) (genericY W K) - algebraMap K _ b) := by
  have heq := (generic_nonsingular W K).left
  rw [equation_iff] at heq
  obtain ⟨e1, e2, e3, e4, e6⟩ := baseChange_a_eq W K
  simp only [wAtY, eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow, eval₂_C, eval₂_X, negY]
  rw [← e1, ← e2, ← e3, ← e4, ← e6]
  rw [e1, e2, e3, e4, e6] at heq ⊢
  linear_combination heq

/-- 接線の分母を正則な商へ書き直し、P=Sの倍加でも付値上界を輸送する。 -/
theorem valuation_transEquiv_le_self' {S : (W⁄K).Point} (hS : S ≠ 0) (h2S : S + S ≠ 0)
    (h : (W⁄K).FunctionField) (k : ℕ)
    (hh : (placeOf W K (S + S) h2S).valuation (W⁄K).FunctionField h ≤ exp (-(k : ℤ))) :
    (placeOf W K S hS).valuation (W⁄K).FunctionField (transEquiv W K S h) ≤ exp (-(k : ℤ)) := by
  set v := (placeOf W K S hS).valuation (W⁄K).FunctionField with hv
  have hc := valuation_algebraMap_le_one W K S hS
  rcases S with _ | ⟨xS, yS, hSns⟩
  · exact absurd rfl hS
  have hy : yS ≠ (W⁄K).negY xS yS := fun h => h2S (Point.add_self_of_Y_eq h)
  have hγx : genericX W K ≠ algebraMap K (W⁄K).FunctionField xS := genericX_ne_algebraMap W K xS
  have hγx' : genericX W K ≠ Algebra.ofId K (W⁄K).FunctionField xS := hγx
  have hQx : (genericPoint W K + Point.baseChange K (W⁄K).FunctionField (.some xS yS hSns)).xc =
      (W⁄(W⁄K).FunctionField).addX (genericX W K) (algebraMap K (W⁄K).FunctionField xS)
        ((W⁄(W⁄K).FunctionField).slope (genericX W K) (algebraMap K (W⁄K).FunctionField xS)
          (genericY W K) (algebraMap K (W⁄K).FunctionField yS)) := by
    rw [genericPoint, Point.baseChange, Point.map_some, Point.add_of_X_ne hγx', Point.xc_some]; rfl
  have hQy : (genericPoint W K + Point.baseChange K (W⁄K).FunctionField (.some xS yS hSns)).yc =
      (W⁄(W⁄K).FunctionField).addY (genericX W K) (algebraMap K (W⁄K).FunctionField xS) (genericY W K)
        ((W⁄(W⁄K).FunctionField).slope (genericX W K) (algebraMap K (W⁄K).FunctionField xS)
          (genericY W K) (algebraMap K (W⁄K).FunctionField yS)) := by
    rw [genericPoint, Point.baseChange, Point.map_some, Point.add_of_X_ne hγx', Point.yc_some]; rfl
  have hX := cong_genericX W K (.some xS yS hSns) hS
  have hY := cong_genericY W K (.some xS yS hSns) hS
  simp only [Point.xc_some, Point.yc_some] at hX hY
  obtain ⟨e1, e2, e3, e4, e6⟩ := baseChange_a_eq W K
  have hD : v.Cong ((W⁄(W⁄K).FunctionField).negY (genericX W K) (genericY W K) - algebraMap K _ yS)
      (algebraMap K _ ((W⁄K).negY xS yS - yS)) := by
    simp only [negY, map_sub, map_neg, map_mul, e1, e3]
    exact (((hY.neg).sub ((Valuation.Cong.refl _).mul hX (hc _) (hc _))).sub (Valuation.Cong.refl _)).sub
      (Valuation.Cong.refl _)
  have hD0 : (W⁄K).negY xS yS - yS ≠ 0 := sub_ne_zero.mpr (Ne.symm hy)
  have hD1 : v ((W⁄(W⁄K).FunctionField).negY (genericX W K) (genericY W K) - algebraMap K _ yS) = 1 :=
    hD.eq_of_eq_one (valuation_algebraMap_eq_one W K _ hS hD0)
  have hDL : (W⁄(W⁄K).FunctionField).negY (genericX W K) (genericY W K) - algebraMap K _ yS ≠ 0 := by
    intro h0; rw [h0, Valuation.map_zero] at hD1; exact zero_ne_one hD1
  have hroot : (wAtY W K yS).IsRoot xS := by
    rw [IsRoot.def, eval_wAtY]
    have := hSns.left
    rw [equation_iff] at this
    linear_combination this
  set q := wAtY W K yS /ₘ (X - C xS) with hq
  have hwq : (X - C xS) * q = wAtY W K yS := mul_divByMonic_eq_iff_isRoot.mpr hroot
  have hqxS : q.eval xS = (W⁄K).a₁ * yS - (3 * xS ^ 2 + 2 * (W⁄K).a₂ * xS + (W⁄K).a₄) := by
    have key := congrArg (eval xS) (divByMonic_add_X_sub_C_mul_derivative_divByMonic_eq_derivative (wAtY W K yS) xS)
    rw [eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, add_zero] at key
    rw [key, eval_derivative_wAtY]
  have hΛ : (W⁄(W⁄K).FunctionField).slope (genericX W K) (algebraMap K _ xS) (genericY W K) (algebraMap K _ yS) =
      q.eval₂ (algebraMap K (W⁄K).FunctionField) (genericX W K) /
        ((W⁄(W⁄K).FunctionField).negY (genericX W K) (genericY W K) - algebraMap K _ yS) := by
    rw [slope_of_X_ne hγx, div_eq_div_iff (sub_ne_zero.mpr hγx) hDL, ← eval₂_wAtY_generic, ← hwq,
      eval₂_mul, eval₂_sub, eval₂_X, eval₂_C]
    ring
  have hslope : v.Cong ((W⁄(W⁄K).FunctionField).slope (genericX W K) (algebraMap K _ xS) (genericY W K)
      (algebraMap K _ yS)) (algebraMap K _ ((W⁄K).slope xS xS yS yS)) := by
    rw [hΛ, slope_of_Y_ne rfl hy]
    have hq' := Valuation.Cong.eval₂ (v := v) (algebraMap K _) hc hX (hc _) q
    rw [eval₂_at_apply, hqxS] at hq'
    have : (3 * xS ^ 2 + 2 * (W⁄K).a₂ * xS + (W⁄K).a₄ - (W⁄K).a₁ * yS) / (yS - (W⁄K).negY xS yS) =
        ((W⁄K).a₁ * yS - (3 * xS ^ 2 + 2 * (W⁄K).a₂ * xS + (W⁄K).a₄)) / ((W⁄K).negY xS yS - yS) := by
      rw [← neg_sub ((W⁄K).negY xS yS) yS, ← neg_sub ((W⁄K).a₁ * yS), neg_div_neg_eq]
    rw [this, map_div₀]
    exact hq'.1.div hD hq'.2 (valuation_algebraMap_eq_one W K _ hS hD0)
  obtain ⟨hcx, hcy⟩ := cong_addX_addY (P := .some xS yS hSns) hS (x₂' := xS) hX
    (Valuation.Cong.refl (algebraMap K (W⁄K).FunctionField xS)) hY hslope
  rw [transEquiv_apply, transPull]
  refine valuation_pointPull_le W K _ _ _ hS h2S ?_ ?_ h k hh
  · rw [hQx, Point.add_self_of_Y_ne hy, Point.xc_some]
    exact hcx
  · rw [hQy, Point.add_self_of_Y_ne hy, Point.yc_some]
    exact hcy

end TransportTauSelf

variable {R : Type*} [Field R] (W : WeierstrassCurve R) (K : Type*) [Field K] [Algebra R K]
  [DecidableEq K] [IsAlgClosed K] [W.IsElliptic] [IsDedekindDomain (W⁄K).CoordinateRing]

/-- P≠OかつP+S≠Oなら、実際の平行移動による引き戻しは付値を移動先の付値へ一致させる。 -/
theorem valuation_transEquiv_eq {P S : (W⁄K).Point} (hP : P ≠ 0) (hPS : P + S ≠ 0)
    (h : (W⁄K).FunctionField) :
    (placeOf W K P hP).valuation (W⁄K).FunctionField (transEquiv W K S h) =
      (placeOf W K (P + S) hPS).valuation (W⁄K).FunctionField h := by
  by_cases hS : S = 0
  · subst hS
    simp only [transEquiv_zero, AlgEquiv.coe_refl, id_eq]
    have key : ∀ (Q : (W⁄K).Point) (hQ : Q ≠ 0), Q = P →
        (placeOf W K P hP).valuation (W⁄K).FunctionField h =
          (placeOf W K Q hQ).valuation (W⁄K).FunctionField h := by
      rintro Q hQ rfl; rfl
    exact key (P + 0) hPS (add_zero P)
  have hle : ∀ f : (W⁄K).FunctionField,
      (placeOf W K (P + S) hPS).valuation (W⁄K).FunctionField f ≤ 1 →
        (placeOf W K P hP).valuation (W⁄K).FunctionField (transEquiv W K S f) ≤ 1 := by
    intro f hf
    have hf' : (placeOf W K (P + S) hPS).valuation (W⁄K).FunctionField f ≤ exp (-((0 : ℕ) : ℤ)) := by
      simpa using hf
    by_cases hx : P.xc ≠ S.xc
    · simpa using valuation_transEquiv_le' W K hP hS hx hPS f 0 hf'
    · rw [not_ne_iff] at hx
      have hPS' : P = S := by
        rcases P with _ | ⟨a, b, hab⟩
        · exact absurd rfl hP
        rcases S with _ | ⟨c, d, hcd⟩
        · exact absurd rfl hS
        simp only [Point.xc_some] at hx
        subst hx
        rcases Y_eq_of_X_eq hab.left hcd.left rfl with hy | hy
        · subst hy; rfl
        · exact absurd (Point.add_of_Y_eq rfl hy) hPS
      subst hPS'
      simpa using valuation_transEquiv_le_self' W K hP hPS f 0 hf'
  have key := Valuation.eq_comap_of_valuationSubring_le_comap_aux
    (v := (placeOf W K P hP).valuation (W⁄K).FunctionField)
    (w := (placeOf W K (P + S) hPS).valuation (W⁄K).FunctionField)
    (valuation_surjective _ _) (valuation_surjective _ _) (transEquiv W K S).toRingEquiv
    (fun f hf => (ValuationSubring.mem_comap).mpr (hle f hf))
  rw [key]
  rfl
end DkMath.Lib.NumberTheory.EllipticFunctionField
