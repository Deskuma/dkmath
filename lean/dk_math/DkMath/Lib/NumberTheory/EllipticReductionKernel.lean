/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticDyadicSeparation
import DkMath.Lib.NumberTheory.EllipticGoodReductionSeparation
import DkMath.Lib.NumberTheory.ValuationPrimeSupport

#print "file: DkMath.Lib.NumberTheory.EllipticReductionKernel"

/-!
# NOTE-031-004B: 還元核の加法閉性を整点と極の加法から証明する

整な有限点と極を持つ点を足すと、和のx座標は整となる。
割線公式の分母の付値はv(x₂)²、分子はx₁x₂²+b x₂-c y₂+dとなり、b,c,dは整である。
曲線方程式からv(y₂)<v(x₂)²を得るので、商の付値は1以下となる。

極を持つ二点の和が整な有限点なら、その和から第二点を引くことで
「整点＋極が極になる」矛盾を得る。従って無限遠と極の点は加法部分群をなす。
形式群の全展開を構成せず、実際の点群の加法公式と反転を使う。
この部分群は単元位数に限定しないので、剰余標数と同じp-torsionへも使える。
-/
namespace DkMath.Lib.NumberTheory.EllipticReductionKernel
open WeierstrassCurve WeierstrassCurve.Affine
open EllipticDyadicSeparation
variable {K : Type*} [Field K] [DecidableEq K] (A : ValuationSubring K)
  (W : WeierstrassCurve A)
local notation "E" => W.map A.subtype

omit [DecidableEq K] in
private theorem model_integral : Integral A (W.map A.subtype) :=
  ⟨W.a₁.2, W.a₂.2, W.a₃.2, W.a₄.2, W.a₆.2⟩

/-- 整な有限点と極の有限点との和のx座標は整となる。
極同士の加法を直接展開せずに還元核の閉性を示すための核である。 -/
theorem addX_mem_of_integral_pole {x₁ y₁ x₂ y₂ : K}
    (h₂ : (E).toAffine.Equation x₂ y₂) (hx₁ : x₁ ∈ A) (hy₁ : y₁ ∈ A)
    (hx₂ : 1 < A.valuation x₂) :
    (E).toAffine.addX x₁ x₂ ((E).toAffine.slope x₁ x₂ y₁ y₂) ∈ A := by
  have hxi := (A.valuation_le_one_iff _).mpr hx₁
  have hne : x₁ ≠ x₂ := by
    intro h
    rw [h] at hxi
    exact hx₂.not_ge hxi
  have hd0 : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hne
  have hvx0 : 0 < A.valuation x₂ := zero_lt_one.trans hx₂
  have hvx2 : A.valuation x₂ < A.valuation x₂ ^ 2 := by
    simpa only [pow_two, mul_one] using mul_lt_mul_of_pos_left hx₂ hvx0
  have hvy : A.valuation y₂ < A.valuation x₂ ^ 2 := by
    have hv := (v_pole (model_integral A W) h₂ hx₂).1
    apply lt_of_pow_lt_pow_left₀ 2 zero_le
    rw [hv, ← pow_mul]
    exact pow_lt_pow_right₀ hx₂ (by norm_num)
  let X : A := ⟨x₁, hx₁⟩
  let Y : A := ⟨y₁, hy₁⟩
  let b : A := 2 * W.a₂ * X - W.a₁ * Y + X ^ 2 + W.a₄
  let c : A := 2 * Y + W.a₁ * X + W.a₃
  let d : A := Y ^ 2 + W.a₁ * X * Y + W.a₆ - W.a₂ * X ^ 2 - X ^ 3
  have hb := (A.valuation_le_one_iff _).mpr b.2
  have hc := (A.valuation_le_one_iff _).mpr c.2
  have hd := (A.valuation_le_one_iff _).mpr d.2
  have heq : (E).toAffine.addX x₁ x₂ ((E).toAffine.slope x₁ x₂ y₁ y₂) =
      (x₁ * x₂ ^ 2 + (b : K) * x₂ - (c : K) * y₂ + d) / (x₁ - x₂) ^ 2 := by
    rw [slope_of_X_ne hne, addX]
    have he := (equation_iff ..).mp h₂
    dsimp [b, c, d, X, Y]
    simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
      WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at he ⊢
    field_simp
    norm_num [ValuationSubring.subtype_apply] at he ⊢
    simp only [show ((2 : A) : K) = (2 : K) from rfl]
    linear_combination he
  have hden : A.valuation (x₁ - x₂) = A.valuation x₂ :=
    Valuation.map_sub_eq_of_lt_right _ (hxi.trans_lt hx₂)
  apply (A.valuation_le_one_iff _).mp
  rw [heq, map_div₀, map_pow, hden, div_le_one₀ (pow_pos hvx0 2)]
  refine Valuation.map_add_le _ (Valuation.map_sub_le _ (Valuation.map_add_le _ ?_ ?_) ?_) ?_
  · rw [map_mul, map_pow]
    exact mul_le_of_le_one_left' hxi
  · rw [map_mul]
    exact (mul_le_of_le_one_left' hb).trans hvx2.le
  · rw [map_mul]
    exact (mul_le_of_le_one_left' hc).trans hvy.le
  · exact hd.trans (one_le_pow₀ hx₂.le)

/-- 無限遠点とx座標に極を持つ点からなる実際の加法部分群。 -/
def reductionKernel : AddSubgroup (W.map A.subtype).toAffine.Point where
  carrier := {P | PoleOrZero A (W.map A.subtype) P}
  zero_mem' := poleOrZero_zero
  neg_mem' := by
    rintro (_ | ⟨x, y, h⟩) hP
    · exact poleOrZero_zero
    · change PoleOrZero A (E) (-Point.some x y h)
      rw [Point.neg_some, poleOrZero_some_iff]
      exact poleOrZero_some_iff.mp hP
  add_mem' := by
    rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩) hP hQ
    · simpa only [← Point.zero_def, zero_add] using hQ
    · simpa only [← Point.zero_def, zero_add] using hQ
    · simpa only [← Point.zero_def, add_zero] using hP
    · intro x y h heq
      by_contra hxp
      have hx : x ∈ A := (A.valuation_le_one_iff _).mp (le_of_not_gt hxp)
      have hy : y ∈ A := EllipticTorsionValuationIntegrality.y_mem_of_x_mem A W _ rfl h.1 hx
      have hx₂ := poleOrZero_some_iff.mp hQ
      have hne : x ≠ x₂ := by
        intro hh
        rw [hh] at hx
        exact hx₂.not_ge ((A.valuation_le_one_iff _).mpr hx)
      have hback : Point.some x y h + (-Point.some x₂ y₂ h₂) = Point.some x₁ y₁ h₁ := by
        rw [← heq, add_neg_cancel_right]
      rw [Point.neg_some, Point.add_of_X_ne hne] at hback
      have hab := addX_mem_of_integral_pole A W
        ((nonsingular_neg ..).mpr h₂).1 hx hy hx₂
      have hinj := (Point.some.inj hback).1
      rw [hinj] at hab
      exact (poleOrZero_some_iff.mp hP).not_ge ((A.valuation_le_one_iff _).mpr hab)

/-- 有限点が還元核に属する条件は、まさにx座標が付値環を外れることである。 -/
theorem some_mem_iff {x y : K} (h : (E).toAffine.Nonsingular x y) :
    Point.some x y h ∈ reductionKernel A W ↔ x ∉ A := by
  change PoleOrZero A (E) (Point.some x y h) ↔ x ∉ A
  rw [poleOrZero_some_iff, ← A.valuation_le_one_iff]
  exact not_le.symm

/-- 整性が係数ごとに与えられた元の曲線上の還元核。一般ファイバーを選び直さない。 -/
noncomputable def ofIntegral (V : WeierstrassCurve K) (hV : Integral A V) : AddSubgroup V.toAffine.Point := by
  rw [← hV.model_map]
  exact reductionKernel A hV.model

/-- 元の曲線へ戻しても、還元核は無限遠または極という同じ条件である。 -/
theorem mem_ofIntegral_iff (V : WeierstrassCurve K) (hV : Integral A V) (P : V.toAffine.Point) :
    P ∈ ofIntegral A V hV ↔ PoleOrZero A V P := by
  cases V
  rfl

/-- 整な有限点は還元核に入らない。真の吸収空間を作るための反証点になる。 -/
theorem not_mem_ofIntegral_some (V : WeierstrassCurve K) (hV : Integral A V)
    {x y : K} (h : V.toAffine.Nonsingular x y) (hx : x ∈ A) :
    Point.some x y h ∉ ofIntegral A V hV := by
  rw [mem_ofIntegral_iff, poleOrZero_some_iff]
  exact not_lt_of_ge ((A.valuation_le_one_iff _).mpr hx)

end DkMath.Lib.NumberTheory.EllipticReductionKernel
