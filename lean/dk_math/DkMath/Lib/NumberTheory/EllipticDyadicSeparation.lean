/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from S_FreyPackage_frey_wild_inertia_at_two_trivial.lean,
blob 0131af47435077971efee94c10fe2363fbfa1eb8.
Modified: general coefficient model; reuse DkMath division-polynomial integrality.
-/

import DkMath.Lib.NumberTheory.EllipticTorsionValuationIntegrality

#print "file: DkMath.Lib.NumberTheory.EllipticDyadicSeparation"

/-!
# NOTE-031-003C: 剰余標数2の節点と奇数位数の捩れ点

a₁=1,a₃=a₆=0の整モデルでは、二倍公式と(0,0)との加法から
奇数の単元位数を持つ点にv(a₄)≤v(x)を得る。
単元xの場合は滑らかな還元の差を使う。v(x)<1の場合はy/xを整化し、
xの比が1に合同かつy/xの差が小さければ、差点は無限遠か極を持つ。
しかし単元位数の捩れ点に極はないので、後の章で実際の点の一致が得られる。
ここでは全点群の還元準同型や野生慣性の消滅はまだ主張しない。
-/
namespace DkMath.Lib.NumberTheory.EllipticDyadicSeparation
open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

section ValueGroup

variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]

/-- 1より大きい正の付値は二乗で厳密に増える。 -/
lemma lt_mul_self {a : Γ} (h : 1 < a) : a < a * a := by
  have ha : 0 < a := lt_trans zero_lt_one h
  simpa using mul_lt_mul_of_pos_left h ha

/-- 1より大きい付値の二乗も1より大きい。 -/
lemma one_lt_mul_self {a : Γ} (h : 1 < a) : 1 < a * a :=
  lt_trans h (lt_mul_self h)

/-- 正の因子の乗法は厳密不等式を保つ。 -/
lemma mul_lt_mul_right_pos {a b c : Γ} (h : a < b) (hc : 0 < c) : a * c < b * c := by
  simpa only [mul_comm] using mul_lt_mul_of_pos_left h hc

/-- 乗法の厳密不等式から共通因子を除く。 -/
lemma lt_of_mul_lt_mul_right_pos {a b c : Γ} (h : a * c < b * c) : a < b := by
  rw [mul_comm a, mul_comm b] at h
  exact lt_of_mul_lt_mul_left h zero_le

/-- 正の共通因子を付値の弱不等式から除く。 -/
lemma le_of_mul_le_mul_right_pos {a b c : Γ} (h : a * c ≤ b * c) (hc : 0 < c) : a ≤ b := by
  rw [mul_comm a, mul_comm b] at h
  exact le_of_mul_le_mul_left h hc

end ValueGroup

section Model

variable {K : Type*} [Field K] (A : ValuationSubring K) {W : WeierstrassCurve K}

/-- 曲線の五係数が同じ付値環に入る条件。 -/
structure Integral (A : ValuationSubring K) (W : WeierstrassCurve K) : Prop where
  mem₁ : W.a₁ ∈ A
  mem₂ : W.a₂ ∈ A
  mem₃ : W.a₃ ∈ A
  mem₄ : W.a₄ ∈ A
  mem₆ : W.a₆ ∈ A

variable {A}

/-- 係数の整性を付値の上界1へ翻訳する。 -/
lemma Integral.a₁ (hW : Integral A W) : A.valuation W.a₁ ≤ 1 := (A.valuation_le_one_iff _).mpr hW.mem₁
/-- 係数の整性を付値の上界1へ翻訳する。 -/
lemma Integral.a₂ (hW : Integral A W) : A.valuation W.a₂ ≤ 1 := (A.valuation_le_one_iff _).mpr hW.mem₂
/-- 係数の整性を付値の上界1へ翻訳する。 -/
lemma Integral.a₃ (hW : Integral A W) : A.valuation W.a₃ ≤ 1 := (A.valuation_le_one_iff _).mpr hW.mem₃
/-- 係数の整性を付値の上界1へ翻訳する。 -/
lemma Integral.a₄ (hW : Integral A W) : A.valuation W.a₄ ≤ 1 := (A.valuation_le_one_iff _).mpr hW.mem₄
/-- 係数の整性を付値の上界1へ翻訳する。 -/
lemma Integral.a₆ (hW : Integral A W) : A.valuation W.a₆ ≤ 1 := (A.valuation_le_one_iff _).mpr hW.mem₆

/-- 整モデルの方程式では、xが整ならyも整である。 -/
lemma v_y_le_one (hW : Integral A W) {x y : K} (h : W.toAffine.Equation x y)
    (hx : A.valuation x ≤ 1) : A.valuation y ≤ 1 := by
  by_contra hy
  rw [not_le] at hy
  rw [equation_iff] at h
  have hR : A.valuation (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) ≤ 1 := by
    refine Valuation.map_add_le _ (Valuation.map_add_le _ (Valuation.map_add_le _ ?_ ?_) ?_) hW.a₆
    · rw [map_pow]; exact pow_le_one₀ zero_le hx
    · rw [map_mul, map_pow]; exact mul_le_one' hW.a₂ (pow_le_one₀ zero_le hx)
    · rw [map_mul]; exact mul_le_one' hW.a₄ hx
  have hL : A.valuation (y ^ 2 + W.a₁ * x * y + W.a₃ * y) = A.valuation y ^ 2 := by
    have h1 : A.valuation (W.a₁ * x * y + W.a₃ * y) < A.valuation (y ^ 2) := by
      rw [map_pow, sq]
      refine Valuation.map_add_lt _ ?_ ?_
      · rw [map_mul, map_mul]
        calc A.valuation W.a₁ * A.valuation x * A.valuation y
            ≤ 1 * 1 * A.valuation y := by gcongr; exact hW.a₁
          _ = A.valuation y := by rw [one_mul, one_mul]
          _ < A.valuation y * A.valuation y := lt_mul_self hy
      · rw [map_mul]
        calc A.valuation W.a₃ * A.valuation y ≤ 1 * A.valuation y := by gcongr; exact hW.a₃
          _ = A.valuation y := one_mul _
          _ < A.valuation y * A.valuation y := lt_mul_self hy
    rw [add_assoc, Valuation.map_add_eq_of_lt_left _ h1, map_pow]
  have : A.valuation y ^ 2 ≤ 1 := by rw [← hL, h]; exact hR
  have h2 : (1 : A.ValueGroup) < A.valuation y ^ 2 := by rw [sq]; exact one_lt_mul_self hy
  exact absurd this (not_le.mpr h2)

/-- xに極がある点ではy²とx³の付値が等しく、yの極はさらに大きい。 -/
lemma v_pole (hW : Integral A W) {x y : K} (h : W.toAffine.Equation x y)
    (hx : 1 < A.valuation x) :
    A.valuation y ^ 2 = A.valuation x ^ 3 ∧ A.valuation x < A.valuation y := by
  rw [equation_iff] at h
  have hx0 : 0 < A.valuation x := lt_trans zero_lt_one hx
  have hx1 : A.valuation x < A.valuation x ^ 2 := by rw [sq]; exact lt_mul_self hx
  have hx2 : A.valuation x ^ 2 < A.valuation x ^ 3 := by
    have := mul_lt_mul_of_pos_left hx (pow_pos hx0 2)
    rw [mul_one] at this
    rw [pow_succ]
    exact this
  have hR : A.valuation (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) = A.valuation x ^ 3 := by
    have hlow : A.valuation (W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) < A.valuation (x ^ 3) := by
      rw [map_pow]
      refine Valuation.map_add_lt _ (Valuation.map_add_lt _ ?_ ?_) ?_
      · rw [map_mul, map_pow]
        calc A.valuation W.a₂ * A.valuation x ^ 2 ≤ 1 * A.valuation x ^ 2 := by
              gcongr; exact hW.a₂
          _ = A.valuation x ^ 2 := one_mul _
          _ < A.valuation x ^ 3 := hx2
      · rw [map_mul]
        calc A.valuation W.a₄ * A.valuation x ≤ 1 * A.valuation x := by gcongr; exact hW.a₄
          _ = A.valuation x := one_mul _
          _ < A.valuation x ^ 3 := lt_trans hx1 hx2
      · exact lt_of_le_of_lt hW.a₆ (lt_trans hx (lt_trans hx1 hx2))
    have : x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ = x ^ 3 + (W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) := by
      ring
    rw [this, Valuation.map_add_eq_of_lt_left _ hlow, map_pow]
  have hlin : A.valuation (W.a₁ * x + W.a₃) ≤ A.valuation x := by
    refine Valuation.map_add_le _ ?_ (le_trans hW.a₃ (le_of_lt hx))
    rw [map_mul]
    calc A.valuation W.a₁ * A.valuation x ≤ 1 * A.valuation x := by gcongr; exact hW.a₁
      _ = A.valuation x := one_mul _
  have hfac : y ^ 2 + W.a₁ * x * y + W.a₃ * y = y * (y + (W.a₁ * x + W.a₃)) := by ring
  have hxy : A.valuation x < A.valuation y := by
    by_contra hle
    rw [not_lt] at hle
    have : A.valuation (y ^ 2 + W.a₁ * x * y + W.a₃ * y) ≤ A.valuation x ^ 2 := by
      rw [hfac, map_mul, sq]
      exact mul_le_mul' hle (Valuation.map_add_le _ hle hlin)
    rw [h, hR] at this
    exact absurd this (not_le.mpr hx2)
  refine ⟨?_, hxy⟩
  have hsum : A.valuation (y + (W.a₁ * x + W.a₃)) = A.valuation y :=
    Valuation.map_add_eq_of_lt_left _ (lt_of_le_of_lt hlin hxy)
  have : A.valuation (y ^ 2 + W.a₁ * x * y + W.a₃ * y) = A.valuation y ^ 2 := by
    rw [hfac, map_mul, hsum, sq]
  rw [← this, h, hR]

/-- 整座標の二点で傾きに極があれば、和のxにも極がある。 -/
lemma v_addX_of_slope (hW : Integral A W) {x₁ x₂ L : K} (h₁ : A.valuation x₁ ≤ 1)
    (h₂ : A.valuation x₂ ≤ 1) (hL : 1 < A.valuation L) :
    1 < A.valuation (W.toAffine.addX x₁ x₂ L) := by
  have hL2 : A.valuation L < A.valuation L ^ 2 := by rw [sq]; exact lt_mul_self hL
  have hlow : A.valuation (W.a₁ * L - W.a₂ - x₁ - x₂) < A.valuation (L ^ 2) := by
    rw [map_pow]
    have h1L2 : (1 : A.ValueGroup) < A.valuation L ^ 2 := lt_trans hL hL2
    refine Valuation.map_sub_lt _ (Valuation.map_sub_lt _ (Valuation.map_sub_lt _ ?_ ?_) ?_) ?_
    · rw [map_mul]
      calc A.valuation W.a₁ * A.valuation L ≤ 1 * A.valuation L := by gcongr; exact hW.a₁
        _ = A.valuation L := one_mul _
        _ < A.valuation L ^ 2 := hL2
    · exact lt_of_le_of_lt hW.a₂ h1L2
    · exact lt_of_le_of_lt h₁ h1L2
    · exact lt_of_le_of_lt h₂ h1L2
  have : W.toAffine.addX x₁ x₂ L = L ^ 2 + (W.a₁ * L - W.a₂ - x₁ - x₂) := by
    rw [addX]; ring
  rw [this, Valuation.map_add_eq_of_lt_left _ hlow, map_pow]
  exact lt_trans hL hL2

/-- 2が非単元なら3は付値1の単元となる。 -/
lemma v_three (h2 : A.valuation (2 : K) < 1) : A.valuation (3 : K) = 1 := by
  have : (3 : K) = 1 + 2 := by norm_num
  rw [this, Valuation.map_add_eq_of_lt_left _ (by rwa [Valuation.map_one]), Valuation.map_one]

/-- 剰余標数2の整モデルで極を持つ点の二倍も極を持つ。 -/
lemma v_addX_double [DecidableEq K] (hW : Integral A W) (h2 : A.valuation (2 : K) < 1) {x y : K}
    (h : W.toAffine.Equation x y) (hx : 1 < A.valuation x) (hy : y ≠ W.toAffine.negY x y) :
    1 < A.valuation (W.toAffine.addX x x (W.toAffine.slope x x y y)) := by
  obtain ⟨hY2, hxy⟩ := v_pole hW h hx
  have hX0 : 0 < A.valuation x := lt_trans zero_lt_one hx
  have hY0 : 0 < A.valuation y := lt_trans hX0 hxy
  have hx1 : A.valuation x < A.valuation x ^ 2 := by rw [sq]; exact lt_mul_self hx
  have hYX2 : A.valuation y < A.valuation x ^ 2 := by
    apply lt_of_pow_lt_pow_left₀ 2 zero_le
    rw [hY2, ← pow_mul]
    exact pow_lt_pow_right₀ hx (by norm_num)
  rw [slope_of_Y_ne rfl hy]
  have hD : y - W.toAffine.negY x y = 2 * y + (W.a₁ * x + W.a₃) := by rw [negY]; ring
  have hD0 : y - W.toAffine.negY x y ≠ 0 := sub_ne_zero.mpr hy
  have hvD0 : 0 < A.valuation (y - W.toAffine.negY x y) :=
    zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hD0)
  have hlin : A.valuation (W.a₁ * x + W.a₃) ≤ A.valuation x := by
    refine Valuation.map_add_le _ ?_ (le_trans hW.a₃ (le_of_lt hx))
    rw [map_mul]
    calc A.valuation W.a₁ * A.valuation x ≤ 1 * A.valuation x := by gcongr; exact hW.a₁
      _ = A.valuation x := one_mul _
  have hDle : A.valuation (y - W.toAffine.negY x y) ≤
      max (A.valuation (2 : K) * A.valuation y) (A.valuation x) := by
    rw [hD]
    refine le_trans (Valuation.map_add _ _ _) (max_le_max (by rw [map_mul]) hlin)
  have hN : A.valuation (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) = A.valuation x ^ 2 := by
    have hmain : A.valuation (3 * x ^ 2) = A.valuation x ^ 2 := by
      rw [map_mul, v_three h2, one_mul, map_pow]
    have hlow : A.valuation (2 * W.a₂ * x + W.a₄ - W.a₁ * y) < A.valuation (3 * x ^ 2) := by
      rw [hmain]
      refine Valuation.map_sub_lt _ (Valuation.map_add_lt _ ?_ ?_) ?_
      · rw [map_mul, map_mul]
        calc A.valuation (2 : K) * A.valuation W.a₂ * A.valuation x
            ≤ A.valuation (2 : K) * 1 * A.valuation x := by gcongr; exact hW.a₂
          _ < 1 * 1 * A.valuation x := by
              rw [mul_one, mul_one]; exact mul_lt_mul_right_pos h2 hX0
          _ = A.valuation x := by rw [one_mul, one_mul]
          _ < A.valuation x ^ 2 := hx1
      · exact lt_of_le_of_lt hW.a₄ (lt_trans hx hx1)
      · rw [map_mul]
        calc A.valuation W.a₁ * A.valuation y ≤ 1 * A.valuation y := by gcongr; exact hW.a₁
          _ = A.valuation y := one_mul _
          _ < A.valuation x ^ 2 := hYX2
    have : 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y = 3 * x ^ 2 + (2 * W.a₂ * x + W.a₄ - W.a₁ * y) := by
      ring
    rw [this, Valuation.map_add_eq_of_lt_left _ hlow, hmain]
  have hDlt : A.valuation (y - W.toAffine.negY x y) < A.valuation x ^ 2 := by
    refine lt_of_le_of_lt hDle (max_lt ?_ hx1)
    calc A.valuation (2 : K) * A.valuation y < 1 * A.valuation y := mul_lt_mul_right_pos h2 hY0
      _ = A.valuation y := one_mul _
      _ < A.valuation x ^ 2 := hYX2
  set L := (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) / (y - W.toAffine.negY x y) with hLdef
  have hvL : A.valuation L * A.valuation (y - W.toAffine.negY x y) = A.valuation x ^ 2 := by
    rw [← map_mul, hLdef, div_mul_cancel₀ _ hD0, hN]
  have hL : 1 < A.valuation L := by
    apply lt_of_mul_lt_mul_right_pos (c := A.valuation (y - W.toAffine.negY x y))
    rw [one_mul, hvL]
    exact hDlt
  have hB : A.valuation (2 : K) * A.valuation x < A.valuation L ^ 2 := by
    apply lt_of_mul_lt_mul_right_pos (c := A.valuation (y - W.toAffine.negY x y) ^ 2)
    rw [← mul_pow, hvL]
    calc A.valuation (2 : K) * A.valuation x * A.valuation (y - W.toAffine.negY x y) ^ 2
        ≤ A.valuation (2 : K) * A.valuation x *
            (max (A.valuation (2 : K) * A.valuation y) (A.valuation x)) ^ 2 := by gcongr
      _ < (A.valuation x ^ 2) ^ 2 := by
          rcases le_total (A.valuation (2 : K) * A.valuation y) (A.valuation x) with hc | hc
          · rw [max_eq_right hc]
            have : A.valuation (2 : K) * A.valuation x * A.valuation x ^ 2 =
                A.valuation (2 : K) * A.valuation x ^ 3 := by
              simp only [pow_succ, pow_zero, one_mul, mul_comm, mul_left_comm]
            rw [this, show (A.valuation x ^ 2) ^ 2 = A.valuation x * A.valuation x ^ 3 by
              simp only [pow_succ, pow_zero, one_mul, mul_comm, mul_left_comm]]
            exact mul_lt_mul_right_pos (lt_trans h2 hx) (pow_pos hX0 3)
          · rw [max_eq_left hc]
            have : A.valuation (2 : K) * A.valuation x * (A.valuation (2 : K) * A.valuation y) ^ 2 =
                A.valuation (2 : K) ^ 3 * (A.valuation x * A.valuation y ^ 2) := by
              simp only [pow_succ, pow_zero, one_mul, mul_comm, mul_left_comm]
            rw [this, hY2, show A.valuation x * A.valuation x ^ 3 = (A.valuation x ^ 2) ^ 2 by
              simp only [pow_succ, pow_zero, one_mul, mul_comm, mul_left_comm]]
            calc A.valuation (2 : K) ^ 3 * (A.valuation x ^ 2) ^ 2
                < 1 * (A.valuation x ^ 2) ^ 2 :=
                  mul_lt_mul_right_pos (pow_lt_one₀ zero_le h2 (by norm_num))
                    (pow_pos (pow_pos hX0 2) 2)
              _ = (A.valuation x ^ 2) ^ 2 := one_mul _
  have hL2 : A.valuation L < A.valuation L ^ 2 := by rw [sq]; exact lt_mul_self hL
  have hlow : A.valuation (W.a₁ * L - W.a₂ - 2 * x) < A.valuation (L ^ 2) := by
    rw [map_pow]
    refine Valuation.map_sub_lt _ (Valuation.map_sub_lt _ ?_ ?_) ?_
    · rw [map_mul]
      calc A.valuation W.a₁ * A.valuation L ≤ 1 * A.valuation L := by gcongr; exact hW.a₁
        _ = A.valuation L := one_mul _
        _ < A.valuation L ^ 2 := hL2
    · exact lt_of_le_of_lt hW.a₂ (lt_trans hL hL2)
    · rw [map_mul]; exact hB
  have : W.toAffine.addX x x L = L ^ 2 + (W.a₁ * L - W.a₂ - 2 * x) := by rw [addX]; ring
  rw [this, Valuation.map_add_eq_of_lt_left _ hlow, map_pow]
  exact lt_trans hL hL2

/-- a₃=a₆=0の曲線で(0,0)との和のx座標はa₄/xである。 -/
lemma addX_T0 [DecidableEq K] (ha₃ : W.a₃ = 0) (ha₆ : W.a₆ = 0) {x y : K}
    (h : W.toAffine.Equation x y) (hx : x ≠ 0) :
    W.toAffine.addX x 0 (W.toAffine.slope x 0 y 0) = W.a₄ / x := by
  rw [slope_of_X_ne hx, addX, sub_zero, sub_zero, sub_zero]
  rw [equation_iff, ha₃, ha₆] at h
  field_simp
  linear_combination h

variable [DecidableEq K]

variable (A W) in
/-- 無限遠点か、有限ならx座標に極を持つという二択。 -/
def PoleOrZero (P : W.toAffine.Point) : Prop :=
  ∀ x y (h : W.toAffine.Nonsingular x y), P = .some x y h → 1 < A.valuation x

omit [DecidableEq K] in
/-- 無限遠点は極または零の条件を満たす。 -/
lemma poleOrZero_zero : PoleOrZero A W 0 := fun _ _ h heq => absurd heq.symm (some_ne_zero h)

omit [DecidableEq K] in
/-- 有限点では条件はx座標の付値が1を超えることに等しい。 -/
lemma poleOrZero_some_iff {x y : K} {h : W.toAffine.Nonsingular x y} :
    PoleOrZero A W (.some x y h) ↔ 1 < A.valuation x := by
  refine ⟨fun H => H x y h rfl, fun H x' y' h' heq => ?_⟩
  obtain ⟨rfl, -⟩ := some.inj heq
  exact H

/-- 剰余標数2では極または零の条件は二倍で保存される。 -/
lemma poleOrZero_double (hW : Integral A W) (h2 : A.valuation (2 : K) < 1) {P : W.toAffine.Point}
    (hP : PoleOrZero A W P) : PoleOrZero A W (P + P) := by
  rcases P with _ | ⟨x, y, h⟩
  · rw [← zero_def, add_zero]; exact poleOrZero_zero
  · by_cases hy : y = W.toAffine.negY x y
    · rw [add_self_of_Y_eq hy]; exact poleOrZero_zero
    · rw [add_self_of_Y_ne hy, poleOrZero_some_iff]
      exact v_addX_double hW h2 h.left (poleOrZero_some_iff.mp hP) hy

/-- v(x)<v(a₄)なら(0,0)との和は極または零となる。 -/
lemma poleOrZero_add_T0 (ha₃ : W.a₃ = 0) (ha₆ : W.a₆ = 0) {x y : K}
    {h : W.toAffine.Nonsingular x y} (h₀ : W.toAffine.Nonsingular 0 0)
    (hx : A.valuation x < A.valuation W.a₄) :
    PoleOrZero A W (.some x y h + .some 0 0 h₀) := by
  by_cases hx0 : x = 0
  · subst hx0
    have hy : y = 0 := by
      have he := h.left
      rw [equation_iff, ha₃, ha₆] at he
      have : y ^ 2 = 0 := by linear_combination he
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    subst hy
    rw [add_of_Y_eq rfl (by rw [negY, ha₃]; ring)]
    exact poleOrZero_zero
  · rw [add_of_X_ne hx0, poleOrZero_some_iff, addX_T0 ha₃ ha₆ h.left hx0, map_div₀,
      lt_div_iff₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hx0)), one_mul]
    exact hx

/-- 係数ごとの整性を同じ曲線の付値環モデルへまとめる。 -/
noncomputable def Integral.model (hW : Integral A W) : WeierstrassCurve A :=
  ⟨⟨W.a₁, hW.mem₁⟩, ⟨W.a₂, hW.mem₂⟩, ⟨W.a₃, hW.mem₃⟩,
    ⟨W.a₄, hW.mem₄⟩, ⟨W.a₆, hW.mem₆⟩⟩

omit [DecidableEq K] in
/-- 整性から作るモデルは元の曲線へ厳密に戻る。 -/
lemma Integral.model_map (hW : Integral A W) : hW.model.map A.subtype = W := by
  cases W
  rfl

/-- 奇数位数の捩れ点の整性を既存の除法多項式の証明から供給する。 -/
lemma torsion_x_mem [CharZero K] (hW : Integral A W) {n : ℕ}
    (hnA : (n : K) ∉ A.nonunits) {x y : K} (h : W.toAffine.Nonsingular x y)
    (hP : n • Point.some x y h = 0) : x ∈ A := by
  have hn : A.valuation (n : K) = 1 := by
    apply le_antisymm ((A.valuation_le_one_iff _).mpr (natCast_mem A n))
    exact le_of_not_gt (fun h => hnA ((A.mem_nonunits_iff).mpr h))
  exact EllipticTorsionValuationIntegrality.torsion_x_mem A hW.model W hW.model_map hn h hP

/-- 単元位数の捩れ点は整であるため、極または零なら零である。 -/
lemma eq_zero_of_poleOrZero [CharZero K] [W.IsElliptic] (hW : Integral A W) {n : ℕ} (_hn : Odd n)
    (hnA : (n : K) ∉ A.nonunits) {P : W.toAffine.Point} (hP : n • P = 0)
    (hpole : PoleOrZero A W P) : P = 0 := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · exfalso
    have hx : x ∈ A := torsion_x_mem hW hnA h hP
    exact absurd ((A.valuation_le_one_iff x).mpr hx) (not_le.mpr (poleOrZero_some_iff.mp hpole))

/-- 奇数単元位数の非無限遠点はv(a₄)≤v(x)を満たす。二倍して2捩れ点を消す。 -/
lemma v_a₄_le_of_torsion [CharZero K] [W.IsElliptic] (hW : Integral A W) (ha₃ : W.a₃ = 0) (ha₆ : W.a₆ = 0)
    (ha₄ : W.a₄ ≠ 0) (h2 : A.valuation (2 : K) < 1) {n : ℕ} (hn : Odd n)
    (hnA : (n : K) ∉ A.nonunits) {x y : K} {h : W.toAffine.Nonsingular x y}
    (hP : n • Point.some x y h = 0) : A.valuation W.a₄ ≤ A.valuation x := by
  by_contra hlt
  rw [not_le] at hlt
  have h₀ : W.toAffine.Nonsingular 0 0 := by rw [nonsingular_zero]; exact ⟨ha₆, Or.inr ha₄⟩
  have hT : Point.some 0 0 h₀ + Point.some 0 0 h₀ = 0 :=
    add_self_of_Y_eq (by rw [negY, ha₃]; ring)
  have hS : PoleOrZero A W (Point.some x y h + Point.some 0 0 h₀) := poleOrZero_add_T0 ha₃ ha₆ h₀ hlt
  have hSS := poleOrZero_double hW h2 hS
  rw [add_add_add_comm, hT, add_zero] at hSS
  have hn2 : n • (Point.some x y h + Point.some x y h) = 0 := by rw [smul_add, hP, add_zero]
  have hRR0 : Point.some x y h + Point.some x y h = 0 := eq_zero_of_poleOrZero hW hn hnA hn2 hSS
  obtain ⟨k, rfl⟩ := hn
  have : Point.some x y h = 0 := by
    have e : (2 * k + 1) • Point.some x y h = k • (Point.some x y h + Point.some x y h) +
        Point.some x y h := by
      rw [add_smul, one_smul, mul_comm, mul_smul, two_smul]
    rw [e, hRR0, smul_zero, zero_add] at hP
    exact hP
  exact absurd this (some_ne_zero h)

omit [DecidableEq K] in
/-- xが単元なら、2y+xも単元である。 -/
lemma v_two_y_add_x (hW : Integral A W)
    (h2 : A.valuation (2 : K) < 1) {x y : K} (h : W.toAffine.Equation x y)
    (hx : A.valuation x = 1) : A.valuation (2 * y + x) = 1 := by
  have hy : A.valuation y ≤ 1 := v_y_le_one hW h (le_of_eq hx)
  have : A.valuation (2 * y) < A.valuation x := by
    rw [map_mul, hx]
    calc A.valuation (2 : K) * A.valuation y ≤ A.valuation (2 : K) * 1 := by gcongr
      _ < 1 := by rw [mul_one]; exact h2
  rw [Valuation.map_add_eq_of_lt_right _ this, hx]

/-- 単元xを持ち剰余座標が一致する二点の差は極または零である。 -/
lemma poleOrZero_sub_of_unit (hW : Integral A W) (ha₁ : W.a₁ = 1) (ha₃ : W.a₃ = 0)
    (h2 : A.valuation (2 : K) < 1) {x y x' y' : K} {h : W.toAffine.Nonsingular x y}
    {h' : W.toAffine.Nonsingular x' y'} (hx : A.valuation x = 1)
    (hxx : A.valuation (x' - x) < 1) (hyy : A.valuation (y' - y) < 1) :
    PoleOrZero A W (.some x' y' h' - .some x y h) := by
  rw [sub_eq_add_neg, neg_some]
  have hneg : W.toAffine.negY x y = -y - x := by rw [negY, ha₁, ha₃]; ring
  by_cases hxe : x' = x
  · rcases (X_eq_iff (h₁ := h') (h₂ := h)).mp hxe with heq | heq
    · rw [← neg_some h, heq, add_neg_cancel]; exact poleOrZero_zero
    · exfalso
      rw [neg_some] at heq
      obtain ⟨-, hy'⟩ := some.inj heq
      rw [hy', hneg] at hyy
      have : -y - x - y = -(2 * y + x) := by ring
      rw [this, Valuation.map_neg, v_two_y_add_x hW h2 h.left hx] at hyy
      exact lt_irrefl _ hyy
  · rw [add_of_X_ne hxe, poleOrZero_some_iff]
    have hx' : A.valuation x' ≤ 1 := by
      have : x' = x + (x' - x) := by ring
      rw [this, Valuation.map_add_eq_of_lt_left _ (by rwa [hx]), hx]
    refine v_addX_of_slope hW hx' (le_of_eq hx) ?_
    rw [slope_of_X_ne hxe, hneg, map_div₀]
    have hnum : A.valuation (y' - (-y - x)) = 1 := by
      have : y' - (-y - x) = (2 * y + x) + (y' - y) := by ring
      rw [this, Valuation.map_add_eq_of_lt_left _ (by rwa [v_two_y_add_x hW h2 h.left hx]),
        v_two_y_add_x hW h2 h.left hx]
    rw [hnum, lt_div_iff₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr (sub_ne_zero.mpr hxe))),
      one_mul]
    exact hxx

omit [DecidableEq K] in
/-- 節点側の捩れ点の下界v(a₄)≤v(x)から比y/xの整性を得る。 -/
lemma v_ratio_le_one (hW : Integral A W) (ha₁ : W.a₁ = 1) (ha₃ : W.a₃ = 0) (ha₆ : W.a₆ = 0)
    {x y : K} (h : W.toAffine.Equation x y) (hxa : A.valuation W.a₄ ≤ A.valuation x)
    (hx1 : A.valuation x < 1) (hx0 : x ≠ 0) : A.valuation (y * x⁻¹) ≤ 1 := by
  have hvx0 : 0 < A.valuation x := zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hx0)
  rw [equation_iff, ha₁, ha₃, ha₆] at h
  have hss : (y * x⁻¹) ^ 2 + y * x⁻¹ = x + W.a₂ + W.a₄ * x⁻¹ := by
    field_simp; linear_combination h
  by_contra hlt
  rw [not_le] at hlt
  have hl : A.valuation ((y * x⁻¹) ^ 2 + y * x⁻¹) = A.valuation (y * x⁻¹) ^ 2 := by
    rw [Valuation.map_add_eq_of_lt_left _ (by rw [map_pow, sq]; exact lt_mul_self hlt), map_pow]
  have hr : A.valuation (x + W.a₂ + W.a₄ * x⁻¹) ≤ 1 := by
    refine Valuation.map_add_le _ (Valuation.map_add_le _ (le_of_lt hx1) hW.a₂) ?_
    rw [map_mul, map_inv₀]
    calc A.valuation W.a₄ * (A.valuation x)⁻¹ ≤ A.valuation x * (A.valuation x)⁻¹ := by gcongr
      _ = 1 := mul_inv_cancel₀ (ne_of_gt hvx0)
  rw [← hss, hl] at hr
  have : (1 : A.ValueGroup) < A.valuation (y * x⁻¹) ^ 2 := by rw [sq]; exact one_lt_mul_self hlt
  exact absurd hr (not_le.mpr this)

/-- 節点側でxの乗法的合同とy/xの加法的合同から、差点が極または零とわかる。 -/
lemma poleOrZero_sub_of_node (hW : Integral A W) (ha₁ : W.a₁ = 1) (ha₃ : W.a₃ = 0)
    (ha₆ : W.a₆ = 0) (h2 : A.valuation (2 : K) < 1) {x y x' y' : K}
    {h : W.toAffine.Nonsingular x y} {h' : W.toAffine.Nonsingular x' y'}
    (hxa : A.valuation W.a₄ ≤ A.valuation x) (hx1 : A.valuation x < 1) (hx0 : x ≠ 0)
    (hw : A.valuation (x' * x⁻¹ - 1) < 1) (hs : A.valuation (y' * x'⁻¹ - y * x⁻¹) < 1) :
    PoleOrZero A W (.some x' y' h' - .some x y h) := by
  rw [sub_eq_add_neg, neg_some]
  have hneg : W.toAffine.negY x y = -y - x := by rw [negY, ha₁, ha₃]; ring
  set s := y * x⁻¹ with hsdef
  set w := x' * x⁻¹ with hwdef
  set s' := y' * x'⁻¹ with hs'def
  have hvx0 : 0 < A.valuation x := zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hx0)
  have hys : y = x * s := by rw [hsdef]; field_simp
  have hvw : A.valuation w = 1 := by
    have : w = 1 + (w - 1) := by ring
    rw [this, Valuation.map_add_eq_of_lt_left _ (by rwa [Valuation.map_one]), Valuation.map_one]
  have hw0 : w ≠ 0 := (Valuation.ne_zero_iff _).mp (by rw [hvw]; exact one_ne_zero)
  have hx'e : x' = x * w := by rw [hwdef]; field_simp
  have hx'0 : x' ≠ 0 := by rw [hx'e]; exact mul_ne_zero hx0 hw0
  have hvx' : A.valuation x' = A.valuation x := by rw [hx'e, map_mul, hvw, mul_one]
  have hys' : y' = x * w * s' := by rw [hs'def, ← hx'e]; field_simp
  have hvs : A.valuation s ≤ 1 := v_ratio_le_one hW ha₁ ha₃ ha₆ h.left hxa hx1 hx0
  have h2s1 : A.valuation (2 * s + 1) = 1 := by
    have : A.valuation (2 * s) < A.valuation (1 : K) := by
      rw [map_mul, Valuation.map_one]
      calc A.valuation (2 : K) * A.valuation s ≤ A.valuation (2 : K) * 1 := by gcongr
        _ < 1 := by rw [mul_one]; exact h2
    rw [Valuation.map_add_eq_of_lt_right _ this, Valuation.map_one]
  by_cases hxe : x' = x
  · rcases (X_eq_iff (h₁ := h') (h₂ := h)).mp hxe with heq | heq
    · rw [← neg_some h, heq, add_neg_cancel]; exact poleOrZero_zero
    · exfalso
      rw [neg_some] at heq
      obtain ⟨-, hy'⟩ := some.inj heq
      have : s' - s = -(2 * s + 1) := by
        rw [hs'def, hsdef, hy', hneg, hxe]; field_simp; ring
      rw [this, Valuation.map_neg, h2s1] at hs
      exact lt_irrefl _ hs
  · rw [add_of_X_ne hxe, poleOrZero_some_iff]
    refine v_addX_of_slope hW (by rw [hvx']; exact le_of_lt hx1) (le_of_lt hx1) ?_
    rw [slope_of_X_ne hxe, hneg]
    have hw1 : w - 1 ≠ 0 := by
      intro hw1
      apply hxe
      rw [hx'e, show w = 1 from sub_eq_zero.mp hw1, mul_one]
    have hL : (y' - (-y - x)) / (x' - x) = (w * s' + s + 1) / (w - 1) := by
      rw [hys', hys, hx'e]
      have : x * w - x = x * (w - 1) := by ring
      rw [this]
      field_simp
      ring
    rw [hL, map_div₀]
    have hnum : A.valuation (w * s' + s + 1) = 1 := by
      have : w * s' + s + 1 = (2 * s + 1) + (w * (s' - s) + (w - 1) * s) := by ring
      rw [this, Valuation.map_add_eq_of_lt_left _ ?_, h2s1]
      rw [h2s1]
      refine Valuation.map_add_lt _ ?_ ?_
      · rw [map_mul, hvw, one_mul]; exact hs
      · rw [map_mul]
        calc A.valuation (w - 1) * A.valuation s ≤ A.valuation (w - 1) * 1 := by gcongr
          _ < 1 := by rw [mul_one]; exact hw
    rw [hnum, lt_div_iff₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hw1)), one_mul]
    exact hw

end Model


end DkMath.Lib.NumberTheory.EllipticDyadicSeparation
