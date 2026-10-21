/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from anthropics/fermats-last-theorem,
P2M/Sol/S_FreyPackage_freyCurve_rational_p_torsion_eq_zero.lean, frey_deep_of_order.
Upstream blob: fe61fd5d4f94d55b5a9da38d1541903c84397df0
Modified for DkMath: separate coefficient parity, local unit-coordinate formulas,
and the finite-order argument; reuse the proved nonnegative orbit theorem.
-/

import DkMath.Lib.NumberTheory.WeierstrassTorsionValuation

#print "file: DkMath.Lib.NumberTheory.WeierstrassPositiveValuation"

/-!
# NOTE-030-004: 付値0の排除は2Qと3Qの座標で行う

前章の非負下界から正の下界へ進むには、xが2進単元である場合を排除する。
a₂が深さ1以上なら曲線方程式を法2で読むだけで矛盾する。
a₂が単元なら倍点のxも単元となり、x(2Q)≠x(Q)の場合に3Qのx付値が負となる。
この負付値は前章の有限軌道の定理に反する。

等しいx座標の例外は群法で処理する。2Q=QならQ=0、2Q=−Qなら3Q=0であり、
位数p≥5には両方とも起きない。従ってp=3の既存の単元x座標の例を誤って排除しない。
局所の座標補題には有限位数を仮定せず、曲線と座標の条件を明示する。
-/
namespace DkMath.Lib.NumberTheory.WeierstrassPositiveValuation
open WeierstrassCurve WeierstrassCurve.Affine
open RationalTwoAdicBounds WeierstrassNegativeValuation WeierstrassTorsionValuation
local notation "v" => padicValRat 2
variable {W : Affine ℚ}

/-- a₂,a₄がともに深さ1以上なら、整なyを持つ有限点のxは単元ではない。
左辺y(y+x)は深さ1以上、右辺は単元x³が最低項となるため矛盾する。 -/
theorem not_unit_x_of_even_a₂ (h₁ : W.a₁ = 1) (h₃ : W.a₃ = 0) (h₆ : W.a₆ = 0)
    (ha₂ : Lower 1 W.a₂) (ha₄ : Lower 1 W.a₄)
    {x y : ℚ} (h : W.Nonsingular x y) (hy : Lower 0 y) : ¬ Exact 0 x := by
  intro hx
  have hL : Lower 1 (y ^ 2 + x * y) := by
    by_cases hyu : Exact 0 y
    · rw [show y ^ 2 + x * y = y * (y + x) by ring]
      simpa using hyu.lower.mul (lower_one_add_of_units hyu hx)
    · have hy1 : Lower 1 y := by
        by_cases hy0 : y = 0
        · exact Or.inl hy0
        · have hv0 : v y ≠ 0 := fun hv => hyu ⟨hy0, hv⟩
          exact Or.inr (by have := hy.le_valuation hy0; omega)
      exact hy1.square.mono (by norm_num) |>.add
        (by simpa using hx.lower.mul hy1)
  have hR : Exact 0 (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x) := by
    have h3 : Exact 0 (x ^ 3) := by simpa using hx.pow 3
    have h2 : Lower 1 (W.a₂ * x ^ 2) := by simpa using ha₂.mul hx.lower.square
    have h1 : Lower 1 (W.a₄ * x) := by simpa using ha₄.mul hx.lower
    exact (h3.add_lower h2 (by norm_num)).add_lower h1 (by norm_num)
  rw [equation_of_normalized h₁ h₃ h₆ h] at hL
  exact hR.not_lower hL (by norm_num)

/-- a₂とxが単元、yが整なら、接線分母は単元、傾きは整、倍点のxも単元となる。
曲線方程式や有限位数を使わない局所計算であり、次の反射段階でも再利用できる。 -/
theorem double_x_unit (h₁ : W.a₁ = 1) (h₃ : W.a₃ = 0)
    (ha₂ : Exact 0 W.a₂) (ha₄ : Lower 1 W.a₄) {x y : ℚ}
    (hx : Exact 0 x) (hy : Lower 0 y) :
    y ≠ W.negY x y ∧ Lower 0 (W.slope x x y y) ∧
      Exact 0 (W.addX x x (W.slope x x y y)) := by
  have hD : y - W.negY x y = x + 2 * y := by
    rw [negY_of_normalized h₁ h₃]; ring
  have h2y : Lower 1 (2 * y) := by simpa using lower_two.mul hy
  have h2x : Lower 1 (2 * x) := by simpa using lower_two.mul hx.lower
  have hED : Exact 0 (x + 2 * y) := hx.add_lower h2y (by norm_num)
  have hyy : y ≠ W.negY x y := by
    intro heq
    apply hED.1
    rw [← hD]
    exact sub_eq_zero.mpr heq
  have hN : Lower 0 (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) := by
    rw [h₁, one_mul]
    have h1 : Lower 0 (3 * x ^ 2) := by simpa using exact_three.lower.mul hx.lower.square
    have h2 : Lower 1 (2 * W.a₂ * x) := by
      simpa using (lower_two.mul ha₂.lower).mul hx.lower
    exact ((h1.add (h2.mono (by norm_num))).add (ha₄.mono (by norm_num))).sub hy
  have hslope : W.slope x x y y =
      (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) / (x + 2 * y) := by
    rw [slope_of_Y_ne rfl hyy, hD]
  have hℓ : Lower 0 (W.slope x x y y) := by
    rw [hslope]
    simpa using hN.div_exact hED
  refine ⟨hyy, hℓ, ?_⟩
  have hrw : W.addX x x (W.slope x x y y) =
      -W.a₂ + (W.slope x x y y * (W.slope x x y y + 1) - 2 * x) := by
    simp only [addX, h₁]; ring
  rw [hrw]
  exact ha₂.neg.add_lower ((lower_one_mul_add_one hℓ).sub h2x) (by norm_num)

/-- xと倍点のx₂が異なる単元なら、和差の分母は深さ1以上、分子は単元。
従って割線の傾きは負の付値を持ち、三倍点のx付値は−2以下となる。
倍点の座標は同じaddX/addYで計算し、x₂≠xを明示して分母の非零性を保つ。 -/
theorem triple_x_valuation_negative (h₁ : W.a₁ = 1) (h₃ : W.a₃ = 0)
    (ha₂ : Lower 0 W.a₂) {x y ℓ : ℚ} (hx : Exact 0 x) (hy : Lower 0 y)
    (hℓ : Lower 0 ℓ) (hx₂ : Exact 0 (W.addX x x ℓ)) (hne : W.addX x x ℓ ≠ x) :
    W.addX (W.addX x x ℓ) x (W.slope (W.addX x x ℓ) x (W.addY x x y ℓ) y) ≠ 0 ∧
      v (W.addX (W.addX x x ℓ) x (W.slope (W.addX x x ℓ) x (W.addY x x y ℓ) y)) ≤ -2 := by
  let x₂ := W.addX x x ℓ
  let y₂ := W.addY x x y ℓ
  have h2y : Lower 1 (2 * y) := by simpa using lower_two.mul hy
  have hdy : Exact 0 (y₂ - y) := by
    have hrw : y₂ - y = -x₂ + (-(ℓ * (x₂ - x)) - 2 * y) := by
      dsimp only [y₂, x₂]
      simp only [addY, negAddY, negY, addX, h₁, h₃]; ring
    rw [hrw]
    have hℓd : Lower 1 (ℓ * (x₂ - x)) := by
      simpa only [zero_add] using hℓ.mul (lower_one_sub_of_units (show Exact 0 x₂ from hx₂) hx)
    exact hx₂.neg.add_lower (hℓd.neg.sub h2y) (by norm_num)
  have hdx : Exact (v (x₂ - x)) (x₂ - x) := exact_valuation (sub_ne_zero.mpr hne)
  have hdx1 : 1 ≤ v (x₂ - x) :=
    (lower_one_sub_of_units hx₂ hx).le_valuation hdx.1
  let μ := W.slope x₂ x y₂ y
  have hμ : W.slope x₂ x y₂ y = (y₂ - y) / (x₂ - x) := slope_of_X_ne hne
  have hEμ : Exact (0 - v (x₂ - x)) μ := by
    rw [show μ = W.slope x₂ x y₂ y from rfl, hμ]
    exact hdy.div hdx
  let m := (0 : ℤ) - v (x₂ - x)
  have hX : Exact (m + m) (W.addX x₂ x μ) := by
    simp only [addX, h₁, one_mul]
    exact (((hEμ.square.add_lower hEμ.lower (by omega)).sub_lower
      ha₂ (by omega)).sub_lower hx₂.lower (by omega)).sub_lower hx.lower (by omega)
  exact ⟨hX.1, by rw [hX.2]; dsimp only [m]; omega⟩

/-- 位数p≥5の有限点のx付値は1以上である。
a₂の偶奇で分け、単元の場合は2Qの例外を位数で除き、3Qの負付値を既存の非負下界と矛盾させる。 -/
theorem x_positive_of_prime_order (h₁ : W.a₁ = 1) (h₃ : W.a₃ = 0) (h₆ : W.a₆ = 0)
    (ha₂ : Lower 0 W.a₂) (ha₄ : Lower 1 W.a₄)
    (Q : W.Point) (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hQ : addOrderOf Q = p)
    {x y : ℚ} {h : W.Nonsingular x y} (hxy : Q = Point.some x y h) : 1 ≤ v x := by
  have hx0 := x_nonzero_of_addOrder_eq h₁ h₃ h₆ Q p (by omega) hQ hxy
  have hxI : Lower 0 x := by
    have hi := x_integral_of_prime_order h₁ h₃ h₆ ha₂ ha₄ Q p hp (by omega) hQ 1
    rwa [one_nsmul, hxy, Point.xc_some] at hi
  by_contra hlt
  have hx : Exact 0 x := ⟨hx0, by have := hxI.le_valuation hx0; omega⟩
  have hy := y_integral_of_x_integral h₁ h₃ h₆ ha₂ ha₄ h hxI
  by_cases hA2 : Lower 1 W.a₂
  · exact not_unit_x_of_even_a₂ h₁ h₃ h₆ hA2 ha₄ h hy hx
  · have hEA2 : Exact 0 W.a₂ := by
      refine ⟨fun hz => hA2 (Or.inl hz), ?_⟩
      have hi := ha₂.le_valuation (fun hz => hA2 (Or.inl hz))
      have hn : ¬ 1 ≤ v W.a₂ := fun hh => hA2 (Or.inr hh)
      omega
    obtain ⟨hyy, hℓ, hx₂⟩ := double_x_unit h₁ h₃ hEA2 ha₄ hx hy
    let ℓ := W.slope x x y y
    let x₂ := W.addX x x ℓ
    let y₂ := W.addY x x y ℓ
    have hns₂ : W.Nonsingular x₂ y₂ := nonsingular_add h h (fun hxy => hyy hxy.2)
    have h2Q : Q + Q = Point.some x₂ y₂ hns₂ := by rw [hxy, Point.add_self_of_Y_ne hyy]
    have hxx₂ : x₂ ≠ x := by
      intro heq
      rcases (Point.X_eq_iff (h₁ := hns₂) (h₂ := h)).mp heq with he | he
      · have hQQ : Q + Q = Q := by rw [h2Q, he, ← hxy]
        have hz : Q = 0 := by
          have hh := congrArg (· - Q) hQQ
          simpa using hh
        have ho : addOrderOf Q = 1 := by rw [hz]; simp
        omega
      · have h3 : (3 : ℕ) • Q = 0 := by
          rw [show (3 : ℕ) = 2 + 1 from rfl, succ_nsmul, two_nsmul,
            h2Q, he, ← hxy, neg_add_cancel]
        have hd : p ∣ 3 := by
          rw [← hQ]
          exact addOrderOf_dvd_iff_nsmul_eq_zero.mpr h3
        have := Nat.le_of_dvd (by decide : 0 < 3) hd
        omega
    obtain ⟨_, hneg⟩ := triple_x_valuation_negative h₁ h₃ ha₂ hx hy hℓ hx₂ hxx₂
    have h3Q : (3 : ℕ) • Q = Point.some _ _
        (nonsingular_add hns₂ h (fun hh => hxx₂ hh.1)) := by
      rw [show (3 : ℕ) = 2 + 1 from rfl, succ_nsmul, two_nsmul,
        h2Q, hxy, Point.add_of_X_ne hxx₂]
    have hi3 := x_nonnegative_of_prime_order h₁ h₃ h₆ ha₂ ha₄ Q p hp (by omega) hQ 3
    rw [h3Q, Point.xc_some] at hi3
    change v (W.addX x₂ x (W.slope x₂ x y₂ y)) ≤ -2 at hneg
    omega

/-- pで割れない倍点の実際のx座標には正の下界がある。
k=0などpで割れる倍点は零点となるため、このガードを外して全kとは主張しない。 -/
theorem nsmul_x_positive_of_prime_order (h₁ : W.a₁ = 1) (h₃ : W.a₃ = 0) (h₆ : W.a₆ = 0)
    (ha₂ : Lower 0 W.a₂) (ha₄ : Lower 1 W.a₄)
    (Q : W.Point) (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hQ : addOrderOf Q = p)
    (k : ℕ) (hk : ¬ p ∣ k) : 1 ≤ v (k • Q).xc := by
  have hcop : (addOrderOf Q).Coprime k := by
    rw [hQ]
    exact hp.coprime_iff_not_dvd.mpr hk
  have hord : addOrderOf (k • Q) = p := hcop.addOrderOf_nsmul.trans hQ
  have hne : k • Q ≠ 0 := fun hz => hk (hQ ▸ addOrderOf_dvd_iff_nsmul_eq_zero.mpr hz)
  exact x_positive_of_prime_order h₁ h₃ h₆ ha₂ ha₄ (k • Q) p hp hp5 hord
    (Point.eq_some_xc_yc hne)

end DkMath.Lib.NumberTheory.WeierstrassPositiveValuation
