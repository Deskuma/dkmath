/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from anthropics/fermats-last-theorem,
P2M/Sol/S_FreyPackage_freyCurve_rational_p_torsion_eq_zero.lean, S04.Points.
Upstream blob: fe61fd5d4f94d55b5a9da38d1541903c84397df0
Modified for DkMath: general normalized Weierstrass model with explicit coefficient bounds;
separate local coordinate arithmetic from the finite-orbit argument.
-/

import DkMath.Lib.NumberTheory.RationalTwoAdicBounds
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

#print "file: DkMath.Lib.NumberTheory.WeierstrassNegativeValuation"

/-!
# 負のx付値は倍点でさらに下がる

有理数上のモデルy²+xy=x³+a₂x²+a₄xを考える。
係数条件a₁=1,a₃=a₆=0、a₂の2進整性、a₄の深さ1以上を明示する。
有限点のxの付値が負なら、方程式がyの付値を決め、接線と倍点公式により
倍点のx付値は少なくとも2だけ小さくなる。

このファイルは局所的な座標計算だけであり、点が有限位数であるとは仮定しない。
倍点が零点になる場合は接線分母が零になるので、その場合を仮定で除く。
次の有限軌道の議論でこの仮定を奇素数位数から供給する。
-/
namespace DkMath.Lib.NumberTheory.WeierstrassNegativeValuation
open WeierstrassCurve WeierstrassCurve.Affine
open RationalTwoAdicBounds
local notation "v" => padicValRat 2
variable {W : Affine ℚ}

/-- 三つの係数を固定したモデルの実際の有限点は、正規化した方程式を満たす。 -/
theorem equation_of_normalized (h₁ : W.a₁ = 1) (h₃ : W.a₃ = 0) (h₆ : W.a₆ = 0)
    {x y : ℚ} (h : W.Nonsingular x y) :
    y ^ 2 + x * y = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x := by
  have he := (equation_iff x y).mp h.left
  rw [h₁, h₃, h₆] at he
  linear_combination he

/-- 同じモデルで負の点のy座標は−y−xである。 -/
theorem negY_of_normalized (h₁ : W.a₁ = 1) (h₃ : W.a₃ = 0) (x y : ℚ) :
    W.negY x y = -y - x := by simp [negY, h₁, h₃]

/-- xが2進整なら曲線方程式からyも整となる。負のy付値ではy²が他項より低く矛盾する。 -/
theorem y_integral_of_x_integral (h₁ : W.a₁ = 1) (h₃ : W.a₃ = 0)
    (h₆ : W.a₆ = 0) (ha₂ : Lower 0 W.a₂) (ha₄ : Lower 1 W.a₄)
    {x y : ℚ} (h : W.Nonsingular x y) (hx : Lower 0 x) : Lower 0 y := by
  by_cases hy0 : y = 0
  · exact Or.inl hy0
  by_contra hy
  have hf : v y < 0 := by
    simp only [Lower, not_or, not_le] at hy; exact hy.2
  have heq := equation_of_normalized h₁ h₃ h₆ h
  have hR : Lower 0 (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x) := by
    have h3 : Lower 0 (x ^ 3) := by
      have := Lower.mul hx (Lower.square hx); rw [← pow_succ'] at this; simpa using this
    have h2 : Lower 0 (W.a₂ * x ^ 2) := by
      have := Lower.mul ha₂ (Lower.square hx); simpa using this
    have h1 : Lower 0 (W.a₄ * x) := by
      have := Lower.mul (Lower.mono ha₄ (by norm_num : (0 : ℤ) ≤ 1)) hx
      simpa using this
    exact Lower.add (Lower.add h3 h2) h1
  have hEy : Exact (v y) y := exact_valuation hy0
  have hL : Exact (v y + v y) (y ^ 2 + x * y) := by
    have h1 : Exact (v y + v y) (y ^ 2) := Exact.square hEy
    have h2 : Lower (0 + v y) (x * y) := Lower.mul hx hEy.lower
    exact Exact.add_lower h1 h2 (by omega)
  rw [heq] at hL
  exact Exact.not_lower hL hR (by omega)

/-- xの負の付値eから、y≠0、v₂(y)<e、2v₂(y)=3eを同時に導く。
方程式の右辺ではx³が一意に低い付値を持つ。左辺の最小項を比較する。 -/
theorem y_valuation_of_x_negative (h₁ : W.a₁ = 1) (h₃ : W.a₃ = 0)
    (h₆ : W.a₆ = 0) (ha₂ : Lower 0 W.a₂) (ha₄ : Lower 1 W.a₄)
    {x y : ℚ} (h : W.Nonsingular x y) {e : ℤ} (hx : Exact e x)
    (he : e < 0) : y ≠ 0 ∧ v y < e ∧ 2 * v y = 3 * e := by
  have heq := equation_of_normalized h₁ h₃ h₆ h
  have hR : Exact (3 * e) (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x) := by
    have h3 : Exact (3 * e) (x ^ 3) := by have := Exact.pow hx 3; simpa using this
    have h2 : Lower (0 + (e + e)) (W.a₂ * x ^ 2) := Lower.mul ha₂ (Lower.square hx.lower)
    have h1 : Lower (1 + e) (W.a₄ * x) := Lower.mul ha₄ hx.lower
    exact Exact.add_lower (Exact.add_lower h3 h2 (by omega)) h1 (by omega)
  by_cases hy0 : y = 0
  · subst hy0
    have : Exact (3 * e) (0 : ℚ) := by
      have h0 : (0:ℚ) ^ 2 + x * 0 = 0 := by ring
      rw [← h0, heq]; exact hR
    exact absurd rfl this.1
  have hEy : Exact (v y) y := exact_valuation hy0
  refine ⟨hy0, ?_⟩
  rcases lt_trichotomy (v y) e with hlt | heq' | hgt
  · have hL : Exact (v y + v y) (y ^ 2 + x * y) :=
      Exact.add_lower (Exact.square hEy) (Lower.mul hx.lower hEy.lower) (by omega)
    rw [heq] at hL
    have := hL.2.symm.trans hR.2
    exact ⟨hlt, by omega⟩
  · exfalso
    have hL : Lower (e + e) (y ^ 2 + x * y) := by
      have hy' : Lower e y := Or.inr heq'.ge
      exact Lower.add (Lower.square hy') (Lower.mul hx.lower hy')
    rw [heq] at hL
    exact Exact.not_lower hR hL (by omega)
  · exfalso
    have hL : Exact (v y + e) (y ^ 2 + x * y) := by
      have : y ^ 2 + x * y = y * (y + x) := by ring
      rw [this]
      exact Exact.mul hEy (Lower.add_exact hEy.lower hx hgt)
    rw [heq] at hL
    have := hL.2.symm.trans hR.2
    omega

/-- xが負の付値eを持ち、倍点が有限点なら、そのx座標は非零で付値がe−2以下になる。
接線分母x+2yの非零性を先に確保し、傾きの平方が倍点公式の最小項になることを示す。 -/
theorem double_x_valuation_drop (h₁ : W.a₁ = 1) (h₃ : W.a₃ = 0)
    (h₆ : W.a₆ = 0) (ha₂ : Lower 0 W.a₂) (ha₄ : Lower 1 W.a₄)
    {x y : ℚ} (h : W.Nonsingular x y) {e : ℤ} (hx : Exact e x)
    (he : e < 0) (hy : y ≠ W.negY x y) :
    W.addX x x (W.slope x x y y) ≠ 0 ∧
    v (W.addX x x (W.slope x x y y)) ≤ e - 2 := by
  obtain ⟨hy0, hylt, h23⟩ := y_valuation_of_x_negative h₁ h₃ h₆ ha₂ ha₄ h hx he
  have hEy : Exact (v y) y := exact_valuation hy0
  set f := v y with hf
  have hD : y - W.negY x y = x + 2 * y := by rw [negY_of_normalized h₁ h₃]; ring
  have hD0 : x + 2 * y ≠ 0 := by rw [← hD]; exact sub_ne_zero.mpr hy
  have hDv : 1 + f ≤ v (x + 2 * y) := by
    have h2y : Exact (1 + f) (2 * y) := Exact.mul exact_two hEy
    rcases lt_or_ge (1 + f) e with hlt | hge
    · exact (Lower.add_exact hx.lower h2y hlt).2.ge
    · have hfe : 1 + f = e := by omega
      have hI : Lower (1 + f) (x + 2 * y) := Lower.add (by rw [hfe]; exact hx.lower) h2y.lower
      rcases hI with h0 | h0
      · exact absurd h0 hD0
      · exact h0
  have hN : Exact (e + e) (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ -
      W.a₁ * y) := by
    rw [h₁, one_mul]
    have h1 : Exact (0 + (e + e)) (3 * x ^ 2) := Exact.mul exact_three (Exact.square hx)
    have h2 : Lower (1 + 0 + e) (2 * W.a₂ * x) := Lower.mul (Lower.mul lower_two ha₂) hx.lower
    have h3 : Lower 1 W.a₄ := ha₄
    have h4 : Lower f y := hEy.lower
    have := Exact.sub_lower (Exact.add_lower (Exact.add_lower h1 h2 (by omega)) h3 (by omega)) h4 (by omega)
    simpa using this
  have hslope : W.slope x x y y =
      (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) /
        (x + 2 * y) := by
    rw [slope_of_Y_ne rfl hy, hD]
  set ℓ := W.slope x x y y with hℓ
  have hEℓ : Exact (e + e - v (x + 2 * y)) ℓ := by
    rw [hslope]; exact Exact.div hN (exact_valuation hD0)
  set m := e + e - v (x + 2 * y) with hm
  have hm2 : m + m ≤ e - 2 := by omega
  have hmneg : m < 0 := by omega
  have hX : Exact (m + m) (W.addX x x ℓ) := by
    simp only [addX, h₁, one_mul]
    have h1 : Exact (m + m) (ℓ ^ 2) := Exact.square hEℓ
    have h2 : Lower m ℓ := hEℓ.lower
    exact Exact.sub_lower (Exact.sub_lower (Exact.sub_lower (Exact.add_lower h1 h2 (by omega)) ha₂ (by omega))
      hx.lower (by omega)) hx.lower (by omega)
  exact ⟨hX.1, by rw [hX.2]; exact hm2⟩

end DkMath.Lib.NumberTheory.WeierstrassNegativeValuation
