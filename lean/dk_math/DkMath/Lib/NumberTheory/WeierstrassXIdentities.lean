/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from anthropics/fermats-last-theorem,
P2M/Sol/S_FreyPackage_freyCurve_rational_p_torsion_eq_zero.lean,
dbl_ident, pm_ident, frey_E_D and their point-coordinate bridges.
Upstream blob: fe61fd5d4f94d55b5a9da38d1541903c84397df0
Modified for DkMath: separate a division-free polynomial identity, actual point coordinates,
nonzero factors and exact valuations; use the completed bounds from chapter 005.
-/


import DkMath.Lib.NumberTheory.WeierstrassTorsionBounds
import Mathlib.Tactic.FieldSimp

#print "file: DkMath.Lib.NumberTheory.WeierstrassXIdentities"

/-!
# NOTE-030-006: 分母の深さと倍点・和差の恒等式

まず分母のない多項式恒等式を証明し、その後に同じモデルのaddXと点群へ接続する。
正規化係数a₁=1,a₃=a₆=0を保持し、倍点ではx+2y≠0、和差ではx₁≠x₂を要求する。
無限遠点の便宜的なxc=0を有限座標点として使わない。

有理数の付値では、1≤e≤γ−1からExact e (x+2y)を得る。
恒等式の各因子が非零であることを確認して初めてpadicValRatの積公式を適用する。
ここには整数折り返し核やtorsion排除の結論を仮定しない。
-/
namespace DkMath.Lib.NumberTheory.WeierstrassXIdentities
open WeierstrassCurve WeierstrassCurve.Affine
open RationalTwoAdicBounds WeierstrassNegativeValuation
local notation "v" => padicValRat 2

/-- 和差公式の分母を払った核。任意の可換環で二つの曲線方程式から従う。
rは二つの方程式の残差の差であり、証明は残差の線形結合として検査される。 -/
theorem plus_minus_polynomial_identity {K : Type*} [CommRing K] (x y z w a b : K)
    (hP : y ^ 2 + x * y = x ^ 3 + a * x ^ 2 + b * x)
    (hQ : w ^ 2 + z * w = z ^ 3 + a * z ^ 2 + b * z) :
    ((y - w) ^ 2 + (y - w) * (x - z) - (a + x + z) * (x - z) ^ 2) *
      ((y + w + z) ^ 2 + (y + w + z) * (x - z) - (a + x + z) * (x - z) ^ 2) =
      (x * z - b) ^ 2 * (x - z) ^ 2 := by
  let r := (y ^ 2 + x * y - (x ^ 3 + a * x ^ 2 + b * x)) -
    (w ^ 2 + z * w - (z ^ 3 + a * z ^ 2 + b * z))
  linear_combination
    (r + (x - z) * (4 * a * z + 2 * b + 2 * x * z + 4 * z ^ 2 + z)) * hP +
    (-r - (x - z) * (4 * a * x + 2 * b + 4 * x ^ 2 + 2 * x * z + x)) * hQ

variable {W : Affine ℚ}

/-- 倍点のaddXと接線分母の恒等式。非特異性と接線例外の除外を明示する。 -/
theorem double_addX_identity (h₁ : W.a₁ = 1) (h₃ : W.a₃ = 0) (h₆ : W.a₆ = 0)
    {x y : ℚ} (h : W.Nonsingular x y) (hy : y ≠ W.negY x y) :
    W.addX x x (W.slope x x y y) * (x + 2 * y) ^ 2 = (x ^ 2 - W.a₄) ^ 2 := by
  have heq := equation_of_normalized h₁ h₃ h₆ h
  have hD : y - W.negY x y = x + 2 * y := by rw [negY_of_normalized h₁ h₃]; ring
  have hD0 : x + 2 * y ≠ 0 := by rw [← hD]; exact sub_ne_zero.mpr hy
  rw [slope_of_Y_ne rfl hy, hD]
  simp only [addX, h₁, one_mul]
  field_simp
  linear_combination (-1 - 4 * W.a₂ - 8 * x) * heq

/-- 異なるx座標での和差のaddX恒等式。二つの有限点は同じ曲線に属する。 -/
theorem plus_minus_addX_identity (h₁ : W.a₁ = 1) (h₃ : W.a₃ = 0) (h₆ : W.a₆ = 0)
    {x y z w : ℚ} (hP : W.Nonsingular x y) (hQ : W.Nonsingular z w) (hx : x ≠ z) :
    W.addX x z (W.slope x z y w) * W.addX x z (W.slope x z y (W.negY z w)) *
      (x - z) ^ 2 = (x * z - W.a₄) ^ 2 := by
  have heP := equation_of_normalized h₁ h₃ h₆ hP
  have heQ := equation_of_normalized h₁ h₃ h₆ hQ
  have hd := sub_ne_zero.mpr hx
  rw [slope_of_X_ne hx, slope_of_X_ne hx, negY_of_normalized h₁ h₃]
  simp only [addX, h₁, one_mul]
  field_simp
  convert plus_minus_polynomial_identity x y z w W.a₂ W.a₄ heP heQ using 1 <;> ring

/-- 同じ有限点の実際の倍点のxcに、倍点恒等式を接続する。 -/
theorem double_x_identity (h₁ : W.a₁ = 1) (h₃ : W.a₃ = 0) (h₆ : W.a₆ = 0)
    (P : W.Point) {x y : ℚ} {h : W.Nonsingular x y} (hxy : P = Point.some x y h)
    (hy : y ≠ W.negY x y) :
    (2 • P).xc * (x + 2 * y) ^ 2 = (x ^ 2 - W.a₄) ^ 2 := by
  rw [two_nsmul, hxy, Point.add_self_of_Y_ne hy, Point.xc_some]
  exact double_addX_identity h₁ h₃ h₆ h hy

/-- 実際のP+QとP−Qのxcを使う和差恒等式。座標の非零性は付値化する段階で加える。 -/
theorem plus_minus_x_identity (h₁ : W.a₁ = 1) (h₃ : W.a₃ = 0) (h₆ : W.a₆ = 0)
    (P Q : W.Point) {x y z w : ℚ} {hP : W.Nonsingular x y} {hQ : W.Nonsingular z w}
    (hxy : P = Point.some x y hP) (hzw : Q = Point.some z w hQ) (hx : x ≠ z) :
    (P + Q).xc * (P - Q).xc * (x - z) ^ 2 = (x * z - W.a₄) ^ 2 := by
  rw [sub_eq_add_neg, hxy, hzw, Point.neg_some, Point.add_of_X_ne hx,
    Point.add_of_X_ne hx, Point.xc_some, Point.xc_some]
  exact plus_minus_addX_identity h₁ h₃ h₆ hP hQ hx

/-- 区間内の深さeを持つxでは、接線分母x+2yも非零で正確に同じ深さeを持つ。
平方完成後のx²項が一意の最低項となるため、打ち消しは起きない。 -/
theorem tangent_denominator_exact (h₁ : W.a₁ = 1) (h₃ : W.a₃ = 0) (h₆ : W.a₆ = 0)
    (ha₂ : Lower 0 W.a₂) {γ e : ℤ} (ha₄ : Exact γ W.a₄)
    {x y : ℚ} (h : W.Nonsingular x y) (hx : Exact e x) (he : 1 ≤ e) (heγ : e ≤ γ - 1) :
    Exact e (x + 2 * y) := by
  have heq := equation_of_normalized h₁ h₃ h₆ h
  have hD2 : (x + 2 * y) ^ 2 =
      4 * x ^ 3 + (1 + 4 * W.a₂) * x ^ 2 + 4 * W.a₄ * x := by
    linear_combination 4 * heq
  have hunit : Exact 0 (1 + 4 * W.a₂) := by
    have h1 : Exact 0 (1 : ℚ) := ⟨one_ne_zero, padicValRat.one⟩
    exact h1.add_lower (exact_four.lower.mul ha₂) (by norm_num)
  have hmain : Exact (e + e) ((1 + 4 * W.a₂) * x ^ 2) := by
    simpa using hunit.mul hx.square
  have h3 : Lower (2 + 3 * e) (4 * x ^ 3) := by
    simpa using exact_four.lower.mul (hx.lower.pow 3)
  have h1 : Lower (2 + γ + e) (4 * W.a₄ * x) :=
    (exact_four.lower.mul ha₄.lower).mul hx.lower
  have hE2 : Exact (e + e) ((x + 2 * y) ^ 2) := by
    rw [hD2]
    exact (h3.add_exact hmain (by omega)).add_lower h1 (by omega)
  refine ⟨fun hz => hE2.1 (by rw [hz]; ring), ?_⟩
  have hv := hE2.2
  rw [padicValRat.pow] at hv
  norm_num only [Nat.cast_ofNat] at hv
  omega

/-- 倍点恒等式の因子が非零なら、x²−a₄も非零で、正確な付値の倍点等式を得る。
接線分母のExactから分母非零とv₂(x+2y)=eを同時に供給する。 -/
theorem double_x_valuation_identity (h₁ : W.a₁ = 1) (h₃ : W.a₃ = 0) (h₆ : W.a₆ = 0)
    (P : W.Point) {x y : ℚ} {h : W.Nonsingular x y} (hxy : P = Point.some x y h)
    {e : ℤ} (hD : Exact e (x + 2 * y)) (h2x : (2 • P).xc ≠ 0) :
    x ^ 2 - W.a₄ ≠ 0 ∧ v (2 • P).xc + 2 * e = 2 * v (x ^ 2 - W.a₄) := by
  have hy : y ≠ W.negY x y := by
    intro hy
    apply hD.1
    rw [negY_of_normalized h₁ h₃] at hy
    linear_combination hy
  have hid := double_x_identity h₁ h₃ h₆ P hxy hy
  have hn : x ^ 2 - W.a₄ ≠ 0 := by
    intro hz
    apply mul_ne_zero h2x (pow_ne_zero 2 hD.1)
    rw [hid, hz, zero_pow (by decide)]
  refine ⟨hn, ?_⟩
  have hv := congrArg (padicValRat 2) hid
  rw [padicValRat.mul h2x (pow_ne_zero 2 hD.1), padicValRat.pow, padicValRat.pow, hD.2] at hv
  exact hv

/-- 和差の各x座標と差が非零なら、x(P)x(Q)−a₄も非零となり、付値恒等式が成立する。
等しいx座標や和差が無限遠点となる場合にはこの定理を適用しない。 -/
theorem plus_minus_x_valuation_identity (h₁ : W.a₁ = 1) (h₃ : W.a₃ = 0) (h₆ : W.a₆ = 0)
    (P Q : W.Point) {x y z w : ℚ} {hP : W.Nonsingular x y} {hQ : W.Nonsingular z w}
    (hxy : P = Point.some x y hP) (hzw : Q = Point.some z w hQ) (hx : x ≠ z)
    (hplus : (P + Q).xc ≠ 0) (hminus : (P - Q).xc ≠ 0) :
    x * z - W.a₄ ≠ 0 ∧ v (P + Q).xc + v (P - Q).xc + 2 * v (x - z) =
      2 * v (x * z - W.a₄) := by
  have hd := sub_ne_zero.mpr hx
  have hid := plus_minus_x_identity h₁ h₃ h₆ P Q hxy hzw hx
  have hn : x * z - W.a₄ ≠ 0 := by
    intro hz
    apply mul_ne_zero (mul_ne_zero hplus hminus) (pow_ne_zero 2 hd)
    rw [hid, hz, zero_pow (by decide)]
  refine ⟨hn, ?_⟩
  have hv := congrArg (padicValRat 2) hid
  rw [padicValRat.mul (mul_ne_zero hplus hminus) (pow_ne_zero 2 hd),
    padicValRat.mul hplus hminus, padicValRat.pow, padicValRat.pow] at hv
  exact hv

end DkMath.Lib.NumberTheory.WeierstrassXIdentities
