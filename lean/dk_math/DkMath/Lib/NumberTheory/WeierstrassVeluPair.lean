/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.WeierstrassVeluPolynomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

#print "file: DkMath.Lib.NumberTheory.WeierstrassVeluPair"

/-!
# 反転対の割線公式を、二つの有理関数へまとめる

[DkMath.Lib] (a,b)とその反対点を足したx座標の補正は
 t/(x−a)+u/(x−a)² となる。ここでt=6a²+b₂a+b₄、u=(2b+a₁a+a₃)²。
平方完成座標z=2y+a₁x+a₃の対和は、その有理関数の形式微分にzを掛けた式になる。
微分の理論は使わず、二つの元の曲線方程式から分母払い恒等式を直接証明する。
-/
namespace DkMath.Lib.NumberTheory.WeierstrassVeluPair
open WeierstrassCurve WeierstrassCurve.Affine WeierstrassVeluPolynomial
variable {F : Type*} [Field F] (W : WeierstrassCurve F)

/-- [DkMath.Lib] 半核代表が与えるx補正。一般点のxと代表のxが異なる場所で使う。 -/
def xCorrection (a b x : F) : F :=
  momentT W a / (x - a) + (2 * b + W.a₁ * a + W.a₃) ^ 2 / (x - a) ^ 2

/-- [DkMath.Lib] 同じ補正の形式微分に当たる式。微分構造の仮定は不要。 -/
def zCorrection (a b x : F) : F :=
  -momentT W a / (x - a) ^ 2 - 2 * (2 * b + W.a₁ * a + W.a₃) ^ 2 / (x - a) ^ 3

/-- [DkMath.Lib] 反転対のx座標の割線式。二つの方程式の差だけで証明できる。 -/
theorem secant_pair_x {x y a b : F} (hx : x ≠ a)
    (hxy : W.toAffine.Equation x y) (hab : W.toAffine.Equation a b) :
    W.toAffine.addX x a ((y - b) / (x - a)) +
      W.toAffine.addX x a ((y - W.toAffine.negY a b) / (x - a)) - 2 * a =
      xCorrection W a b x := by
  rw [equation_iff] at hxy hab
  simp only [addX, negY, xCorrection, momentT, b₂, b₄]
  field_simp [sub_ne_zero.mpr hx]
  linear_combination 2 * hxy - 2 * hab

/-- [DkMath.Lib] 平方完成座標の対和。反転対の定数補正はちょうど零となる。 -/
theorem secant_pair_z {x y a b : F} (hx : x ≠ a)
    (hxy : W.toAffine.Equation x y) (hab : W.toAffine.Equation a b) :
    (2 * W.toAffine.addY x a y ((y - b) / (x - a)) +
        W.a₁ * W.toAffine.addX x a ((y - b) / (x - a)) + W.a₃) +
      (2 * W.toAffine.addY x a y ((y - W.toAffine.negY a b) / (x - a)) +
        W.a₁ * W.toAffine.addX x a ((y - W.toAffine.negY a b) / (x - a)) + W.a₃) =
      (2 * y + W.a₁ * x + W.a₃) * zCorrection W a b x := by
  rw [equation_iff] at hxy hab
  simp only [addY, negAddY, addX, negY, zCorrection, momentT, b₂, b₄]
  field_simp [sub_ne_zero.mpr hx]
  linear_combination -2 * (2 * y + W.a₁ * x + W.a₃) * hxy +
    2 * (2 * y + W.a₁ * x + W.a₃) * hab

/-- [DkMath.Lib] 2が非零の体では、Weierstrass方程式は平方完成した三次式と同値。
2y+a₁x+a₃を用い、係数b₂,b₄,b₆を保って比較する。 -/
theorem equation_iff_completedSquare [NeZero (2 : F)] (x y : F) :
    W.toAffine.Equation x y ↔
      (2 * y + W.a₁ * x + W.a₃) ^ 2 =
        4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ := by
  rw [equation_iff]
  simp only [b₂, b₄, b₆]
  constructor
  · intro he
    linear_combination 4 * he
  · intro he
    apply mul_left_cancel₀ (show (4 : F) ≠ 0 by simpa only [show (4 : F) = 2 ^ 2 by ring] using pow_ne_zero 2 (NeZero.ne (2 : F)))
    linear_combination he

end DkMath.Lib.NumberTheory.WeierstrassVeluPair
