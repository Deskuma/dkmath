/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Tactic.LinearCombination

#print "file: DkMath.Lib.Algebra.ValuationCubicModel"

/-!
# 極位数2,3と正則な補正から、三次式の最高項を固定する

[DkMath.Lib] X−x,Y−yが正則なら、Y²+a₁XY+a₃Y−X³の極は高々4。
三次項を単なる次数の一致で推測せず、元の曲線方程式と差の因数分解で比較する。
この評価は、多項式化した後に右辺の最高係数が1であることを保証する。
-/
namespace DkMath.Lib.Algebra.ValuationCubicModel
open WithZero
variable {F : Type*} [Field F]

/-- [DkMath.Lib] 同じ曲線の座標へ正則項を足しても、Y²とX³の最高極は相殺する。
a₂,a₄,a₆の新しい値を先に仮定せず、残差の極上界4を与える。 -/
theorem residual_le (v : Valuation F ℤᵐ⁰) (x y X Y a₁ a₂ a₃ a₄ a₆ : F)
    (hcurve : y ^ 2 + a₁ * x * y + a₃ * y = x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆)
    (hx : v x = exp (2 : ℤ)) (hy : v y = exp (3 : ℤ))
    (hX : v X = exp (2 : ℤ)) (hY : v Y = exp (3 : ℤ))
    (hdX : v (X - x) ≤ 1) (hdY : v (Y - y) ≤ 1)
    (h₁ : v a₁ ≤ 1) (h₂ : v a₂ ≤ 1) (h₃ : v a₃ ≤ 1)
    (h₄ : v a₄ ≤ 1) (h₆ : v a₆ ≤ 1) :
    v (Y ^ 2 + a₁ * X * Y + a₃ * Y - X ^ 3) ≤ exp (4 : ℤ) := by
  have he23 : exp (2 : ℤ) ≤ exp (3 : ℤ) := exp_le_exp.mpr (by decide)
  have he34 : exp (3 : ℤ) ≤ exp (4 : ℤ) := exp_le_exp.mpr (by decide)
  have he04 : (1 : ℤᵐ⁰) ≤ exp (4 : ℤ) := by rw [← exp_zero, exp_le_exp]; decide
  have hx2 : v (x ^ 2) = exp (4 : ℤ) := by rw [map_pow, hx]; rfl
  have hX2 : v (X ^ 2) = exp (4 : ℤ) := by rw [map_pow, hX]; rfl
  have hXx : v (X * x) = exp (4 : ℤ) := by rw [map_mul, hX, hx]; rfl
  have hbase : v (y ^ 2 + a₁ * x * y + a₃ * y - x ^ 3) ≤ exp (4 : ℤ) := by
    have he : y ^ 2 + a₁ * x * y + a₃ * y - x ^ 3 = a₂ * x ^ 2 + a₄ * x + a₆ := by
      linear_combination hcurve
    rw [he]
    apply (v.map_add _ _).trans (max_le ?_ (h₆.trans he04))
    apply (v.map_add _ _).trans (max_le ?_ ?_)
    · rw [map_mul, hx2]
      exact (mul_le_mul' h₂ le_rfl).trans_eq (one_mul _)
    · rw [map_mul, hx]
      exact ((mul_le_mul' h₄ le_rfl).trans_eq (one_mul _)).trans (he23.trans he34)
  have hdY2 : v ((Y - y) * (Y + y)) ≤ exp (4 : ℤ) := by
    rw [map_mul]
    have hs : v (Y + y) ≤ exp (3 : ℤ) := (v.map_add _ _).trans (max_le hY.le hy.le)
    exact ((mul_le_mul' hdY hs).trans_eq (one_mul _)).trans he34
  have hdXY : v (a₁ * ((X - x) * Y + x * (Y - y))) ≤ exp (4 : ℤ) := by
    rw [map_mul]
    have hs : v ((X - x) * Y + x * (Y - y)) ≤ exp (3 : ℤ) := by
      apply (v.map_add _ _).trans (max_le ?_ ?_)
      · rw [map_mul, hY]
        exact (mul_le_mul' hdX le_rfl).trans_eq (one_mul _)
      · rw [map_mul, hx]
        exact ((mul_le_mul' le_rfl hdY).trans_eq (mul_one _)).trans he23
    exact ((mul_le_mul' h₁ hs).trans_eq (one_mul _)).trans he34
  have hdY1 : v (a₃ * (Y - y)) ≤ exp (4 : ℤ) := by
    rw [map_mul]
    exact ((mul_le_mul' h₃ hdY).trans_eq (one_mul 1)).trans he04
  have hdX3 : v ((X - x) * (X ^ 2 + X * x + x ^ 2)) ≤ exp (4 : ℤ) := by
    rw [map_mul]
    have hs : v (X ^ 2 + X * x + x ^ 2) ≤ exp (4 : ℤ) :=
      (v.map_add _ _).trans (max_le
        ((v.map_add _ _).trans (max_le hX2.le hXx.le)) hx2.le)
    exact (mul_le_mul' hdX hs).trans_eq (one_mul _)
  have he : Y ^ 2 + a₁ * X * Y + a₃ * Y - X ^ 3 =
      (y ^ 2 + a₁ * x * y + a₃ * y - x ^ 3) + (Y - y) * (Y + y) +
      a₁ * ((X - x) * Y + x * (Y - y)) + a₃ * (Y - y) -
      (X - x) * (X ^ 2 + X * x + x ^ 2) := by ring
  rw [he]
  exact (v.map_sub _ _).trans (max_le
    ((v.map_add _ _).trans (max_le
      ((v.map_add _ _).trans (max_le
        ((v.map_add _ _).trans (max_le hbase hdY2)) hdXY)) hdY1)) hdX3)

end DkMath.Lib.Algebra.ValuationCubicModel
