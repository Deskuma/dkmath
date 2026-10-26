/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

#print "file: DkMath.Lib.Algebra.ValuationVeluExpansion"

/-!
# Vélu対和の無限遠展開を、付値環の有限計算へ翻訳する

[DkMath.Lib] h=1/xが極大イデアルに入るとき、1−ahは単元となる。
対和をhの三次・四次の剰余まで正確に展開し、剰余係数の整性を証明する。
形式級数や収束は不要。有限の有理式恒等式と部分環の閉性だけを用いる。
-/
namespace DkMath.Lib.Algebra.ValuationVeluExpansion
variable {F Γ : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ]

/-- [DkMath.Lib] x補正の三次剰余係数。分母1−ahは無限遠で単元となる。 -/
def remainderX (a t u h : F) : F :=
  a ^ 2 * t / (1 - a * h) + u * a * (2 - a * h) / (1 - a * h) ^ 2

/-- [DkMath.Lib] 形式微分補正の四次剰余係数。 -/
def remainderZ (a t u h : F) : F :=
  -t * a ^ 2 * (3 - 2 * a * h) / (1 - a * h) ^ 2 -
    2 * u * a * (3 - 3 * a * h + (a * h) ^ 2) / (1 - a * h) ^ 3

/-- [DkMath.Lib] 対和とその形式微分の有限で正確な二段展開。 -/
theorem pair_expansion (x h a t u : F) (hxh : x * h = 1) (hd : 1 - a * h ≠ 0) :
    t / (x - a) + u / (x - a) ^ 2 =
      h * (t + h * (a * t + u + h * remainderX a t u h)) ∧
    -t / (x - a) ^ 2 - 2 * u / (x - a) ^ 3 =
      h ^ 2 * (-t + h * (-2 * (a * t + u) + h * remainderZ a t u h)) := by
  have hxa : x - a ≠ 0 := by
    intro he
    apply hd
    linear_combination h * he - hxh
  have hi : (x - a)⁻¹ = h / (1 - a * h) := by
    field_simp [hxa, hd]
    linear_combination -hxh
  simp only [div_eq_mul_inv, ← inv_pow, hi]
  unfold remainderX remainderZ
  set d := 1 - a * h with hddef
  have hd' : d ≠ 0 := hd
  constructor <;> field_simp [hd'] <;> dsimp only [d] <;> ring

/-- [DkMath.Lib] hが極大イデアル、a,t,uが整なら、二つの正確な剰余係数も整。 -/
theorem remainders_mem (v : Valuation F Γ) (a t u h : F)
    (ha : a ∈ v.valuationSubring) (ht : t ∈ v.valuationSubring)
    (hu : u ∈ v.valuationSubring) (hh : v h < 1) :
    remainderX a t u h ∈ v.valuationSubring ∧ remainderZ a t u h ∈ v.valuationSubring := by
  let V := v.valuationSubring.toSubring
  have hh' : h ∈ V := hh.le
  have hd : v (1 - a * h) = 1 := v.map_one_sub_of_lt (by
    rw [map_mul]
    exact (mul_le_of_le_one_left' ha).trans_lt hh)
  have hi : (1 - a * h)⁻¹ ∈ V := by
    change v ((1 - a * h)⁻¹) ≤ 1
    rw [map_inv₀, hd, inv_one]
  change remainderX a t u h ∈ V ∧ remainderZ a t u h ∈ V
  simp only [remainderX, remainderZ, div_eq_mul_inv, ← inv_pow]
  constructor <;>
    repeat' first | assumption | exact natCast_mem V _ | apply V.add_mem | apply V.sub_mem |
      apply V.neg_mem | apply V.mul_mem | apply V.pow_mem

/-- [DkMath.Lib] 平方完成した三次式。 -/
def cubic (b₂ b₄ b₆ x : F) : F := 4 * x ^ 3 + b₂ * x ^ 2 + 2 * b₄ * x + b₆

/-- [DkMath.Lib] 平方完成残差の全係数と二座標が部分環に入れば、残差も入る。 -/
theorem squareDefect_mem (A : Subring F) (X Y a₁ a₃ b₂ b₄ b₆ : F)
    (hX : X ∈ A) (hY : Y ∈ A) (h₁ : a₁ ∈ A) (h₃ : a₃ ∈ A)
    (h₂ : b₂ ∈ A) (h₄ : b₄ ∈ A) (h₆ : b₆ ∈ A) :
    (2 * Y + a₁ * X + a₃) ^ 2 - cubic b₂ b₄ b₆ X ∈ A := by
  unfold cubic
  repeat' first | assumption | exact natCast_mem A _ | apply A.add_mem |
    apply A.sub_mem | apply A.mul_mem | apply A.pow_mem

/-- [DkMath.Lib] 正確な二段展開から、候補三次方程式の残差が無限遠で厳密に消える。
TとWは有限核の二つのモーメント和、A,Bは整な剰余係数である。 -/
theorem defect_lt_one (v : Valuation F Γ) (x z X Z h T W A B b₂ b₄ b₆ : F)
    (hxh : x * h = 1) (hh : v h < 1)
    (hT : T ∈ v.valuationSubring) (hW : W ∈ v.valuationSubring)
    (hA : A ∈ v.valuationSubring) (hB : B ∈ v.valuationSubring)
    (h₂ : b₂ ∈ v.valuationSubring) (h₄ : b₄ ∈ v.valuationSubring)
    (h₆ : b₆ ∈ v.valuationSubring)
    (hz : z ^ 2 = cubic b₂ b₄ b₆ x)
    (hX : X = x + h * (T + h * (W + h * A)))
    (hZ : Z = z * (1 + h ^ 2 * (-T + h * (-2 * W + h * B)))) :
    v (Z ^ 2 - cubic b₂ (b₄ - 10 * T) (b₆ - 4 * b₂ * T - 28 * W) X) < 1 := by
  let r := T + h * (W + h * A)
  let s := -T + h * (-2 * W + h * B)
  let P := 8 * B - 12 * A + 2 * b₂ * (-3 * W + h * (B - A)) +
    4 * b₄ * s - 2 * b₄ * r + 2 * b₆ * h * s +
    (4 + b₂ * h + 2 * b₄ * h ^ 2 + b₆ * h ^ 3) * s ^ 2 -
    (12 + b₂ * h) * r ^ 2 - 4 * h ^ 2 * r ^ 3 + 20 * T * r
  have he : Z ^ 2 - cubic b₂ (b₄ - 10 * T) (b₆ - 4 * b₂ * T - 28 * W) X = h * P := by
    have hn : h ≠ 0 := by intro he; simp [he] at hxh
    have hx : x = h⁻¹ := by
      calc x = x * h * h⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ hn, mul_one]
           _ = h⁻¹ := by rw [hxh, one_mul]
    rw [hZ, mul_pow, hz, hX, hx]
    dsimp only [P, r, s, cubic]
    field_simp [hn]
    ring
  let V := v.valuationSubring.toSubring
  have hh' : h ∈ V := hh.le
  have hr : r ∈ V := by
    dsimp only [r]
    repeat' first | assumption | apply V.add_mem | apply V.mul_mem
  have hs : s ∈ V := by
    dsimp only [s]
    repeat' first | assumption | exact natCast_mem V _ | exact intCast_mem V _ | apply V.add_mem | apply V.mul_mem | apply V.neg_mem
  have hP : P ∈ V := by
    dsimp only [P]
    repeat' first | assumption | exact natCast_mem V _ | exact intCast_mem V _ |
      apply V.add_mem | apply V.sub_mem | apply V.neg_mem | apply V.mul_mem | apply V.pow_mem
  rw [he, map_mul]
  exact (mul_le_of_le_one_right' hP).trans_lt hh

end DkMath.Lib.Algebra.ValuationVeluExpansion
