/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib

namespace DkMath.Algebra.DiffPow

open scoped BigOperators
open Finset

/-!
`a^d - b^d = (a - b) * ∑ i in range d, a^(d-1-i) * b^i`
という「差の冪の因数分解」を “宇宙式の Body 項” として使う下地。

型はまず `CommRing`（減法が要る）で作り、必要なら `ℤ` に落とす。
-/

/-- 差の冪の因数分解に出る和：`∑_{i=0}^{d-1} a^(d-1-i) * b^i` -/
def diffPowSum {α : Type*} [CommRing α] (a b : α) (d : ℕ) : α :=
  ∑ i ∈ range d, a^(d - 1 - i) * b^i

/--
差の冪の因数分解（目標）：

`a^d - b^d = (a - b) * diffPowSum a b d`

※ Mathlib を探ると `Finset.sum_range_choose` や幾何級数関連の lemma が見つかる。
自前証明で対応するか、既存 lemma を活用するか決定する。
-/
theorem pow_sub_pow_factor {α : Type*} [CommRing α] (a b : α) (d : ℕ) :
    a^d - b^d = (a - b) * diffPowSum a b d := by
  induction d with
  | zero =>
    simp [diffPowSum, range_zero, Finset.sum_empty]
  | succ d ih =>
    have eq1 : a^(d + 1) - b^(d + 1) = a * a^d - b * b^d := by ring
    rw [eq1]
    have eq2 : a * a^d - b * b^d = (a - b) * a^d + b * (a^d - b^d) := by ring
    rw [eq2, ih]
    have : diffPowSum a b (d + 1) = a^d + b * diffPowSum a b d := by
      unfold diffPowSum
      -- split the 0-th term and shift the rest (use sum_range_succ' to get f 0 + ∑ f (i+1))
      rw [Finset.sum_range_succ']
      -- show the tail sum equals b * the shifted sum
      have tail_eq : ∑ k ∈ range d, a ^ (d + 1 - 1 - (k + 1)) * b ^ (k + 1) =
                     b * ∑ i ∈ range d, a ^ (d - 1 - i) * b ^ i := by
        -- move the `b` inside the sum so `sum_congr` can match summands
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        simp only [add_tsub_cancel_right, pow_succ, Nat.sub_sub, Nat.add_comm]; ring
      rw [tail_eq]
      grind
    rw [this]
    grind

/-- 宇宙式の Body 項：`(x+u)^d - u^d` を一般化したもの -/
def BodyPow {α : Type*} [CommRing α] (x u : α) (d : ℕ) : α :=
  (x + u)^d - u^d

/-- `BodyPow x u d` は差の冪として因数分解できる（a=x+u, b=u で a-b=x）。 -/
theorem BodyPow_factor {α : Type*} [CommRing α] (x u : α) (d : ℕ) :
    BodyPow x u d = x * diffPowSum (x + u) u d := by
  induction d with
  | zero =>
    simp [BodyPow, diffPowSum, range_zero, Finset.sum_empty]
  | succ d ih =>
    show BodyPow x u (d + 1) = x * diffPowSum (x + u) u (d + 1)
    simp only [BodyPow]
    have key : (x + u)^d - u^d = x * diffPowSum (x + u) u d := by
      have h := ih
      simp only [BodyPow] at h
      exact h
    have h : (x + u)^(d + 1) - u^(d + 1) =
        x * ((x + u) * diffPowSum (x + u) u d + u^d) := by
      have h1 : (x + u)^(d + 1) - u^(d + 1) =
          (x + u) * (x + u)^d - u * u^d := by ring
      have h2 : (x + u) * (x + u)^d - u * u^d =
          (x + u) * ((x + u)^d - u^d) + (x + u) * u^d - u * u^d := by ring
      have h3 : (x + u) * ((x + u)^d - u^d) + (x + u) * u^d - u * u^d =
          (x + u) * (x * diffPowSum (x + u) u d) + x * u^d := by
        rw [key]; ring
      have h4 : (x + u) * (x * diffPowSum (x + u) u d) + x * u^d =
          x * ((x + u) * diffPowSum (x + u) u d + u^d) := by ring
      rw [h1, h2, h3, h4]
    rw [h]
    unfold diffPowSum
    -- convert the RHS sum form and show the remaining tail equals u * diffPowSum ...
    -- use the `sum_range_succ'` variant to get f 0 + ∑ f (i+1), matching the index-shifted form
    rw [Finset.sum_range_succ']
    have tail_eq : ∑ i ∈ range d, (x + u) ^ (d + 1 - 1 - (i + 1)) * u ^ (i + 1) =
                   u * ∑ i ∈ range d, (x + u) ^ (d - 1 - i) * u ^ i := by
      -- move the `u` inside the sum so `sum_congr` can match summands
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [add_tsub_cancel_right, pow_succ, Nat.sub_sub, Nat.add_comm]; ring
    rw [tail_eq]
    simp only [add_tsub_cancel_right, tsub_zero, pow_zero, mul_one]
    rw [eq_add_of_sub_eq key]
    rw [diffPowSum]
    ring

end DkMath.Algebra.DiffPow
