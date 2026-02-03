/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib

#print "file: DkMath.UnitCycle.Core"
-- ----------------------------------------------------------------------------
-- DkMath.UnitCycle.Core
--
-- 抽象定理：不変量が反復で加算的増分を取る場合、非自明な閉路は存在しない。
-- ----------------------------------------------------------------------------

namespace DkMath.UnitCycle

/-- 単純な反復関数。`iterate f n x` は `f` を n 回適用した結果。 -/
def iterate {α : Type _} (f : α → α) : Nat → α → α
  | 0 => fun x => x
  | n+1 => fun x => iterate f n (f x)

@[simp]
theorem iterate_zero {α} (f : α → α) (x : α) : iterate f 0 x = x := rfl

@[simp]
theorem iterate_succ {α} (f : α → α) (n : Nat) (x : α) : iterate f (n + 1) x = iterate f n (f x) := rfl

section UnitIncrement

variable {State : Type _} {T : State → State} {I : State → ℕ}

/-- 1 増分の場合：`I (T s) = I s + 1` ならば k 回反復すると `I (iterate T k s) = I s + k` である。 -/
theorem I_iterate_of_unit (h : ∀ s, I (T s) = I s + 1) : ∀ k s, I (iterate T k s) = I s + k := by
  intro k s
  induction k generalizing s
  case zero => rw [iterate_zero]; simp [Nat.add_zero]
  case succ k ih =>
    rw [iterate_succ]
    have ih' := ih (T s)
    rw [ih']
    rw [h s]
    rw [add_assoc (I s) 1 k]
    rw [add_comm 1 k]

theorem I_iterate_of_unit' (h : ∀ s, I (T s) = I s + 1) : ∀ k s, I (iterate T k s) = I s + k := by
  intro k s
  induction k generalizing s with
  | zero => simp [iterate, Nat.add_zero]
  | succ k ih =>
    calc
      I (iterate T (k + 1) s) = I (iterate T k (T s)) := by simp [iterate]
      _ = I (T s) + k := by exact ih (T s)
      _ = I s + 1 + k := by rw [h s]
      _ = I s + (k + 1) := by
        rw [add_assoc, add_comm 1 k]


/-- `I` が 1 増分ならば、非自明な閉路（k>0）は存在しない。 -/
theorem no_nontrivial_cycle_unit (h : ∀ s, I (T s) = I s + 1) : ∀ k s, iterate T k s = s → k = 0 := by
  intros k s hk
  have eqI := congrArg I hk
  rw [I_iterate_of_unit h k s] at eqI
  -- I s + k = I s を得る -> 左側の加算をキャンセルして k = 0
  rw [← Nat.add_zero (I s)] at eqI
  exact Nat.add_left_cancel eqI

end UnitIncrement

section GeneralU

variable {State : Type _} {T : State → State} {I : State → ℕ}

/-- 一般化：`I (T s) = I s + u` のとき、`I (iterate T k s) = I s + k * u`。 -/
theorem I_iterate_of_u (u : ℕ) (h : ∀ s, I (T s) = I s + u) : ∀ k s, I (iterate T k s) = I s + k * u := by
  intro k s
  induction k generalizing s
  case zero => rw [iterate_zero]; simp [Nat.mul_zero]
  case succ k ih =>
    rw [iterate_succ]
    have ih' := ih (T s)
    rw [ih']
    rw [h s]
    rw [add_assoc]
    rw [add_comm u (k * u)]
    rw [← Nat.succ_mul]

theorem I_iterate_of_u' (u : ℕ) (h : ∀ s, I (T s) = I s + u) : ∀ k s, I (iterate T k s) = I s + k * u := by
  intro k s
  induction k generalizing s with
  | zero => simp [iterate, Nat.mul_zero]
  | succ k ih =>
    calc
      I (iterate T (k + 1) s) = I (iterate T k (T s)) := by simp [iterate]
      _ = I (T s) + k * u := by exact ih (T s)
      _ = I s + u + k * u := by rw [h s]
      _ = I s + (k + 1) * u := by
        rw [add_assoc, add_comm u (k * u), ← Nat.succ_mul]

/-- 閉路なら k * u = 0。 -/
theorem cycle_mul_zero (u : ℕ) (h : ∀ s, I (T s) = I s + u) : ∀ k s, iterate T k s = s → k * u = 0 := by
  intros k s hk
  have eqI := congrArg I hk
  rw [I_iterate_of_u u h k s] at eqI
  -- I s + k * u = I s なので左から加算を消して k * u = 0
  rw [← Nat.add_zero (I s)] at eqI
  exact Nat.add_left_cancel eqI

/-- 特に u > 0 のとき、非自明な閉路は存在しない（k=0）。 -/
theorem no_nontrivial_cycle_of_pos_u (u : ℕ) (h : ∀ s, I (T s) = I s + u) (hu : u > 0) : ∀ k s, iterate T k s = s → k = 0 := by
  intros k s hk
  have := cycle_mul_zero u h k s hk
  -- k * u = 0 から `k = 0 ∨ u = 0` が得られる
  have or := (Nat.mul_eq_zero.mp this)
  cases or with
  | inl hk0 => exact hk0
  | inr hu0 => exact (False.elim (Nat.ne_of_gt hu hu0))

end GeneralU

end DkMath.UnitCycle
