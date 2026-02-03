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

/-- `iterate` は Mathlib の反復表記 `f^[n]` を利用する。 -/
abbrev iterate {α : Type _} (f : α → α) : Nat → α → α := fun n x => f^[n] x

@[simp]
theorem iterate_zero {α} (f : α → α) (x : α) : iterate f 0 x = x := rfl

@[simp]
theorem iterate_succ
  {α} (f : α → α) (n : Nat) (x : α) : iterate f (n + 1) x = iterate f n (f x) := by
  simp [iterate, Function.iterate_succ_apply]

section UnitIncrement

variable {State : Type _} {T : State → State} {I : State → ℕ}

/-- 1 増分の場合：`I (T s) = I s + 1` ならば k 回反復すると `I (iterate T k s) = I s + k` である。 -/
theorem I_iterate_of_unit (h : ∀ s, I (T s) = I s + 1) : ∀ k s, I (iterate T k s) = I s + k := by
  intro k s
  induction k generalizing s
  case zero => simp [iterate]
  case succ k ih =>
    simp [iterate_succ, (ih (T s)), (h s), (add_assoc (I s) 1 k), add_comm 1 k]

/-- `I` が 1 増分ならば、非自明な閉路（k>0）は存在しない。 -/
theorem no_nontrivial_cycle_unit (h : ∀ s, I (T s) = I s + 1) :
  ∀ k s, iterate T k s = s → k = 0 := by
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
theorem I_iterate_of_u (u : ℕ) (h : ∀ s, I (T s) = I s + u) :
  ∀ k s, I (iterate T k s) = I s + k * u := by
  intro k s
  induction k generalizing s
  case zero => simp [iterate, zero_mul]
  case succ k ih =>
    simp [iterate_succ, (ih (T s)), (h s), (add_assoc), (add_comm u (k * u)), ← Nat.succ_mul]

/-- 閉路なら k * u = 0。 -/
theorem cycle_mul_zero (u : ℕ) (h : ∀ s, I (T s) = I s + u) :
  ∀ k s, iterate T k s = s → k * u = 0 := by
  intros k s hk
  have eqI := congrArg I hk
  rw [I_iterate_of_u u h k s] at eqI
  -- I s + k * u = I s なので左から加算を消して k * u = 0
  rw [← Nat.add_zero (I s)] at eqI
  exact Nat.add_left_cancel eqI

/-- 特に u > 0 のとき、非自明な閉路は存在しない（k=0）。 -/
theorem no_nontrivial_cycle_of_pos_u (u : ℕ) (h :
  ∀ s, I (T s) = I s + u) (hu : u > 0) : ∀ k s, iterate T k s = s → k = 0 := by
  intros k s hk
  have := cycle_mul_zero u h k s hk
  -- k * u = 0 から `k = 0 ∨ u = 0` が得られる
  have or := (Nat.mul_eq_zero.mp this)
  cases or with
  | inl hk0 => exact hk0
  | inr hu0 => exact (False.elim (Nat.ne_of_gt hu hu0))

end GeneralU

section GeOne

variable {State : Type _} {T : State → State} {I : State → ℕ}

/--
不等式版：`I (T s) ≥ I s + 1` が常に成り立つなら、k 回反復しても
`I (iterate T k s) ≥ I s + k` が成り立つ。

増分一定（`= I s + u`）を仮定できない実モデル向け。
-/
theorem I_iterate_of_ge_one (h : ∀ s, I (T s) ≥ I s + 1) :
    ∀ k s, I (iterate T k s) ≥ I s + k := by
  intro k s
  induction k generalizing s with
  | zero =>
      simp [iterate]
  | succ k ih =>
      -- k+1 回反復は、k 回反復を `T s` から始めるのと同じ
      have h1 : I (iterate T k (T s)) ≥ I (T s) + k := ih (T s)
      have h2 : I (T s) + k ≥ I s + (k + 1) := by
        -- `I (T s) ≥ I s + 1` に k を加える
        have := Nat.add_le_add_right (h s) k
        -- (I s + 1) + k = I s + (k + 1)
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using this
      -- 連鎖して結論へ
      have : I (iterate T (k + 1) s) ≥ I s + (k + 1) := by
        -- iterate_succ: iterate T (k+1) s = iterate T k (T s)
        simpa [iterate_succ] using (ge_trans h1 h2)
      simpa [Nat.succ_eq_add_one] using this

/--
不等式版：`I (T s) ≥ I s + 1` が常に成り立つなら、非自明な閉路は存在しない。
すなわち `iterate T k s = s` ならば `k = 0`。
-/
theorem no_nontrivial_cycle_of_ge_one (h : ∀ s, I (T s) ≥ I s + 1) :
    ∀ k s, iterate T k s = s → k = 0 := by
  intro k s hk
  cases k with
  | zero => rfl
  | succ k =>
      -- 閉路仮定から矛盾を出す：I が必ず増えるのに元へ戻ることはできない
      have hge : I (iterate T (Nat.succ k) s) ≥ I s + Nat.succ k :=
        I_iterate_of_ge_one (State := State) (T := T) (I := I) h (Nat.succ k) s
      have eqI : I (iterate T (Nat.succ k) s) = I s := congrArg I hk
      have ge' : I s ≥ I s + Nat.succ k := by
        rw [eqI] at hge
        exact hge
      have lt' : I s < I s + Nat.succ k :=
        Nat.lt_add_of_pos_right (Nat.succ_pos k)
      exact (False.elim ((not_lt_of_ge ge') lt'))

end GeOne

end DkMath.UnitCycle
