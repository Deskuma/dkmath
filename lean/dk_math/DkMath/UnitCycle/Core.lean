/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib

open scoped BigOperators

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

/-- iterate の前後適用が入れ替えられる補題 -/
theorem iterate_comm {α} (f : α → α) (n : Nat) (x : α) : iterate f n (f x) = f (iterate f n x) := by
  induction n generalizing x with
  | zero => simp [iterate]
  | succ n ih => simp [iterate_succ, ih]

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

section SumIncrement

variable {State : Type _} {T : State → State} {I : State → ℕ} {g : State → ℕ}

/-- 反復ごとの増分の総和で下から抑える（最強の形）。 -/
theorem I_iterate_ge_sum_g (hT : ∀ s, I (T s) ≥ I s + g s) :
  ∀ k s, I (iterate T k s) ≥ I s + (Finset.sum (Finset.range k) fun i => g (iterate T i s)) := by
  intro k s
  induction k generalizing s with
  | zero => simp [iterate]
  | succ k ih =>
    have step := hT (iterate T k s)
    have ih' := ih s
    have A := le_trans (Nat.add_le_add_right ih' (g (iterate T k s))) step
    let e := (iterate_succ (f := T) k s).trans (iterate_comm (f := T) k s)
    -- 左辺を e で書き換え、右辺の sum を開いて A と直接一致させる
    rw [e]
    rw [Finset.sum_range_succ (fun i => g (iterate T i s)) k]
    simp only [ge_iff_le, add_assoc] at *
    exact A

/-- `g(s) ≥ 1` なら総和版から即座に `+k` 版が出る。 -/
theorem I_iterate_ge_add_k (hg : ∀ s, 1 ≤ g s) (hT : ∀ s, I (T s) ≥ I s + g s) :
  ∀ k s, I (iterate T k s) ≥ I s + k := by
  intro k s
  have hs := I_iterate_ge_sum_g (T := T) (I := I) (g := g) hT k s
  have hsum : k ≤ (Finset.sum (Finset.range k) fun i => g (iterate T i s)) := by
    have : (Finset.sum (Finset.range k) fun i => (1 : ℕ))
         ≤ (Finset.sum (Finset.range k) fun i => g (iterate T i s)) :=
      Finset.sum_le_sum fun i hi => hg (iterate T i s)
    simpa [Finset.sum_const, Finset.card_range] using this
  -- I s + k ≤ I s + Σ g ≤ I(iterate T k s)
  exact le_trans (Nat.add_le_add_left hsum (I s)) hs

end SumIncrement

section StateDependentIncrement

variable {State : Type _} {T : State → State} {I : State → ℕ} {g : State → ℕ}

/-- 状態依存の増分でも、常に `g s ≥ 1` なら `I` は反復で少なくとも `k` 増える。 -/
theorem I_iterate_of_ge_g (hg : ∀ s, 1 ≤ g s) (hT : ∀ s, I (T s) ≥ I s + g s) :
  ∀ k s, I (iterate T k s) ≥ I s + k :=
  I_iterate_ge_add_k (hg := hg) (hT := hT)

/-- 状態依存増分 `g(s)≥1` の下で、非自明閉路は存在しない。 -/
theorem no_nontrivial_cycle_of_ge_g (hg : ∀ s, 1 ≤ g s) (hT : ∀ s, I (T s) ≥ I s + g s) :
  ∀ k s, iterate T k s = s → k = 0 := by
  intro k s hk
  -- g(s) ≥ 1 and I(T s) ≥ I s + g s together give I(T s) ≥ I s + 1
  let hge1 : ∀ s, I (T s) ≥ I s + 1 := fun s => ge_trans (hT s) (Nat.add_le_add_left (hg s) (I s))
  exact no_nontrivial_cycle_of_ge_one (State := State) (T := T) (I := I) hge1 k s hk

end StateDependentIncrement

section StrictIncrement

variable {State : Type _} {T : State → State} {I : State → ℕ}

/-- `I (T s) > I s` なら `I (T s) ≥ I s + 1` に落ちる（Nat）。 -/
lemma ge_one_of_strict (h : ∀ s, I (T s) > I s) : ∀ s, I (T s) ≥ I s + 1 := by
  intro s
  have : Nat.succ (I s) ≤ I (T s) := Nat.succ_le_of_lt (h s)
  simpa [Nat.succ_eq_add_one] using this

/-- 厳密増分なら既存の不等式版定理へ落として非自明閉路を排除する。 -/
theorem no_nontrivial_cycle_of_strict (h : ∀ s, I (T s) > I s) :
  ∀ k s, iterate T k s = s → k = 0 := by
  intro k s hk
  exact no_nontrivial_cycle_of_ge_one (State := State) (T := T) (I := I) (ge_one_of_strict h) k s hk

end StrictIncrement

end DkMath.UnitCycle
