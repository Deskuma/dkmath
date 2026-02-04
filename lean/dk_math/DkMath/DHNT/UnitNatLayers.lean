/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.UnitCycle.Core

/-
Unit/Nat 層の最小 Lean 定義と交えない定理
-/

namespace DkMath.DHNT

open DkMath.UnitCycle

/-- Nat 層での「進歩」：毎ステップ I が 1 以上増える -/
def Progress {State : Type} (T : State → State) (I : State → Nat) : Prop :=
  ∀ s, I (T s) ≥ I s + 1

/-- Nat 層での「閉路」：k > 0 で反復が元へ戻る -/
def HasCycle {State : Type} (T : State → State) : Prop :=
  ∃ s k, k > 0 ∧ iterate T k s = s

/-- 「交える」＝（π 的）閉路と（e 的）進歩が同居すること -/
def Mixable {State : Type} (T : State → State) (I : State → Nat) : Prop :=
  HasCycle T ∧ Progress T I

/-- 進歩がある系では閉路は起きない（ゆえに交えない） -/
theorem not_mixable_of_progress {State : Type} {T : State → State} {I : State → Nat}
  (hP : Progress T I) : ¬ Mixable T I := by
  intro hM
  rcases hM with ⟨⟨s, k, hkpos, hk⟩, _⟩
  have hk0 := no_nontrivial_cycle_of_ge_one (State := State) (T := T) (I := I) hP k s hk
  exact (Nat.ne_of_gt hkpos) hk0

end DkMath.DHNT
