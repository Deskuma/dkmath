/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib
import DkMath.UnitCycle.Core

#print "file: DkMath.UnitCycle.ProofNotes"

-- ----------------------------------------------------------------------------
-- DkMath.UnitCycle.ProofNotes
--
-- 補助証明ノート：DkMath.UnitCycle.Core の定理の別証明例。
--
-- ※この Lean はあくまで補助的なものであり、DkMath の正式な一部ではない。
-- > import DkMath.UnitCycle.Core で Core の内容を利用できる。
-- > このファイルに追加する補題は example として記述する。
-- ----------------------------------------------------------------------------

namespace DkMath.UnitCycle

section GeneralU

variable {State : Type _} {T : State → State} {I : State → ℕ}

/-- 1 増分の場合：`I (T s) = I s + 1` ならば k 回反復すると `I (iterate T k s) = I s + k` である。 -/
example /- I_iterate_of_unit -/
  (h : ∀ s, I (T s) = I s + 1) : ∀ k s, I (iterate T k s) = I s + k := by
  intro k s
  induction k generalizing s
  case zero => rw [iterate_zero]; simp [add_zero]
  case succ k ih =>
    simp [iterate_succ, (ih (T s)), (h s), (add_assoc (I s) 1 k), add_comm 1 k]

/-- `I` が 1 増分ならば、非自明な閉路（k>0）は存在しない。 -/
example /- I_iterate_of_unit -/
  (h : ∀ s, I (T s) = I s + 1) :
  ∀ k s, I (iterate T k s) = I s + k := by
  intro k s
  induction k generalizing s with
  | zero => simp [iterate, add_zero]
  | succ k ih =>
    calc
      I (iterate T (k + 1) s) = I (iterate T k (T s)) := by simp [iterate]
      _ = I (T s) + k := by exact ih (T s)
      _ = I s + 1 + k := by rw [h s]
      _ = I s + (k + 1) := by
        rw [add_assoc, add_comm 1 k]

/-- `I` が 1 増分ならば、非自明な閉路（k>0）は存在しない。 -/
example /- no_nontrivial_cycle_unit -/
  (h : ∀ s, I (T s) = I s + 1) :
  ∀ k s, iterate T k s = s → k = 0 := by
  intros k s hk
  have eqI := congrArg I hk
  rw [I_iterate_of_unit h k s] at eqI
  -- I s + k = I s を得る -> 左側の加算をキャンセルして k = 0
  rw [← Nat.add_zero (I s)] at eqI
  exact Nat.add_left_cancel eqI

/-- 一般化：`I (T s) = I s + u` のとき、`I (iterate T k s) = I s + k * u`。 -/
example /- I_iterate_of_u -/
  (u : ℕ) (h : ∀ s, I (T s) = I s + u) :
  ∀ k s, I (iterate T k s) = I s + k * u := by
  intro k s
  induction k generalizing s with
  | zero => simp [iterate, zero_mul, add_zero]
  | succ k ih =>
    calc
      I (iterate T (k + 1) s) = I (iterate T k (T s)) := by simp [iterate]
      _ = I (T s) + k * u := by exact ih (T s)
      _ = I s + u + k * u := by rw [h s]
      _ = I s + (k + 1) * u := by
        rw [add_assoc, add_comm u (k * u), ← Nat.succ_mul]

end GeneralU

end DkMath.UnitCycle
