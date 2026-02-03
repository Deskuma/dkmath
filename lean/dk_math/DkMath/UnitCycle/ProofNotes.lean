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

/-- 同じ定理、別証明。 -/
example /- I_iterate_of_u -/ (u : ℕ) (h : ∀ s, I (T s) = I s + u) :
  ∀ k s, I (iterate T k s) = I s + k * u := by
  intro k s
  induction k generalizing s with
  | zero => simp only [iterate, Function.iterate_zero_apply, zero_mul, add_zero]
  | succ k ih =>
    calc
      I (iterate T (k + 1) s) = I (iterate T k (T s)) := by simp [iterate]
      _ = I (T s) + k * u := by exact ih (T s)
      _ = I s + u + k * u := by rw [h s]
      _ = I s + (k + 1) * u := by
        rw [add_assoc, add_comm u (k * u), ← Nat.succ_mul]

end GeneralU

end DkMath.UnitCycle
