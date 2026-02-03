/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib
import DkMath.UnitCycle.Core

#print "file: DkMath.UnitCycle.Examples"

namespace DkMath.UnitCycle

/-- 最小の State の例。`val : ℕ` を持つ。 -/
structure State where
  val : ℕ
  deriving Repr, Inhabited

/-- 周回遷移：値を 1 増やす。 -/
def T (s : State) : State := { val := s.val + 1 }

/-- 不変量：`I s = s.val` とする。 -/
def I (s : State) : ℕ := s.val

theorem I_T (s : State) : I (T s) = I s + 1 := by simp [I, T]

/-- コア定理を適用して、この具体例に非自明な閉路は存在しないことを示す。 -/
theorem no_cycle_examples (k : ℕ) (s : State) (h : iterate T k s = s) : k = 0 :=
  no_nontrivial_cycle_unit (fun s => I_T s) k s h

end DkMath.UnitCycle
