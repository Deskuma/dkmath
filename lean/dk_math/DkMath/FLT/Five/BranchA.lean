/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Five.Basic

#print "file: DkMath.FLT.Five.BranchA"

namespace DkMath.FLT.Five

/-- The exponent-five branch in which the exponent divides the natural-number gap. -/
def BranchACondition (y z : ℕ) : Prop :=
  5 ∣ z - y

/-- Contract for a future dedicated five-adic Branch-A refuter. -/
abbrev BranchARefuter : Prop :=
  ∀ {x y z : ℕ}, CounterexamplePack x y z → BranchACondition y z → False

/-!
The first Branch-A checkpoint will extract the five-adic normal form implied by
`5 ∣ z-y`.  It will not assume that the normal form is already contradictory.
-/

end DkMath.FLT.Five
