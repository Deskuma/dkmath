/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Five.Basic

#print "file: DkMath.FLT.Five.BranchA"

namespace DkMath.FLT.Five

/-!
# Exceptional five-divisible gap interface

`BranchACondition y z` names the exceptional orientation `5 | z-y`.  In the completed
tower this branch is not attacked by the early clean-channel argument.  Instead,
`SignedBranchA` routes both the difference and sum orientations into a common exact
five-adic packet, and the later golden-order descent supplies the refuter contract.
-/

/-- The exponent-five branch in which the exponent divides the natural-number gap. -/
def BranchACondition (y z : ℕ) : Prop :=
  5 ∣ z - y

/-- Reusable receiver for the completed signed five-adic and golden-order refutation
of a primitive candidate whose natural gap is divisible by five. -/
abbrev BranchARefuter : Prop :=
  ∀ {x y z : ℕ}, CounterexamplePack x y z → BranchACondition y z → False

end DkMath.FLT.Five
