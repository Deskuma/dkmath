/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Five.BranchA
import DkMath.FLT.Five.Provider
import DkMath.FLT.Five.Reduction
import DkMath.FLT.Five.Valuation

#print "file: DkMath.FLT.Five.Main"

namespace DkMath.FLT.Five

/-- Local exponent-five target, independent of the legacy general-`p ≥ 5` facade. -/
abbrev FLT5Target : Prop :=
  ∀ x y z : ℕ,
    0 < x →
    0 < y →
    0 < z →
    ¬ Fermat5Equation x y z

/-!
The final assembly theorem will combine:

- a dedicated Branch-A refuter, and
- an existential Branch-B clean-channel provider plus the local clean-channel refuter.

No assembly theorem is declared before both branches are Lean-certified.
-/

end DkMath.FLT.Five
