/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Five.CleanChannel

#print "file: DkMath.FLT.Five.Valuation"

namespace DkMath.FLT.Five

/-!
# Exponent-five valuation checkpoint

The direct divisibility refuter is implemented first.  This module will then carry an
independent `padicValNat` proof of the same local obstruction:

```text
complete fifth power  -> local load at least 5
clean GN5 channel     -> local load at most 1
```

No research-only valuation theorem is imported here.
-/

/-- Contract for the exponent-five valuation lower bound. -/
abbrev PadicValNatLowerBoundD5Target : Prop :=
  ∀ {x q : ℕ}, 0 < x → Nat.Prime q → q ∣ x → 5 ≤ padicValNat q (x ^ 5)

/-- Contract for the clean-channel valuation upper bound on the full fifth-power body. -/
abbrev PadicValNatCleanBodyUpperBoundTarget : Prop :=
  ∀ {g y q : ℕ}, 0 < g → CleanGN5Channel g y q → padicValNat q (g * GN5 g y) ≤ 1

end DkMath.FLT.Five
