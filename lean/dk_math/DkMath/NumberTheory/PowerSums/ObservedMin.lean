/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

-- NumberTheory.PowerSums module: Observed minimum profile definitions

import Mathlib
import DkMath.NumberTheory.PowerSums.Basic

#print "file: DkMath.NumberTheory.PowerSums.ObservedMin"

namespace DkMath
namespace NumberTheory
namespace PowerSums

/-!
## Observed Minimum Profiles

A lightweight observational notion for fillability:

- `ObservedMinOne d n`: `n` is fillable by one `d`-th power.
- `ObservedMinTwo d n`: `n` is not fillable by one `d`-th power,
  but is fillable by two `d`-th powers.

This is weaker than a full `FillRank`, but useful for direct observation.
-/

/--
Observed minimum at count 1.

`n` is fillable by exactly one `d`-th power.
-/
def ObservedMinOne (d n : ℕ) : Prop :=
  FillableByPowSumExact d n 1

/--
Observed minimum at count 2.

`n` is not fillable by one `d`-th power,
but is fillable by two `d`-th powers.
-/
def ObservedMinTwo (d n : ℕ) : Prop :=
  ¬ FillableByPowSumExact d n 1 ∧ FillableByPowSumExact d n 2

/--
Relationship: `ObservedMinOne` implies `ObservedMinTwo` is false.
-/
theorem not_observedMinTwo_of_observedMinOne (d n : ℕ)
    (h : ObservedMinOne d n) :
    ¬ ObservedMinTwo d n := by
  unfold ObservedMinTwo ObservedMinOne at *
  intro ⟨hnot, _⟩
  exact hnot h

end PowerSums
end NumberTheory
end DkMath
