/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

-- NumberTheory.PowerSums module: Concrete examples of fillability

import Mathlib
import DkMath.NumberTheory.PowerSums.Basic
import DkMath.NumberTheory.PowerSums.ObservedMin

#print "file: DkMath.NumberTheory.PowerSums.Examples"

namespace DkMath
namespace NumberTheory
namespace PowerSums

/-!
## Additional Concrete Examples

Examples demonstrating simple observed minimum profiles.
-/

/-- `16` is observed minimum 1 for degree 2 (squares). -/
theorem observed_min_one_sq_16 : ObservedMinOne 2 16 :=
  fillable_sq_16_exact_one

/-- `64 = 4^3` is observed minimum 1 for degree 3 (cubes). -/
theorem observed_min_one_cube_64 : ObservedMinOne 3 64 := by
  refine ⟨fun _ => 4, ?_⟩
  simp

/-- `27 = 3^3` is observed minimum 1 for degree 3 (cubes). -/
theorem observed_min_one_cube_27 : ObservedMinOne 3 27 := by
  refine ⟨fun _ => 3, ?_⟩
  simp

end PowerSums
end NumberTheory
end DkMath
