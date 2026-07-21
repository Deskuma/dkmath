/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.BookOfMagic
import DkMath.Hackathon.JacobianCounterexample3.Normalized

namespace DkMath.Hackathon.JacobianCounterexample3

/-- Input addresses, viewed as a constant dependent gap family over output cores. -/
abbrev NormalizedGapFamilyC : Point3C → Type := fun _ ↦ Point3C

/-- An input gap restores an output core when the normalized map evaluates to it. -/
def normalizedRestoreRelC
    (core : Point3C)
    (gap : NormalizedGapFamilyC core) : Prop :=
  evalNormalizedCounterexampleC gap = core

/-- The normalized collision target does not have a unique restoring input gap. -/
theorem normalizedTargetC_not_uniqueGap :
    ¬ DkMath.BookOfMagic.UniqueGap
      normalizedRestoreRelC
      normalizedTargetC := by
  apply DkMath.BookOfMagic.not_uniqueGap_of_two
      (gap₁ := p0C) (gap₂ := p1C)
  · simpa [normalizedRestoreRelC] using normalized_eval_p0C
  · simpa [normalizedRestoreRelC] using normalized_eval_p1C
  · exact p0C_ne_p1C

/-- Forgetting the restoring input gap is noninjective at the normalized collision. -/
theorem normalizedForgetGap_notInjective :
    ¬ Function.Injective
      (DkMath.BookOfMagic.forgetGap
        (Core := Point3C)
        (Gap := NormalizedGapFamilyC)
        (RestoreRel := normalizedRestoreRelC)) := by
  apply DkMath.BookOfMagic.forgetGap_notInjective_of_two_gaps
      (core := normalizedTargetC) (gap₁ := p0C) (gap₂ := p1C)
  · simpa [normalizedRestoreRelC] using normalized_eval_p0C
  · simpa [normalizedRestoreRelC] using normalized_eval_p1C
  · exact p0C_ne_p1C

end DkMath.Hackathon.JacobianCounterexample3
