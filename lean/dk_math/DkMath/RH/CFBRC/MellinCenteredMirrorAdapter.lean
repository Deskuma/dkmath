/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Analysis.MellinCriticalMirror
import DkMath.RH.CFBRC.PascalCriticalMirrorRadialContourCF2DBridge
import Mathlib.Tactic

/-!
# CFBRC adapter for the generic Mellin critical mirror

This file is intentionally a thin namespace bridge.  The Mellin transform
reflection theorem lives in `DkMath.Analysis`, while the CFBRC geometry uses
`criticalMirror` and `centeredComplex`.  The only identification made here is
the elementary complex-coordinate equality `1 - conj s = criticalMirror s`,
followed by its centered specialization.

No zero predicate, zeta identity, Xi identity, explicit formula, admissibility
condition, or RH statement is used or provided here.  The centered theorem
reused from the existing CFBRC API is likewise only a coordinate identity.
-/

namespace DkMath.RH.CFBRCProjection

open scoped ComplexConjugate

/-- The Mellin reflection parameter is the CFBRC critical mirror. -/
theorem one_sub_conj_eq_criticalMirror (s : ℂ) :
    1 - (starRingEnd ℂ) s = criticalMirror s := by
  apply Complex.ext <;> simp [criticalMirror]

/-- The centered Mellin reflection parameter is the centered CFBRC mirror. -/
theorem mellinCenteredReflectionParameter_eq_criticalMirror (z : ℂ) :
    (1 : ℂ) / 2 - (starRingEnd ℂ) z =
      criticalMirror ((1 : ℂ) / 2 + z) := by
  rw [← one_sub_conj_eq_criticalMirror]
  have hhalf : (starRingEnd ℂ) ((1 : ℂ) / 2) = (1 : ℂ) / 2 := by
    apply Complex.ext <;> norm_num
  rw [map_add, hhalf]
  ring

end DkMath.RH.CFBRCProjection
