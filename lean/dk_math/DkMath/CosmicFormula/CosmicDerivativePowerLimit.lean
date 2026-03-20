/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib

import DkMath.CosmicFormula.CosmicDerivativeBasic
import DkMath.CosmicFormula.CosmicDerivativePower

#print "file: DkMath.CosmicFormula.CosmicDerivativePowerLimit"

namespace DkMath.CosmicFormula

/-- Power-function derivative theorem in cosmic module naming. -/
theorem hasDerivAt_pow_cosmic (d : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => y ^ d) ((d : ℝ) * x ^ (d - 1)) x := by
  simpa using (hasDerivAt_pow d x)

/--
Punctured-limit version of `powerKernel` at `u → 0`.

This is the Phase 4 limit target aligned with the cosmic-kernel bridge.
-/
theorem tendsto_powerKernel_zero (d : ℕ) (x : ℝ) :
    Filter.Tendsto (fun u : ℝ => powerKernel d x u)
      (nhdsWithin (0 : ℝ) (Set.compl ({(0 : ℝ)} : Set ℝ)))
      (nhds ((d : ℝ) * x ^ (d - 1))) := by
  refine tendsto_nhdsWithin_congr
    (f := fun u : ℝ => cosmicKernel (fun y : ℝ => y ^ d) x u)
    (g := fun u : ℝ => powerKernel d x u)
    ?hEq
    ?hCosmic
  · intro u hu
    have hu0 : u ≠ 0 := by
      simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using hu
    exact cosmicKernel_pow_eq_powerKernel_of_ne_zero d x u hu0
  · exact tendsto_cosmicKernel_of_hasDerivAt (hasDerivAt_pow_cosmic d x)

end DkMath.CosmicFormula
