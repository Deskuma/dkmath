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

/-- Full-neighborhood limit of `powerKernel` at `u → 0`. -/
theorem tendsto_powerKernel_zero (d : ℕ) (x : ℝ) :
    Filter.Tendsto (fun u : ℝ => powerKernel d x u)
      (nhds (0 : ℝ))
      (nhds ((d : ℝ) * x ^ (d - 1))) := by
  have hcont : Continuous (fun u : ℝ => powerKernel d x u) := by
    unfold powerKernel
    continuity
  have hzero : powerKernel d x 0 = (d : ℝ) * x ^ (d - 1) := by
    cases d with
    | zero =>
        simp [powerKernel]
    | succ n =>
        unfold powerKernel
        rw [Finset.sum_eq_single 0]
        · simp
        · intro j hj hj0
          simp [hj0]
        · simp
  simpa [hzero] using hcont.tendsto 0

/-- Punctured-neighborhood variant, derived from the full-neighborhood limit. -/
theorem tendsto_powerKernel_zero_punctured (d : ℕ) (x : ℝ) :
    Filter.Tendsto (fun u : ℝ => powerKernel d x u)
      (nhdsWithin (0 : ℝ) (Set.compl ({(0 : ℝ)} : Set ℝ)))
      (nhds ((d : ℝ) * x ^ (d - 1))) :=
  (tendsto_powerKernel_zero d x).mono_left nhdsWithin_le_nhds

end DkMath.CosmicFormula
