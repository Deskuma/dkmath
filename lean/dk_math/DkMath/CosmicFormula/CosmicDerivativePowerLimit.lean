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

/-- `powerKernel` is continuous in `u`. -/
theorem continuous_powerKernel (d : ℕ) (x : ℝ) :
    Continuous (fun u : ℝ => powerKernel d x u) := by
  unfold powerKernel
  continuity

/-- Evaluation of `powerKernel` at `u = 0`. -/
theorem powerKernel_zero (d : ℕ) (x : ℝ) :
    powerKernel d x 0 = (d : ℝ) * x ^ (d - 1) := by
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

/-- Full-neighborhood limit of `powerKernel` at `u → 0`. -/
theorem tendsto_powerKernel_zero (d : ℕ) (x : ℝ) :
    Filter.Tendsto (fun u : ℝ => powerKernel d x u)
      (nhds (0 : ℝ))
      (nhds ((d : ℝ) * x ^ (d - 1))) := by
  simpa [powerKernel_zero] using (continuous_powerKernel d x).tendsto 0

/-- Punctured-neighborhood variant, derived from the full-neighborhood limit. -/
theorem tendsto_powerKernel_zero_punctured (d : ℕ) (x : ℝ) :
    Filter.Tendsto (fun u : ℝ => powerKernel d x u)
      (nhdsWithin (0 : ℝ) (Set.compl ({(0 : ℝ)} : Set ℝ)))
      (nhds ((d : ℝ) * x ^ (d - 1))) :=
  (tendsto_powerKernel_zero d x).mono_left nhdsWithin_le_nhds

/-- Power-function derivative theorem reconstructed via cosmic-kernel flow. -/
theorem hasDerivAt_pow_cosmic (d : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => y ^ d) ((d : ℝ) * x ^ (d - 1)) x := by
  have hpow :
      Filter.Tendsto (fun u : ℝ => powerKernel d x u)
        (nhdsWithin (0 : ℝ) (Set.compl ({(0 : ℝ)} : Set ℝ)))
        (nhds ((d : ℝ) * x ^ (d - 1))) :=
    tendsto_powerKernel_zero_punctured d x
  have hcosmic :
      Filter.Tendsto (fun u : ℝ => cosmicKernel (fun y : ℝ => y ^ d) x u)
        (nhdsWithin (0 : ℝ) (Set.compl ({(0 : ℝ)} : Set ℝ)))
        (nhds ((d : ℝ) * x ^ (d - 1))) := by
    refine tendsto_nhdsWithin_congr ?hEq hpow
    intro u hu
    have hu0 : u ≠ 0 := by
      simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using hu
    exact (cosmicKernel_pow_eq_powerKernel_of_ne_zero d x u hu0).symm
  exact hasDerivAt_of_tendsto_cosmicKernel hcosmic

end DkMath.CosmicFormula
