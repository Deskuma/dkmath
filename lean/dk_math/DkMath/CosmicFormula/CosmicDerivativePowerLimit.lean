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

/--
Continuity of `powerKernel` in the increment variable `u`.

Reason: `powerKernel` is a finite sum of polynomial terms in `u`.
-/
theorem continuous_powerKernel (d : ℕ) (x : ℝ) :
    Continuous (fun u : ℝ => powerKernel d x u) := by
  unfold powerKernel
  continuity

/--
Center value of the power kernel:
`powerKernel d x 0 = (d : ℝ) * x^(d-1)`.

This is the target derivative value of `y^d` at `x`.
-/
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

/--
Full-neighborhood limit:
`powerKernel d x u -> (d : ℝ) * x^(d-1)` as `u -> 0` in `nhds 0`.

Derived from continuity and the center-value identity.
-/
theorem tendsto_powerKernel_zero (d : ℕ) (x : ℝ) :
    Filter.Tendsto (fun u : ℝ => powerKernel d x u)
      (nhds (0 : ℝ))
      (nhds ((d : ℝ) * x ^ (d - 1))) := by
  simpa [powerKernel_zero] using (continuous_powerKernel d x).tendsto 0

/--
Punctured-neighborhood variant:
restrict the previous limit to `u ≠ 0`.
-/
theorem tendsto_powerKernel_zero_punctured (d : ℕ) (x : ℝ) :
    Filter.Tendsto (fun u : ℝ => powerKernel d x u)
      (nhdsWithin (0 : ℝ) (Set.compl ({(0 : ℝ)} : Set ℝ)))
      (nhds ((d : ℝ) * x ^ (d - 1))) :=
  (tendsto_powerKernel_zero d x).mono_left nhdsWithin_le_nhds

/--
Derivative theorem for powers via cosmic-kernel flow:
1. `cosmicKernel (y^d)` equals `powerKernel` on `u ≠ 0`,
2. `powerKernel` tends to `(d : ℝ) * x^(d-1)` as `u -> 0`,
3. apply `hasDerivAt_of_tendsto_cosmicKernel`.

Conclusion:
`HasDerivAt (fun y => y^d) ((d : ℝ) * x^(d-1)) x`.
-/
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
