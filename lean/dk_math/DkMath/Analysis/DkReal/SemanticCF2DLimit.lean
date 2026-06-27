/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Analysis.DkReal.SemanticCF2DRefinement

#print "file: DkMath.Analysis.DkReal.SemanticCF2DLimit"

/-!
# First limit laws for dyadic phase-depth defects

The finite refinement layer gives exact closed forms:

* the defect introduced at level `n + 1` is `(1 / 2)^(n + 1)`;
* the cumulative defect through level `m - 1` is `1 - (1 / 2)^m`.

This module takes only the elementary geometric limits of those formulas.
It makes no Gaussian claim and does not select a composition law for boundary
normalization.
-/

namespace DkMath.Analysis.DkNNRealQ

/-- The total depth defect introduced at one refinement level tends to zero. -/
theorem tendsto_totalDyadicPhaseDepthDefect_zero :
    Filter.Tendsto totalDyadicPhaseDepthDefect Filter.atTop (nhds 0) := by
  have hpow :
      Filter.Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n)
        Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hscaled :
      Filter.Tendsto (fun n : ℕ => (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ n)
        Filter.atTop (nhds 0) := by
    simpa using hpow.const_mul (1 / 2 : ℝ)
  convert hscaled using 1
  funext n
  rw [totalDyadicPhaseDepthDefect_eq_pow, pow_succ]
  ring

/-- The cumulative finite depth defect tends to the normalized value one. -/
theorem tendsto_cumulativeDyadicPhaseDepthDefect_one :
    Filter.Tendsto cumulativeDyadicPhaseDepthDefect
      Filter.atTop (nhds 1) := by
  have hpow :
      Filter.Tendsto (fun m : ℕ => (1 / 2 : ℝ) ^ m)
        Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  convert (tendsto_const_nhds.sub hpow :
    Filter.Tendsto (fun m : ℕ => (1 : ℝ) - (1 / 2 : ℝ) ^ m)
      Filter.atTop (nhds (1 - 0))) using 1
  · funext m
    exact cumulativeDyadicPhaseDepthDefect_eq m
  · norm_num

end DkMath.Analysis.DkNNRealQ
