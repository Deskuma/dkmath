/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Analysis.DkReal.SemanticCF2DComposition

#print "file: DkMath.Analysis.DkReal.SemanticCF2DLogComposition"

/-!
# Finite logarithmic form of dyadic boundary cancellation

All sampled depths and normalizations are strictly positive. Their finite
products may therefore be transferred to additive logarithmic sums.

The resulting identity

`2 * logNormalizationSum + logDepthSum = 0`

is exactly equivalent to the previously proved finite product cancellation.
This module still does not select a logarithmic sum as the canonical
refinement-limit observable.
-/

namespace DkMath.Analysis.DkNNRealQ

noncomputable section

/-- Pointwise positivity of the dyadic phase-depth observation. -/
theorem dyadicPhaseDepth_pos (n k : ℕ) :
    0 < dyadicPhaseDepth n k :=
  phaseDepth_pos (dyadicPhaseNode n k)

/-- Pointwise positivity of the dyadic normalization observation. -/
theorem dyadicPhaseNormalization_pos (n k : ℕ) :
    0 < dyadicPhaseNormalization n k :=
  phaseNormalization_pos (dyadicPhaseNode n k)

/-- Finite sum of logarithmic depth observations over the complete mesh. -/
def dyadicPhaseLogDepthSum (n : ℕ) : ℝ :=
  ∑ k ∈ dyadicPhaseNodeIndices n, Real.log (dyadicPhaseDepth n k)

/-- Finite sum of logarithmic normalization observations over the complete mesh. -/
def dyadicPhaseLogNormalizationSum (n : ℕ) : ℝ :=
  ∑ k ∈ dyadicPhaseNodeIndices n, Real.log (dyadicPhaseNormalization n k)

/-- Pointwise boundary cancellation in additive logarithmic form. -/
theorem two_mul_log_dyadicPhaseNormalization_add_log_depth
    (n k : ℕ) :
    2 * Real.log (dyadicPhaseNormalization n k) +
        Real.log (dyadicPhaseDepth n k) = 0 := by
  have h := congrArg Real.log
    (dyadicPhaseNormalization_sq_mul_depth n k)
  rw [Real.log_mul
      (pow_ne_zero 2 (dyadicPhaseNormalization_pos n k).ne')
      (dyadicPhaseDepth_pos n k).ne',
    Real.log_pow, Real.log_one] at h
  norm_num at h ⊢
  linarith

/-- The finite log-depth sum is the logarithm of the finite depth product. -/
theorem log_dyadicPhaseDepthProduct (n : ℕ) :
    Real.log (dyadicPhaseDepthProduct n) =
      dyadicPhaseLogDepthSum n := by
  rw [dyadicPhaseDepthProduct, dyadicPhaseLogDepthSum]
  exact Real.log_prod fun k _ => (dyadicPhaseDepth_pos n k).ne'

/--
The finite log-normalization sum is the logarithm of the finite
normalization product.
-/
theorem log_dyadicPhaseNormalizationProduct (n : ℕ) :
    Real.log (dyadicPhaseNormalizationProduct n) =
      dyadicPhaseLogNormalizationSum n := by
  rw [dyadicPhaseNormalizationProduct, dyadicPhaseLogNormalizationSum]
  exact Real.log_prod fun k _ => (dyadicPhaseNormalization_pos n k).ne'

/-- Finite boundary cancellation in additive logarithmic form. -/
theorem two_mul_dyadicPhaseLogNormalizationSum_add_logDepthSum
  (n : ℕ) :
    2 * dyadicPhaseLogNormalizationSum n +
        dyadicPhaseLogDepthSum n = 0 := by
  rw [dyadicPhaseLogNormalizationSum, dyadicPhaseLogDepthSum,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_eq_zero fun k hk =>
    two_mul_log_dyadicPhaseNormalization_add_log_depth n k

end

end DkMath.Analysis.DkNNRealQ
