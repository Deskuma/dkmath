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
refinement-limit observable. The average and mesh-weighted variants below are
therefore recorded only as finite candidate observables: the same cancellation
law survives scalar reweighting, but no limiting interpretation is chosen here.
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

/--
The complete dyadic mesh has one more node than its dyadic denominator.

This is the finite bookkeeping distinction between complete node meshes and
midpoint or odd-child meshes.
-/
theorem dyadicPhaseNodeIndices_card (n : ℕ) :
    (dyadicPhaseNodeIndices n).card = dyadicPhaseDenom n + 1 := by
  simp [dyadicPhaseNodeIndices]

/--
Uniform average weight on the complete finite dyadic node mesh.

This is a finite candidate observable. It does not assert that the uniform
average is the canonical refinement-limit quantity.
-/
def dyadicPhaseAverageWeight (n : ℕ) : ℝ :=
  1 / ((dyadicPhaseNodeIndices n).card : ℝ)

/-- The complete finite dyadic mesh has a positive averaging weight. -/
theorem dyadicPhaseAverageWeight_pos (n : ℕ) :
    0 < dyadicPhaseAverageWeight n := by
  have hcard : 0 < (dyadicPhaseNodeIndices n).card := by
    rw [dyadicPhaseNodeIndices_card]
    exact Nat.succ_pos _
  exact one_div_pos.2 (by exact_mod_cast hcard)

/-- Uniform average of logarithmic depth observations on the complete mesh. -/
def dyadicPhaseAverageLogDepth (n : ℕ) : ℝ :=
  dyadicPhaseAverageWeight n * dyadicPhaseLogDepthSum n

/--
Uniform average of logarithmic normalization observations on the complete
mesh.
-/
def dyadicPhaseAverageLogNormalization (n : ℕ) : ℝ :=
  dyadicPhaseAverageWeight n * dyadicPhaseLogNormalizationSum n

/-- Finite logarithmic cancellation survives uniform averaging. -/
theorem two_mul_dyadicPhaseAverageLogNormalization_add_averageLogDepth
    (n : ℕ) :
    2 * dyadicPhaseAverageLogNormalization n +
        dyadicPhaseAverageLogDepth n = 0 := by
  calc
    2 * dyadicPhaseAverageLogNormalization n +
        dyadicPhaseAverageLogDepth n
        = dyadicPhaseAverageWeight n *
            (2 * dyadicPhaseLogNormalizationSum n +
              dyadicPhaseLogDepthSum n) := by
          rw [dyadicPhaseAverageLogNormalization,
            dyadicPhaseAverageLogDepth]
          ring
    _ = 0 := by
      rw [two_mul_dyadicPhaseLogNormalizationSum_add_logDepthSum]
      simp

/--
Mesh width of the dyadic subdivision.

This is the natural scalar for finite Riemann-style candidates on the complete
node mesh. Endpoint weights are deliberately not chosen here.
-/
def dyadicPhaseMeshWeight (n : ℕ) : ℝ :=
  1 / (dyadicPhaseDenom n : ℝ)

/-- The dyadic mesh width is positive. -/
theorem dyadicPhaseMeshWeight_pos (n : ℕ) :
    0 < dyadicPhaseMeshWeight n := by
  exact one_div_pos.2 (by exact_mod_cast dyadicPhaseDenom_pos n)

/-- Mesh-weighted finite log-depth sum. -/
def dyadicPhaseWeightedLogDepthSum (n : ℕ) : ℝ :=
  dyadicPhaseMeshWeight n * dyadicPhaseLogDepthSum n

/-- Mesh-weighted finite log-normalization sum. -/
def dyadicPhaseWeightedLogNormalizationSum (n : ℕ) : ℝ :=
  dyadicPhaseMeshWeight n * dyadicPhaseLogNormalizationSum n

/--
Finite logarithmic cancellation survives mesh-width weighting.

This is only a finite scalar transport of the log-sum identity; it does not
assert that the mesh-weighted quantity is the canonical limit observable.
-/
theorem two_mul_dyadicPhaseWeightedLogNormalizationSum_add_weightedLogDepthSum
    (n : ℕ) :
    2 * dyadicPhaseWeightedLogNormalizationSum n +
        dyadicPhaseWeightedLogDepthSum n = 0 := by
  calc
    2 * dyadicPhaseWeightedLogNormalizationSum n +
        dyadicPhaseWeightedLogDepthSum n
        = dyadicPhaseMeshWeight n *
            (2 * dyadicPhaseLogNormalizationSum n +
              dyadicPhaseLogDepthSum n) := by
          rw [dyadicPhaseWeightedLogNormalizationSum,
            dyadicPhaseWeightedLogDepthSum]
          ring
    _ = 0 := by
      rw [two_mul_dyadicPhaseLogNormalizationSum_add_logDepthSum]
      simp

end

end DkMath.Analysis.DkNNRealQ
