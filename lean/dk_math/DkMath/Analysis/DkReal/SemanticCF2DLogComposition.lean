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
The trapezoidal candidate records the standard closed-interval endpoint
half-weight pattern as another finite observable, again without selecting a
limit.
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

/-- The logarithmic depth observation vanishes at the left endpoint. -/
@[simp]
theorem log_dyadicPhaseDepth_left_endpoint (n : ℕ) :
    Real.log (dyadicPhaseDepth n 0) = 0 := by
  simp [dyadicPhaseDepth]

/-- The logarithmic depth observation vanishes at the right endpoint. -/
@[simp]
theorem log_dyadicPhaseDepth_right_endpoint (n : ℕ) :
    Real.log (dyadicPhaseDepth n (dyadicPhaseDenom n)) = 0 := by
  simp [dyadicPhaseDepth]

/-- The logarithmic normalization observation vanishes at the left endpoint. -/
@[simp]
theorem log_dyadicPhaseNormalization_left_endpoint (n : ℕ) :
    Real.log (dyadicPhaseNormalization n 0) = 0 := by
  simp [dyadicPhaseNormalization]

/-- The logarithmic normalization observation vanishes at the right endpoint. -/
@[simp]
theorem log_dyadicPhaseNormalization_right_endpoint (n : ℕ) :
    Real.log (dyadicPhaseNormalization n (dyadicPhaseDenom n)) = 0 := by
  simp [dyadicPhaseNormalization]

/--
Centered logarithmic phase-depth increment.

The baseline is the midpoint depth `1 / 2`. This is the first finite
observable whose endpoint values no longer vanish, so endpoint corrections
become visible again.
-/
def centeredLogPhaseDepth (t : ℝ) : ℝ :=
  Real.log (phaseDepth t) - Real.log (1 / 2 : ℝ)

/-- Dyadic samples of the centered logarithmic phase-depth increment. -/
def dyadicPhaseCenteredLogDepth (n k : ℕ) : ℝ :=
  centeredLogPhaseDepth (dyadicPhaseNode n k)

/-- The midpoint baseline makes the centered log-depth increment vanish. -/
@[simp]
theorem centeredLogPhaseDepth_half :
    centeredLogPhaseDepth (1 / 2 : ℝ) = 0 := by
  rw [centeredLogPhaseDepth, phaseDepth_half]
  ring

/-- The left endpoint centered log-depth increment is `log 2`. -/
@[simp]
theorem centeredLogPhaseDepth_zero :
    centeredLogPhaseDepth 0 = Real.log (2 : ℝ) := by
  have hhalf : Real.log (1 / 2 : ℝ) = -Real.log (2 : ℝ) := by
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [centeredLogPhaseDepth, phaseDepth_zero, hhalf, Real.log_one]
  ring

/-- The right endpoint centered log-depth increment is `log 2`. -/
@[simp]
theorem centeredLogPhaseDepth_one :
    centeredLogPhaseDepth 1 = Real.log (2 : ℝ) := by
  have hhalf : Real.log (1 / 2 : ℝ) = -Real.log (2 : ℝ) := by
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [centeredLogPhaseDepth, phaseDepth_one, hhalf, Real.log_one]
  ring

/--
The centered log-depth increment is the logarithm of an explicit centered
quadratic profile.

This is still a finite algebraic observation. It identifies the quadratic
shape that will later be compared with Gaussian-type kernels, without
asserting a Gaussian limit.
-/
theorem centeredLogPhaseDepth_eq_log_one_add_four_sq (t : ℝ) :
    centeredLogPhaseDepth t =
      Real.log (1 + 4 * (t - (1 / 2 : ℝ)) ^ 2) := by
  unfold centeredLogPhaseDepth
  rw [← Real.log_div (phaseDepth_pos t).ne' (by norm_num : (1 / 2 : ℝ) ≠ 0)]
  congr
  rw [phaseDepth_eq_two_sq_add_half]
  ring

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
Pointwise weighted finite logarithmic cancellation.

Every weight function on the complete finite mesh preserves the cancellation
law because the cancellation already holds at each sampled node. This is the
finite algebraic form needed before choosing any particular observable such as
an average, a mesh-width sum, or a trapezoidal sum.
-/
theorem two_mul_weightedLogNormalizationSum_add_weightedLogDepthSum
    (n : ℕ) (w : ℕ → ℝ) :
    2 * (∑ k ∈ dyadicPhaseNodeIndices n,
          w k * Real.log (dyadicPhaseNormalization n k)) +
        (∑ k ∈ dyadicPhaseNodeIndices n,
          w k * Real.log (dyadicPhaseDepth n k)) = 0 := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_eq_zero fun k hk => by
    calc
      2 * (w k * Real.log (dyadicPhaseNormalization n k)) +
          w k * Real.log (dyadicPhaseDepth n k)
          = w k *
              (2 * Real.log (dyadicPhaseNormalization n k) +
                Real.log (dyadicPhaseDepth n k)) := by
            ring
      _ = 0 := by
        rw [two_mul_log_dyadicPhaseNormalization_add_log_depth n k]
        simp

/--
Short API name for pointwise weighted logarithmic boundary cancellation.

This alias is intended for downstream candidate observables where the weight
choice is the main object of study.
-/
theorem dyadicPhaseWeightedLogCancellation
    (n : ℕ) (w : ℕ → ℝ) :
    2 * (∑ k ∈ dyadicPhaseNodeIndices n,
          w k * Real.log (dyadicPhaseNormalization n k)) +
        (∑ k ∈ dyadicPhaseNodeIndices n,
          w k * Real.log (dyadicPhaseDepth n k)) = 0 :=
  two_mul_weightedLogNormalizationSum_add_weightedLogDepthSum n w

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

/-- The uniform average weights on the complete dyadic mesh have total mass one. -/
theorem sum_dyadicPhaseAverageWeight_eq_one (n : ℕ) :
    ∑ _k ∈ dyadicPhaseNodeIndices n, dyadicPhaseAverageWeight n = 1 := by
  have hcard_nat : 0 < (dyadicPhaseNodeIndices n).card := by
    rw [dyadicPhaseNodeIndices_card]
    exact Nat.succ_pos _
  have hcard_pos : (0 : ℝ) < (dyadicPhaseNodeIndices n).card := by
    exact_mod_cast hcard_nat
  simp [dyadicPhaseAverageWeight]
  field_simp [(ne_of_gt hcard_pos)]

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

/--
The complete-node mesh-width weights have total mass `1 + h_n`.

This records the endpoint overcount of the plain complete-node mesh-width
candidate relative to a closed-interval integration rule.
-/
theorem sum_dyadicPhaseMeshWeight_eq_one_add (n : ℕ) :
    ∑ _k ∈ dyadicPhaseNodeIndices n, dyadicPhaseMeshWeight n =
      1 + dyadicPhaseMeshWeight n := by
  have hdenom : (dyadicPhaseDenom n : ℝ) ≠ 0 := by
    exact_mod_cast (dyadicPhaseDenom_pos n).ne'
  simp [dyadicPhaseNodeIndices, dyadicPhaseMeshWeight]
  field_simp [hdenom]

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

/--
Trapezoidal weight on the complete finite dyadic node mesh.

The endpoints receive half a mesh width and every interior node receives one
mesh width. This is a finite closed-interval integration candidate only; no
convergence or canonical-observable statement is made here.
-/
def dyadicPhaseTrapezoidWeight (n k : ℕ) : ℝ :=
  if k = 0 ∨ k = dyadicPhaseDenom n then
    dyadicPhaseMeshWeight n / 2
  else
    dyadicPhaseMeshWeight n

/-- Every trapezoidal mesh weight is positive. -/
theorem dyadicPhaseTrapezoidWeight_pos (n k : ℕ) :
    0 < dyadicPhaseTrapezoidWeight n k := by
  unfold dyadicPhaseTrapezoidWeight
  split_ifs
  · exact div_pos (dyadicPhaseMeshWeight_pos n) (by norm_num)
  · exact dyadicPhaseMeshWeight_pos n

/--
The endpoint set of the complete dyadic mesh consists of the two boundary
indices `0` and `2^n`.
-/
theorem dyadicPhaseEndpointFilter_eq (n : ℕ) :
    (dyadicPhaseNodeIndices n).filter
        (fun k => k = 0 ∨ k = dyadicPhaseDenom n) =
      {0, dyadicPhaseDenom n} := by
  ext k
  constructor
  · intro hk
    exact by
      simp only [Finset.mem_filter] at hk
      simpa using hk.2
  · intro hk
    have hdenom_pos := dyadicPhaseDenom_pos n
    have hk' : k = 0 ∨ k = dyadicPhaseDenom n := by
      simpa using hk
    simp only [Finset.mem_filter]
    constructor
    · simp only [dyadicPhaseNodeIndices, Finset.mem_range,
        Nat.lt_succ_iff]
      rcases hk' with rfl | rfl
      · exact Nat.zero_le _
      · exact le_rfl
    · exact hk'

/--
The trapezoidal weights on the complete dyadic node mesh have total mass one.

This is the finite closed-interval bookkeeping property: two endpoints have
half mesh width and all interior nodes have full mesh width.
-/
theorem sum_dyadicPhaseTrapezoidWeight_eq_one (n : ℕ) :
    ∑ k ∈ dyadicPhaseNodeIndices n, dyadicPhaseTrapezoidWeight n k = 1 := by
  have hmesh :
      ∑ _k ∈ dyadicPhaseNodeIndices n, dyadicPhaseMeshWeight n =
        1 + dyadicPhaseMeshWeight n :=
    sum_dyadicPhaseMeshWeight_eq_one_add n
  have hend :
      ∑ k ∈ dyadicPhaseNodeIndices n,
          (if k = 0 ∨ k = dyadicPhaseDenom n then
            dyadicPhaseMeshWeight n / 2
          else
            0) =
        dyadicPhaseMeshWeight n := by
    rw [← Finset.sum_filter]
    rw [dyadicPhaseEndpointFilter_eq]
    have hdistinct : (0 : ℕ) ≠ dyadicPhaseDenom n :=
      (dyadicPhaseDenom_pos n).ne
    simp [hdistinct]
    ring
  calc
    ∑ k ∈ dyadicPhaseNodeIndices n, dyadicPhaseTrapezoidWeight n k
        = (∑ _k ∈ dyadicPhaseNodeIndices n, dyadicPhaseMeshWeight n) -
            ∑ k ∈ dyadicPhaseNodeIndices n,
              (if k = 0 ∨ k = dyadicPhaseDenom n then
                dyadicPhaseMeshWeight n / 2
              else
                0) := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro k hk
          unfold dyadicPhaseTrapezoidWeight
          by_cases hendpoint : k = 0 ∨ k = dyadicPhaseDenom n
          · rw [if_pos hendpoint]
            simp [hendpoint]
            ring_nf
          · rw [if_neg hendpoint]
            simp [hendpoint]
    _ = 1 := by
      rw [hmesh, hend]
      ring

/--
Plain mesh-width and trapezoidal finite sums differ only by the half-width
endpoint correction.

This theorem separates the choice of finite weights from the sampled
observable `f`. It is the general bookkeeping identity behind the later
special cases where endpoint logarithms vanish.
-/
theorem dyadicPhaseMeshWeight_sum_sub_trapezoid_sum_eq_endpoint_half
    (n : ℕ) (f : ℕ → ℝ) :
    (∑ k ∈ dyadicPhaseNodeIndices n, dyadicPhaseMeshWeight n * f k) -
        (∑ k ∈ dyadicPhaseNodeIndices n,
          dyadicPhaseTrapezoidWeight n k * f k) =
      dyadicPhaseMeshWeight n / 2 *
        (f 0 + f (dyadicPhaseDenom n)) := by
  calc
    (∑ k ∈ dyadicPhaseNodeIndices n, dyadicPhaseMeshWeight n * f k) -
        (∑ k ∈ dyadicPhaseNodeIndices n,
          dyadicPhaseTrapezoidWeight n k * f k)
        = ∑ k ∈ dyadicPhaseNodeIndices n,
            (dyadicPhaseMeshWeight n * f k -
              dyadicPhaseTrapezoidWeight n k * f k) := by
          rw [Finset.sum_sub_distrib]
    _ = ∑ k ∈ dyadicPhaseNodeIndices n,
          (if k = 0 ∨ k = dyadicPhaseDenom n then
            dyadicPhaseMeshWeight n / 2 * f k
          else
            0) := by
        apply Finset.sum_congr rfl
        intro k hk
        unfold dyadicPhaseTrapezoidWeight
        by_cases hendpoint : k = 0 ∨ k = dyadicPhaseDenom n
        · rw [if_pos hendpoint]
          simp [hendpoint]
          ring_nf
        · rw [if_neg hendpoint]
          simp [hendpoint]
    _ = dyadicPhaseMeshWeight n / 2 *
        (f 0 + f (dyadicPhaseDenom n)) := by
        rw [← Finset.sum_filter]
        rw [dyadicPhaseEndpointFilter_eq]
        have hdistinct : (0 : ℕ) ≠ dyadicPhaseDenom n :=
          (dyadicPhaseDenom_pos n).ne
        simp [hdistinct]
        ring

/--
If a sampled observable vanishes at both endpoints, then the plain mesh-width
sum and the trapezoidal sum agree.

This is the zero-endpoint corollary of the half-width endpoint correction
formula. It is useful for boundary-log observables, and it will also isolate
where centered observables differ from them.
-/
theorem dyadicPhaseMeshWeight_sum_eq_trapezoid_sum_of_endpoint_zero
    (n : ℕ) (f : ℕ → ℝ)
    (h0 : f 0 = 0)
    (h1 : f (dyadicPhaseDenom n) = 0) :
    (∑ k ∈ dyadicPhaseNodeIndices n, dyadicPhaseMeshWeight n * f k) =
      ∑ k ∈ dyadicPhaseNodeIndices n,
        dyadicPhaseTrapezoidWeight n k * f k := by
  have h :=
    dyadicPhaseMeshWeight_sum_sub_trapezoid_sum_eq_endpoint_half n f
  rw [h0, h1] at h
  have hzero :
      (∑ k ∈ dyadicPhaseNodeIndices n, dyadicPhaseMeshWeight n * f k) -
          (∑ k ∈ dyadicPhaseNodeIndices n,
            dyadicPhaseTrapezoidWeight n k * f k) = 0 := by
    have hright : dyadicPhaseMeshWeight n / 2 * (0 + 0) = 0 := by ring
    rw [hright] at h
    exact h
  exact sub_eq_zero.mp hzero

/-- Trapezoidal finite log-depth sum on the complete dyadic node mesh. -/
def dyadicPhaseTrapezoidLogDepthSum (n : ℕ) : ℝ :=
  ∑ k ∈ dyadicPhaseNodeIndices n,
    dyadicPhaseTrapezoidWeight n k * Real.log (dyadicPhaseDepth n k)

/--
Trapezoidal finite log-normalization sum on the complete dyadic node mesh.
-/
def dyadicPhaseTrapezoidLogNormalizationSum (n : ℕ) : ℝ :=
  ∑ k ∈ dyadicPhaseNodeIndices n,
    dyadicPhaseTrapezoidWeight n k *
      Real.log (dyadicPhaseNormalization n k)

/--
Finite logarithmic cancellation survives trapezoidal endpoint weighting.

This is an application of pointwise weighted cancellation. It records a
standard closed-interval finite candidate without asserting that this is the
canonical refinement limit.
-/
theorem two_mul_dyadicPhaseTrapezoidLogNormalizationSum_add_trapezoidLogDepthSum
    (n : ℕ) :
    2 * dyadicPhaseTrapezoidLogNormalizationSum n +
        dyadicPhaseTrapezoidLogDepthSum n = 0 := by
  rw [dyadicPhaseTrapezoidLogNormalizationSum,
    dyadicPhaseTrapezoidLogDepthSum]
  exact two_mul_weightedLogNormalizationSum_add_weightedLogDepthSum
    n (dyadicPhaseTrapezoidWeight n)

/--
Plain mesh-width and trapezoidal log-depth sums agree on the complete mesh.

Although the total masses of the two weights differ, the discrepancy is
supported only at the two endpoints, where the logarithmic depth observation
is zero.
-/
theorem dyadicPhaseWeightedLogDepthSum_eq_trapezoidLogDepthSum (n : ℕ) :
    dyadicPhaseWeightedLogDepthSum n =
      dyadicPhaseTrapezoidLogDepthSum n := by
  rw [dyadicPhaseWeightedLogDepthSum, dyadicPhaseLogDepthSum,
    dyadicPhaseTrapezoidLogDepthSum, Finset.mul_sum]
  exact dyadicPhaseMeshWeight_sum_eq_trapezoid_sum_of_endpoint_zero n
    (fun k => Real.log (dyadicPhaseDepth n k))
    (by simp) (by simp)

/--
Plain mesh-width and trapezoidal log-normalization sums agree on the complete
mesh.

As for depth, the endpoint correction has no logarithmic contribution because
the normalization factor is one at both endpoints.
-/
theorem dyadicPhaseWeightedLogNormalizationSum_eq_trapezoidLogNormalizationSum
    (n : ℕ) :
    dyadicPhaseWeightedLogNormalizationSum n =
      dyadicPhaseTrapezoidLogNormalizationSum n := by
  rw [dyadicPhaseWeightedLogNormalizationSum, dyadicPhaseLogNormalizationSum,
    dyadicPhaseTrapezoidLogNormalizationSum, Finset.mul_sum]
  exact dyadicPhaseMeshWeight_sum_eq_trapezoid_sum_of_endpoint_zero n
    (fun k => Real.log (dyadicPhaseNormalization n k))
    (by simp) (by simp)

/-- Plain mesh-width finite sum of centered log-depth observations. -/
def dyadicPhaseMeshWeightedCenteredLogDepthSum (n : ℕ) : ℝ :=
  ∑ k ∈ dyadicPhaseNodeIndices n,
    dyadicPhaseMeshWeight n * dyadicPhaseCenteredLogDepth n k

/-- Trapezoidal finite sum of centered log-depth observations. -/
def dyadicPhaseTrapezoidCenteredLogDepthSum (n : ℕ) : ℝ :=
  ∑ k ∈ dyadicPhaseNodeIndices n,
    dyadicPhaseTrapezoidWeight n k * dyadicPhaseCenteredLogDepth n k

/--
For centered log-depth, the plain mesh-width and trapezoidal sums differ by
the restored endpoint correction `h_n * log 2`.

Boundary logs had zero endpoint values, so their correction vanished. Centered
log-depth has endpoint value `log 2`, making the same finite endpoint
correction visible again.
-/
theorem dyadicPhaseMeshWeightedCenteredLogDepthSum_sub_trapezoidCenteredLogDepthSum
    (n : ℕ) :
    dyadicPhaseMeshWeightedCenteredLogDepthSum n -
        dyadicPhaseTrapezoidCenteredLogDepthSum n =
      dyadicPhaseMeshWeight n * Real.log (2 : ℝ) := by
  rw [dyadicPhaseMeshWeightedCenteredLogDepthSum,
    dyadicPhaseTrapezoidCenteredLogDepthSum]
  calc
    (∑ k ∈ dyadicPhaseNodeIndices n,
        dyadicPhaseMeshWeight n * dyadicPhaseCenteredLogDepth n k) -
        (∑ k ∈ dyadicPhaseNodeIndices n,
          dyadicPhaseTrapezoidWeight n k *
            dyadicPhaseCenteredLogDepth n k)
        = dyadicPhaseMeshWeight n / 2 *
            (dyadicPhaseCenteredLogDepth n 0 +
              dyadicPhaseCenteredLogDepth n (dyadicPhaseDenom n)) := by
          exact dyadicPhaseMeshWeight_sum_sub_trapezoid_sum_eq_endpoint_half
            n (dyadicPhaseCenteredLogDepth n)
    _ = dyadicPhaseMeshWeight n * Real.log (2 : ℝ) := by
      simp [dyadicPhaseCenteredLogDepth]
      ring

end

end DkMath.Analysis.DkNNRealQ
