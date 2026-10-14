/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedFusionAllocationThreshold

#print "file: DkMathTest.FLT.Seven.AllocationThresholdCalibration"

namespace DkMathTest.FLT.Seven

open DkMath.FLT.Seven DkMath.CosmicFormulaBinom
open RamifiedSignedRootRoutingPacket.QuotientPrimeSupport

set_option exponentiation.threshold 512

/-- The GN strict comparison needs a positive endpoint. -/
theorem gn_zero_boundary : GN 7 (7 : ℕ) 0 = 7 ^ 6 := by
  rw [GN_seven_eq_gap_mul_add_seven_mul_y_pow_six]
  norm_num

theorem gn_positive_above_threshold : 7 ^ 6 < GN 7 (7 : ℕ) 1 :=
  GN_seven_gap_pow_six_lt (by decide)

/-- The zero-gap boundary remains valid for the GN inequality. -/
theorem gn_zero_gap_positive : 0 < GN 7 (0 : ℕ) 1 :=
  GN_seven_gap_pow_six_lt (D := 0) (u := 1) (by decide)

/-- Both alternating endpoints must be positive for strict inequality. -/
theorem alternating_zero_boundary : alternatingCyclotomicSeven 0 7 = 7 ^ 6 := by
  norm_num [alternatingCyclotomicSeven]

theorem alternating_positive_below_threshold : alternatingCyclotomicSeven 3 4 < 7 ^ 6 :=
  alternatingCyclotomicSeven_lt_sum_pow_six (by decide) (by decide)

theorem alternating_coarse_power_bound : 7 ^ 6 ≤ 64 * alternatingCyclotomicSeven 3 4 :=
  sum_pow_six_le_sixtyFour_mul_alternatingCyclotomicSeven (x := 3) (y := 4) (by decide)

theorem threshold_exponent_transport {M r s : ℕ} (hr : 0 < r) (hM : M = r * s) :
    ((7 ^ 27 * r ^ 49) ^ 6 < 7 * s ^ 49 ↔ 7 ^ 161 * r ^ 343 < M ^ 49) ∧
      (7 * s ^ 49 < (7 ^ 27 * r ^ 49) ^ 6 ↔ M ^ 49 < 7 ^ 161 * r ^ 343) :=
  nestedAllocation_threshold_comparisons hr hM

/-- Opposite sides occur for two coprime divisor allocations of a single
seven-unit core, even after the coarse filter. No endpoint solution is
asserted by these numerical threshold facts. -/
theorem opposite_supported_thresholds :
    Nat.Coprime 1 (64002 / 1) ∧ Nat.Coprime 2 (64002 / 2) ∧
      7 ^ 3 * 1 ^ 7 < (64002 : ℕ) ∧ 7 ^ 3 * 2 ^ 7 < (64002 : ℕ) ∧
      7 ^ 161 * 1 ^ 343 < (64002 : ℕ) ^ 49 ∧
      (64002 : ℕ) ^ 49 < 7 ^ 161 * 2 ^ 343 := by decide

theorem opposite_divisor_support :
    1 ∈ (64002 : ℕ).divisors ∧ 2 ∈ (64002 : ℕ).divisors := by
  constructor
  · exact Nat.mem_divisors.mpr ⟨by decide, by decide⟩
  · exact Nat.mem_divisors.mpr ⟨by decide, by decide⟩

theorem seven_unit_threshold_boundary_absent (r : ℕ) :
    (64002 : ℕ) ^ 49 ≠ 7 ^ 161 * r ^ 343 :=
  nestedAllocation_threshold_ne (by decide)

theorem fixed_allocation_disjoint {M r : ℕ} (hM : 0 < M) (hdiv : r ∣ M) :
    ¬ (NestedGNAllocationCondition M r ∧ NestedRHSAllocationCondition M r) :=
  nestedAllocation_branches_disjoint hM hdiv

theorem right_divisor_receiver (M : ℕ) (hM : 0 < M) :
    NestedRightHandSideCondition M ↔
      ∃ r ∈ M.divisors, Nat.Coprime r (M / r) ∧ NestedRHSAllocationCondition M r :=
  nestedRightHandSideCondition_iff_allocation M hM

theorem fixed_sum_product_value :
    (alternatingCyclotomicSeven 3 4 : ℤ) =
      7 ^ 6 - 7 * 7 ^ 4 * 12 + 14 * 7 ^ 2 * 12 ^ 2 - 7 * 12 ^ 3 :=
  alternatingCyclotomicSeven_fixed_sum_product 3 4

theorem combined_threshold_receiver (p : RamifiedSignedRootRoutingPacket) :
    InternalDepthFourCounterexampleReconstructionObligation p ↔
      ThresholdRoutedNestedCondition (internalDepthFourSeventhCore p) :=
  internalDepthFourReconstruction_iff_threshold_routed p

theorem small_source_core_excluded (p : RamifiedSignedRootRoutingPacket)
    (hM : internalDepthFourSeventhCore p ≤ 343) :
    ¬ InternalDepthFourCounterexampleReconstructionObligation p :=
  internalDepthFourReconstruction_false_of_core_le_343 p hM

end DkMathTest.FLT.Seven
