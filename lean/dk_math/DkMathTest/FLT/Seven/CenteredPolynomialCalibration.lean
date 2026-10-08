/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedFusionCenteredPolynomial
import DkMathTest.FLT.Seven.SixthPowerAllocationSieveCalibration

#print "file: DkMathTest.FLT.Seven.CenteredPolynomialCalibration"

namespace DkMathTest.FLT.Seven

open DkMath.FLT.Seven DkMath.CosmicFormulaBinom
open RamifiedSignedRootRoutingPacket.QuotientPrimeSupport

set_option exponentiation.threshold 512

theorem alternating_midpoint_value :
    alternatingCyclotomicSeven 1 1 = 1 ∧ centeredSevenSextic 2 0 = 64 ∧
      64 * alternatingCyclotomicSeven 1 1 = centeredSevenSextic 2 (1 - 1) := by decide

theorem gn_zero_endpoint_boundary :
    GN 7 1 0 = 1 ∧ centeredSevenSextic 1 1 = 64 ∧
      64 * GN 7 1 0 = centeredSevenSextic 1 (1 + 2 * 0) := by decide

theorem positive_gn_endpoint_value :
    GN 7 1 1 = 127 ∧ centeredSevenSextic 1 3 = 8128 ∧
      64 * GN 7 1 1 = centeredSevenSextic 1 (1 + 2 * 1) := by decide

theorem unequal_ordered_alternating_value :
    alternatingCyclotomicSeven 1 2 = 43 ∧ centeredSevenSextic 3 1 = 2752 ∧
      64 * alternatingCyclotomicSeven 1 2 = centeredSevenSextic 3 (2 - 1) := by decide

theorem swapped_endpoints_keep_residual :
    alternatingCyclotomicSeven 1 2 = alternatingCyclotomicSeven 2 1 ∧
      (1 : ℕ) ≠ 2 := by decide

/-- Dropping the order premise and truncating the signed difference fails. -/
theorem truncated_swapped_coordinate_is_wrong :
    ¬ 64 * alternatingCyclotomicSeven 2 1 = centeredSevenSextic 3 (1 - 2) := by decide

theorem zero_gap_identity_needs_no_division :
    GN 7 0 1 = 7 ∧ 64 * GN 7 0 1 = centeredSevenSextic 0 2 := by decide

theorem signed_chart_value :
    64 * (((-1 : ℤ) + 3) ^ 7 - (-1 : ℤ) ^ 7) =
      3 * (7 * (2 * (-1 : ℤ) + 3) ^ 6 + 35 * 3 ^ 2 * (2 * (-1 : ℤ) + 3) ^ 4 +
        21 * 3 ^ 4 * (2 * (-1 : ℤ) + 3) ^ 2 + 3 ^ 6) :=
  centered_seventh_power_difference (-1) 3

theorem center_is_strictly_increasing (D : ℕ) : StrictMono (centeredSevenSextic D) :=
  centeredSevenSextic_strictMono D

theorem shared_center_target_unique {D q₁ q₂ target : ℕ}
    (h₁ : centeredSevenSextic D q₁ = target) (h₂ : centeredSevenSextic D q₂ = target) :
    q₁ = q₂ := centeredSevenSextic_target_unique h₁ h₂

theorem gn_uniqueness_regression {r s u v : ℕ}
    (hu : GN 7 (7 ^ 27 * r ^ 49) u = 7 * s ^ 49)
    (hv : GN 7 (7 ^ 27 * r ^ 49) v = 7 * s ^ 49) : u = v :=
  GN_seven_endpoint_unique_via_center hu hv

theorem old_gn_endpoint_unique_retained {r s u v : ℕ}
    (hu : GN 7 (7 ^ 27 * r ^ 49) u = 7 * s ^ 49)
    (hv : GN 7 (7 ^ 27 * r ^ 49) v = 7 * s ^ 49) : u = v :=
  nestedResidual_unit_unique hu hv

theorem center_position_is_old_threshold {M r s q : ℕ} (hr : 0 < r)
    (hM : M = r * s)
    (hP : centeredSevenSextic (7 ^ 27 * r ^ 49) q = 64 * (7 * s ^ 49)) :
    (7 ^ 27 * r ^ 49 < q ↔ 7 ^ 161 * r ^ 343 < M ^ 49) ∧
      (q < 7 ^ 27 * r ^ 49 ↔ M ^ 49 < 7 ^ 161 * r ^ 343) :=
  nestedCentered_allocation_threshold hr hM hP

theorem alternating_ordered_uniqueness_regression {D u v u' v' target : ℕ}
    (hsum : u + v = D) (hsum' : u' + v' = D) (horder : u ≤ v) (horder' : u' ≤ v')
    (hAlt : alternatingCyclotomicSeven u v = target)
    (hAlt' : alternatingCyclotomicSeven u' v' = target) : u = u' ∧ v = v' :=
  alternatingCyclotomicSeven_ordered_endpoint_unique hsum hsum' horder horder' hAlt hAlt'

theorem midpoint_ordered_pair_unique {u v : ℕ} (hsum : u + v = 2) (horder : u ≤ v)
    (hAlt : alternatingCyclotomicSeven u v = 1) : u = 1 ∧ v = 1 :=
  alternatingCyclotomicSeven_ordered_endpoint_unique hsum (by decide) horder
    (by decide : (1 : ℕ) ≤ 1) hAlt (by decide)

theorem candidate_keeps_parity {M r q : ℕ} (h : CenteredNestedAllocationCandidate M r q) :
    Nat.ModEq 2 q (7 ^ 27 * r ^ 49) := h.1

theorem degenerate_center_not_candidate (M r : ℕ) :
    ¬ CenteredNestedAllocationCandidate M r (7 ^ 27 * r ^ 49) :=
  fun h => centeredNestedAllocationCandidate_ne_gap h rfl

theorem canonical_candidate_unique_across_charts {M r q₁ q₂ : ℕ}
    (h₁ : CenteredNestedAllocationCandidate M r q₁)
    (h₂ : CenteredNestedAllocationCandidate M r q₂) : q₁ = q₂ :=
  centeredNestedAllocationCandidate_unique h₁ h₂

theorem gn_chart_reconstruction (M r : ℕ) :
    NestedGNAllocationCondition M r ↔
      ∃ q : ℕ, CenteredNestedAllocationCandidate M r q ∧ 7 ^ 27 * r ^ 49 < q :=
  nestedGNAllocation_iff_centered M r

theorem alternating_chart_reconstruction (M r : ℕ) :
    NestedRHSAllocationCondition M r ↔
      ∃ q : ℕ, CenteredNestedAllocationCandidate M r q ∧ q < 7 ^ 27 * r ^ 49 :=
  nestedRHSAllocation_iff_centered M r

/-- The old allocation retains filters; no endpoint or center is invented. -/
theorem old_one_allocation_still_has_support :
    Nat.Coprime 1 (64002 / 1) ∧ 7 ^ 3 * 1 ^ 7 < (64002 : ℕ) ∧
      Nat.ModEq 7 (64002 / 1) 1 ∧ 7 ^ 161 * 1 ^ 343 < (64002 : ℕ) ^ 49 ∧
      SixthPowerAllocationSieve 1 (64002 / 1) := old_one_allocation_keeps_all_filters

theorem old_three_allocation_still_excluded :
    ¬ ∃ q : ℕ, CenteredNestedAllocationCandidate 1890024 3 q := by
  intro h
  exact three_allocation_has_no_exact_branch ((nestedAllocation_iff_centered _ _).mpr h)

theorem source_centered_receiver_equivalence (p : RamifiedSignedRootRoutingPacket) :
    InternalDepthFourCounterexampleReconstructionObligation p ↔
      SixthPowerSievedCenteredCondition (internalDepthFourSeventhCore p) :=
  internalDepthFourReconstruction_iff_centered p

end DkMathTest.FLT.Seven
