/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedFusionCenteredGnomonGap
import DkMathTest.FLT.Seven.CenteredPolynomialCalibration

#print "file: DkMathTest.FLT.Seven.CenteredGnomonGapCalibration"

namespace DkMathTest.FLT.Seven

open DkMath.FLT.Seven
open RamifiedSignedRootRoutingPacket.QuotientPrimeSupport

set_option exponentiation.threshold 512

theorem adjacent_power_one_boundary : (1 : ℕ) ^ 5 ≤ 1 ^ 6 - (1 - 1) ^ 6 :=
  adjacent_sixth_power_sub_ge (by decide)

theorem adjacent_power_two_value : (2 : ℕ) ^ 5 ≤ 2 ^ 6 - (2 - 1) ^ 6 := by decide

theorem symbolic_adjacent_power_step {Q : ℕ} (hQ : 0 < Q) :
    (Q - 1) ^ 6 + Q ^ 5 ≤ Q ^ 6 := adjacent_sixth_power_add_le hQ

theorem symbolic_sixth_power_bracket {D Q : ℕ} (hD : 0 < D) (hscale : 9 * D ^ 2 ≤ Q) :
    centeredSevenSextic D (Q - 1) < 7 * Q ^ 6 ∧
      7 * Q ^ 6 < centeredSevenSextic D Q :=
  centeredSevenSextic_adjacent_sixth_bracket hD hscale

/-- The zero gap has an exact pure-sixth-power image for every t. -/
theorem zero_gap_has_exact_target (t : ℕ) :
    ∃ q : ℕ, centeredSevenSextic 0 q = 448 * (t ^ 6) ^ 49 := by
  refine ⟨2 * t ^ 49, ?_⟩
  rw [centeredSevenSextic_perfectSixth_target]
  simp [centeredSevenSextic]

theorem zero_root_fails_positive_gap_scale {D : ℕ} (hD : 0 < D) :
    ¬ 9 * D ^ 2 ≤ 2 * (0 : ℕ) ^ 49 := by
  have hpos : 0 < 9 * D ^ 2 := Nat.mul_pos (by decide) (pow_pos hD 2)
  norm_num
  omega

theorem missing_size_can_break_lower_bracket :
    ¬ centeredSevenSextic 2 (1 - 1) < 7 * (1 : ℕ) ^ 6 := by decide

theorem nested_scale_constant_checked : 9 * (7 : ℕ) ^ 54 ≤ 2 * 9 ^ 49 :=
  nestedCentered_perfectSixth_scale_constant

theorem nested_scale_symbolic {r t : ℕ} (hsize : 9 * r ^ 2 ≤ t) :
    9 * (7 ^ 27 * r ^ 49) ^ 2 ≤ 2 * t ^ 49 := nestedCentered_perfectSixth_scale hsize

theorem nine_family_passes_old_filters :
    (531441 : ℕ) = 1 * 9 ^ 6 ∧ 1 ∈ (531441 : ℕ).divisors ∧
      Nat.Coprime 1 531441 ∧ ¬ 7 ∣ (1 : ℕ) ∧ ¬ 7 ∣ (531441 : ℕ) ∧
      Nat.ModEq 7 531441 1 ∧ 7 ^ 3 * 1 ^ 7 < (531441 : ℕ) ∧
      7 ^ 161 * 1 ^ 343 < (531441 : ℕ) ^ 49 ∧
      SixthPowerAllocationSieve 1 531441 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, sixthPowerAllocationSieve_mod_one _⟩

/-- Independent kernel arithmetic verifies the exact astronomical bracket. -/
theorem nine_family_exact_bracket :
    centeredSevenSextic (7 ^ 27) (2 * 9 ^ 49 - 1) < 448 * ((9 : ℕ) ^ 6) ^ 49 ∧
      448 * ((9 : ℕ) ^ 6) ^ 49 < centeredSevenSextic (7 ^ 27) (2 * 9 ^ 49) := by decide

theorem nine_family_all_centers_excluded (q : ℕ) :
    centeredSevenSextic (7 ^ 27) q ≠ 448 * (531441 : ℕ) ^ 49 := by
  simpa using nestedCentered_perfectSixth_ne (r := 1) (t := 9)
    (s := 531441) (by decide) (by decide) (by decide) q

theorem nine_family_no_centered_candidate :
    ¬ ∃ q : ℕ, CenteredNestedAllocationCandidate 531441 1 q :=
  nestedCenteredAllocation_excluded_of_perfectSixth (t := 9) (by decide) (by decide) (by decide)

theorem nine_family_no_exact_branch :
    ¬ (NestedGNAllocationCondition 531441 1 ∨ NestedRHSAllocationCondition 531441 1) :=
  nestedAllocation_excluded_of_perfectSixth (t := 9) (by decide) (by decide) (by decide)

/-- The family is symbolic in an unbounded parameter, not a list of samples. -/
theorem all_large_one_allocations_excluded {t : ℕ} (ht : 9 ≤ t) :
    ¬ (NestedGNAllocationCondition (t ^ 6) 1 ∨ NestedRHSAllocationCondition (t ^ 6) 1) :=
  nestedAllocation_excluded_of_perfectSixth (t := t) (by decide) (by simp) (by simpa using ht)

theorem source_scale_all_centers_excluded {r s t : ℕ} (hr : 0 < r)
    (hsize : 9 * r ^ 2 ≤ t) (hs : s = t ^ 6) (q : ℕ) :
    centeredSevenSextic (7 ^ 27 * r ^ 49) q ≠ 448 * s ^ 49 :=
  nestedCentered_perfectSixth_ne hr hsize hs q

/-- Residue support does not imply a global perfect sixth power. -/
theorem residue_support_is_not_perfect_sixth :
    SixthPowerAllocationSieve 1 64002 ∧ ¬ ∃ t : ℕ, (64002 : ℕ) = t ^ 6 := by
  refine ⟨sixthPowerAllocationSieve_mod_one _, ?_⟩
  rintro ⟨t, ht⟩
  rcases le_or_gt t 6 with h | h
  · have hp := Nat.pow_le_pow_left h 6
    have hbound : (6 : ℕ) ^ 6 < 64002 := by decide
    omega
  · have hp : (7 : ℕ) ^ 6 ≤ t ^ 6 :=
      Nat.pow_le_pow_left (show 7 ≤ t from Nat.succ_le_iff.mpr h) 6
    have hbound : (64002 : ℕ) < 7 ^ 6 := by decide
    omega

/-- Old filters plus a perfect sixth power still need not force the size
premise of the new gap theorem. This is arithmetic calibration only. -/
theorem old_filters_do_not_force_gap_size :
    Nat.Coprime 1 729 ∧ ¬ 7 ∣ (729 : ℕ) ∧ Nat.ModEq 7 729 1 ∧
      7 ^ 3 * 1 ^ 7 < (729 : ℕ) ∧ 7 ^ 161 * 1 ^ 343 < (729 : ℕ) ^ 49 ∧
      (729 : ℕ) = 3 ^ 6 ∧ ¬ 9 * (1 : ℕ) ^ 2 ≤ 3 := by decide

theorem old_one_allocation_retained :
    Nat.Coprime 1 (64002 / 1) ∧ 7 ^ 3 * 1 ^ 7 < (64002 : ℕ) ∧
      Nat.ModEq 7 (64002 / 1) 1 ∧ 7 ^ 161 * 1 ^ 343 < (64002 : ℕ) ^ 49 ∧
      SixthPowerAllocationSieve 1 (64002 / 1) := old_one_allocation_keeps_all_filters

theorem old_three_center_exclusion_retained :
    ¬ ∃ q : ℕ, CenteredNestedAllocationCandidate 1890024 3 q :=
  old_three_allocation_still_excluded

theorem source_centered_equivalence_retained (p : RamifiedSignedRootRoutingPacket) :
    InternalDepthFourCounterexampleReconstructionObligation p ↔
      SixthPowerSievedCenteredCondition (internalDepthFourSeventhCore p) :=
  internalDepthFourReconstruction_iff_centered p

theorem complementary_product_compatible_with_nonperfect_core :
    (64002 : ℕ) * 5 = 64002 * 5 ∧ Nat.Coprime 64002 5 ∧
      ¬ ∃ t : ℕ, (64002 : ℕ) = t ^ 6 :=
  ⟨by decide, by decide, residue_support_is_not_perfect_sixth.2⟩

end DkMathTest.FLT.Seven
