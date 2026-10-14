/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedFusionAllocationResidueSieve
import DkMathTest.FLT.Seven.AllocationThresholdCalibration

#print "file: DkMathTest.FLT.Seven.AllocationResidueSieveCalibration"

namespace DkMathTest.FLT.Seven

open DkMath.FLT.Seven DkMath.CosmicFormulaBinom
open RamifiedSignedRootRoutingPacket.QuotientPrimeSupport

set_option exponentiation.threshold 512

/-- The finite-field fact applies to all natural seven-units. -/
theorem sixth_power_unit_value : Nat.ModEq 7 (2 ^ 6) 1 :=
  sixth_power_mod_seven_of_unit (by decide : ¬ 7 ∣ 2)

theorem fortyNinth_zero_residue : Nat.ModEq 7 ((7 : ℕ) ^ 49) 7 :=
  fortyNinth_power_mod_seven 7

theorem binomial_carry_value : Nat.ModEq 343 ((8 : ℕ) ^ 49) 1 :=
  fortyNinth_power_mod_seven_cube_of_one (by decide : Nat.ModEq 7 8 1)

theorem binomial_carry_one_boundary : Nat.ModEq 343 ((1 : ℕ) ^ 49) 1 :=
  fortyNinth_power_mod_seven_cube_of_one (by decide : Nat.ModEq 7 1 1)

/-- Being a seven-unit alone does not imply the stronger endpoint residue. -/
theorem seven_unit_does_not_force_cube_residue :
    ¬ 7 ∣ (2 : ℕ) ∧ ¬ Nat.ModEq 343 ((2 : ℕ) ^ 6) 1 := by decide

theorem fortyNinth_carry_requires_residue_one :
    ¬ Nat.ModEq 343 ((2 : ℕ) ^ 49) 1 := by decide

theorem old_opposite_thresholds_retained :
    Nat.Coprime 1 (64002 / 1) ∧ Nat.Coprime 2 (64002 / 2) ∧
      7 ^ 3 * 1 ^ 7 < (64002 : ℕ) ∧ 7 ^ 3 * 2 ^ 7 < (64002 : ℕ) ∧
      7 ^ 161 * 1 ^ 343 < (64002 : ℕ) ^ 49 ∧
      (64002 : ℕ) ^ 49 < 7 ^ 161 * 2 ^ 343 :=
  opposite_supported_thresholds

theorem two_allocation_complementary_residue : (64002 : ℕ) / 2 % 7 = 4 := by decide

theorem two_allocation_removed_by_residue :
    ¬ (NestedGNAllocationCondition 64002 2 ∨ NestedRHSAllocationCondition 64002 2) :=
  nestedAllocation_excluded_of_residue (by decide)

/-- Residue and band are independent tests of the scalar equation; this
allocation fails both while passing the old coarse and RHS strict tests. -/
theorem two_allocation_removed_by_band :
    ¬ (7 ^ 161 * 2 ^ 343 ≤ 64 * (64002 : ℕ) ^ 49) := by decide

/-- This only retains arithmetic filters, not an endpoint solution. -/
theorem one_allocation_retains_gn_filters :
    Nat.Coprime 1 (64002 / 1) ∧ 7 ^ 3 * 1 ^ 7 < (64002 : ℕ) ∧
      Nat.ModEq 7 (64002 / 1) 1 ∧ 7 ^ 161 * 1 ^ 343 < (64002 : ℕ) ^ 49 := by decide

theorem divisor_residue_equivalence {M r s : ℕ} (hM : M = r * s) (hr : ¬ 7 ∣ r) :
    Nat.ModEq 7 s 1 ↔ Nat.ModEq 7 r M :=
  nestedAllocation_residue_iff hM hr

/-- A congruence alone is not an inhabited exact receiver. -/
theorem residue_alone_insufficient :
    Nat.ModEq 7 ((1 : ℕ) / 1) 1 ∧ ¬ ThresholdRoutedNestedCondition 1 := by
  refine ⟨by decide, ?_⟩
  rintro ⟨r, hmem, _, hsize, _⟩
  have hr : 0 < r := Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hmem) (by decide)
  have hp : 0 < r ^ 7 := pow_pos hr 7
  norm_num at hsize
  omega

theorem filtered_receiver_equivalence (M : ℕ) (hM : 0 < M) :
    ThresholdRoutedNestedCondition M ↔ ResidueSievedNestedCondition M :=
  thresholdRoutedNestedCondition_iff_residue_sieved M hM

theorem source_filtered_receiver (p : RamifiedSignedRootRoutingPacket) :
    InternalDepthFourCounterexampleReconstructionObligation p ↔
      ResidueSievedNestedCondition (internalDepthFourSeventhCore p) :=
  internalDepthFourReconstruction_iff_residue_sieved p

end DkMathTest.FLT.Seven
