/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedFusionSixthPowerAllocationSieve
import DkMathTest.FLT.Seven.AllocationResidueSieveCalibration

#print "file: DkMathTest.FLT.Seven.SixthPowerAllocationSieveCalibration"

namespace DkMathTest.FLT.Seven

open DkMath.FLT.Seven
open RamifiedSignedRootRoutingPacket.QuotientPrimeSupport

set_option exponentiation.threshold 512

theorem modular_inverse_recovery {r s w : ℕ} (hcop : Nat.Coprime r s)
    (h : Nat.ModEq (r ^ 49) (s ^ 49) (w ^ 6)) :
    ∃ t : ℕ, Nat.ModEq (r ^ 49) (t ^ 6) s :=
  exists_sixth_power_residue_of_fortyNinth_power hcop h

theorem zero_modulus_boundary : ∃ t : ℕ, Nat.ModEq (0 ^ 49) (t ^ 6) 1 :=
  exists_sixth_power_residue_of_fortyNinth_power (by decide) (w := 1) (by decide)

theorem one_modulus_all_complements (s : ℕ) : SixthPowerAllocationSieve 1 s :=
  sixthPowerAllocationSieve_mod_one s

/-- The powered congruence can hold without coprimality while recovery fails. -/
theorem coprimality_is_required :
    Nat.ModEq (3 ^ 49) ((3 : ℕ) ^ 49) (0 ^ 6) ∧
      ¬ SixthPowerAllocationSieve 3 3 := by
  refine ⟨by decide, ?_⟩
  rintro ⟨t, ht⟩
  have h9 := ht.of_dvd (by decide : 9 ∣ (3 : ℕ) ^ 49)
  have hlt : t % 9 < 9 := Nat.mod_lt _ (by decide)
  have he : (t % 9) ^ 6 % 9 = 3 := by
    simpa [Nat.ModEq, Nat.pow_mod] using h9
  interval_cases hres : t % 9 <;> norm_num [hres] at he

/-- This independent allocation passes every old GN arithmetic guard. -/
theorem three_allocation_passes_old_filters :
    (1890024 : ℕ) = 3 * 630008 ∧ 3 ∈ (1890024 : ℕ).divisors ∧
      (1890024 : ℕ) / 3 = 630008 ∧ Nat.Coprime 3 630008 ∧
      ¬ 7 ∣ (3 : ℕ) ∧ ¬ 7 ∣ (630008 : ℕ) ∧
      Nat.ModEq 7 630008 1 ∧ 7 ^ 3 * 3 ^ 7 < (1890024 : ℕ) ∧
      7 ^ 161 * 3 ^ 343 < (1890024 : ℕ) ^ 49 := by decide

theorem three_allocation_bad_residue : (630008 : ℕ) % 3 = 2 := by decide

theorem three_allocation_removed_by_sixth_power : ¬ SixthPowerAllocationSieve 3 630008 := by
  intro h
  have hs := sixthPowerAllocationSieve_mod_three (by decide : Nat.Coprime 3 630008)
    (by decide : 3 ∣ (3 : ℕ)) h
  exact (by decide : ¬ Nat.ModEq 3 630008 1) hs

theorem three_allocation_has_no_exact_branch :
    ¬ (NestedGNAllocationCondition 1890024 3 ∨ NestedRHSAllocationCondition 1890024 3) :=
  nestedAllocation_excluded_of_sixth_power (by decide)
    (by simpa using three_allocation_removed_by_sixth_power)

theorem old_two_allocation_stays_excluded :
    ¬ (NestedGNAllocationCondition 64002 2 ∨ NestedRHSAllocationCondition 64002 2) :=
  two_allocation_removed_by_residue

/-- Modulus one introduces no false pruning; no scalar endpoint is supplied. -/
theorem old_one_allocation_keeps_all_filters :
    Nat.Coprime 1 (64002 / 1) ∧ 7 ^ 3 * 1 ^ 7 < (64002 : ℕ) ∧
      Nat.ModEq 7 (64002 / 1) 1 ∧ 7 ^ 161 * 1 ^ 343 < (64002 : ℕ) ^ 49 ∧
      SixthPowerAllocationSieve 1 (64002 / 1) := by
  rcases one_allocation_retains_gn_filters with ⟨hcop, hsize, h7, hthreshold⟩
  exact ⟨hcop, hsize, h7, hthreshold, sixthPowerAllocationSieve_mod_one _⟩

theorem prime_support_reduction {q r s : ℕ} (hqr : q ∣ r)
    (h : SixthPowerAllocationSieve r s) : ∃ t : ℕ, Nat.ModEq q (t ^ 6) s :=
  sixthPowerAllocationSieve_reduce hqr h

theorem both_branches_force_mod_three {M r : ℕ} (hcop : Nat.Coprime r (M / r))
    (h3r : 3 ∣ r)
    (h : NestedGNAllocationCondition M r ∨ NestedRHSAllocationCondition M r) :
    Nat.ModEq 3 (M / r) 1 := nestedAllocation_mod_three hcop h3r h

theorem sixth_power_filtered_equivalence (M : ℕ) :
    ResidueSievedNestedCondition M ↔ SixthPowerSievedNestedCondition M :=
  residueSievedNestedCondition_iff_sixth_power_sieved M

theorem source_sixth_power_filtered_receiver (p : RamifiedSignedRootRoutingPacket) :
    InternalDepthFourCounterexampleReconstructionObligation p ↔
      SixthPowerSievedNestedCondition (internalDepthFourSeventhCore p) :=
  internalDepthFourReconstruction_iff_sixth_power_sieved p

/-- The source product and coprimality alone allow three in the allocation.
This is arithmetic calibration, not a source packet. -/
theorem product_identity_does_not_exclude_three :
    (3 : ℕ) * 2 = 3 * 2 ∧ Nat.Coprime 3 2 ∧
      ¬ 3 ∣ (2 : ℕ) ∧ (3 ∣ (3 : ℕ) ∨ 3 ∣ (2 : ℕ)) := by decide

/-- Even an inhabited sixth-power sieve does not supply reconstruction. -/
theorem sixth_power_alone_insufficient :
    SixthPowerAllocationSieve 1 1 ∧ ¬ SixthPowerSievedNestedCondition 1 := by
  refine ⟨sixthPowerAllocationSieve_mod_one 1, ?_⟩
  intro h
  have hres := (residueSievedNestedCondition_iff_sixth_power_sieved 1).mpr h
  have hroute := (thresholdRoutedNestedCondition_iff_residue_sieved 1 (by decide)).mpr hres
  exact residue_alone_insufficient.2 hroute

end DkMathTest.FLT.Seven
