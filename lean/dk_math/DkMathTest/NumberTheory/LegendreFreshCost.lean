/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.ParitySafeFreshCost

#print "file: "

namespace DkMathTest.LegendreFreshCost

open DkMath.NumberTheory.Legendre DkMath.NumberTheory.Primitive
open scoped BigOperators

/-- Computable finite normalization of the existing active support, for
kernel calibration only; this equality introduces no substitute ledger. -/
theorem activeSupport_eq_filter_range (n r : ℕ) :
    paritySafeActiveSupport n r = (Finset.range (n + 1)).filter
      (fun q => q.Prime ∧ ¬q ∣ n ∧ q ≠ 2 ∧ q ∣ n ^ 2 + r) := by
  ext q
  simp [mem_paritySafeActiveSupport_iff_dvd, mem_squareAnchorOddActivePrimes,
    and_assoc, and_left_comm]

theorem oldSupport_eq_filter_range (n r : ℕ) :
    squareOffsetPrimeSupport n r = (Finset.range (n + 1)).filter
      (fun q => q.Prime ∧ q ∣ n ^ 2 + r) := by
  ext q
  simp [and_left_comm]

theorem freshSupport_eq_filter_range (n r : ℕ) :
    lowerParitySafeFreshSupport n r = (Finset.range (n + 2)).filter
      (fun q => q.Prime ∧ ¬q ∣ n + 1 ∧ q ≠ 2 ∧ q ∣ (n + 1) ^ 2 + r ∧
        ¬(q ≤ n ∧ q ∣ n ^ 2 + r)) := by
  ext q
  simp only [lowerParitySafeFreshSupport, Finset.mem_sdiff,
    mem_paritySafeActiveSupport_iff_dvd, mem_squareAnchorOddActivePrimes,
    mem_squareOffsetPrimeSupport, Finset.mem_filter, Finset.mem_range]
  have hbound : q < n + 2 ↔ q ≤ n + 1 := by omega
  rw [hbound]
  tauto

-- Finite support filters are reduced by the kernel; the stack limit is local to this calibration.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
-- Kernel reduction enumerates the finite support filters at all actual lower seats.
/-- The exact zero-excess singleton capacity already exceeds the old bound 76. -/
theorem mainBlock_singleton_capacity :
    (∑ i ∈ Finset.range 20, (lowerSingletonFreshSeats (20 + i)).card) = 94 := by
  unfold lowerSingletonFreshSeats
  simp_rw [lowerParitySafeCandidates_eq_filter_Icc, activeSupport_eq_filter_range,
    freshSupport_eq_filter_range]
  decide

-- This finite reduction includes both actual support filters at each seat.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
-- Kernel reduction enumerates the finite support filters at all actual lower seats.
/-- The exact mandatory-first-slot capacity includes fresh-only multiple supports. -/
theorem mainBlock_first_slot_capacity :
    (∑ i ∈ Finset.range 20, (lowerFreshWithoutPersistentSeats (20 + i)).card) = 110 := by
  unfold lowerFreshWithoutPersistentSeats lowerParitySafePersistentSupport
  simp_rw [lowerParitySafeCandidates_eq_filter_Icc, activeSupport_eq_filter_range,
    oldSupport_eq_filter_range, freshSupport_eq_filter_range]
  decide

set_option maxRecDepth 10000 in
/-- Candidate parity strictly improves the previous temporal capacity, from 169 to 97. -/
theorem mainBlock_parity_capacity :
    lowerParitySafeParityPersistenceCap 20 20 = 97 ∧
      lowerParitySafeParityPersistenceCap 20 20 < lowerParitySafePersistenceCap 20 20 := by
  decide

set_option maxRecDepth 10000 in
theorem mainBlock_required_seats :
    (∑ i ∈ Finset.range 20, (lowerParitySafeCandidates (20 + i)).card) = 245 := by
  simp_rw [lowerParitySafeCandidates_eq_filter_Icc]
  decide

/-- The original 76-fresh lower bound cannot exceed the actual zero-cost capacity. -/
theorem old_fresh_bound_below_singleton_capacity :
    76 < ∑ i ∈ Finset.range 20, (lowerSingletonFreshSeats (20 + i)).card := by
  rw [mainBlock_singleton_capacity]
  decide

/-- The refined temporal bound forces at least 148 fresh lower incidences,
under precisely the existing simultaneous full-cover hypothesis. -/
theorem mainBlock_fresh_lower_bound
    (hfull : ∀ i ∈ Finset.range 20, SquareOffsetsFullyCovered (20 + i + 1)) :
    148 ≤ ∑ i ∈ Finset.range 20, lowerParitySafeFreshCount (20 + i) := by
  have h := sum_lowerCandidates_sub_parityCap_le_fresh_of_fullyCovered 20 20 hfull
  simpa only [mainBlock_required_seats, mainBlock_parity_capacity.1] using h

/-- Beyond the 110 first slots, at least 38 units of the existing support-excess
ledger are forced by the improved persistence bound and actual cost decomposition. -/
theorem mainBlock_support_excess_lower_bound
    (hfull : ∀ i ∈ Finset.range 20, SquareOffsetsFullyCovered (20 + i + 1)) :
    38 ≤ ∑ i ∈ Finset.range 20, paritySafeSupportExcess (20 + i + 1) := by
  have h := sum_lowerCandidates_sub_parityCap_sub_firstSlots_le_excess 20 20 hfull
  simpa only [mainBlock_required_seats, mainBlock_parity_capacity.1,
    mainBlock_first_slot_capacity] using h

/-- A checked positive left-side charge in the existing full-cover balance. -/
theorem mainBlock_fullCover_balance_with_positive_charge
    (hfull : ∀ i ∈ Finset.range 20, SquareOffsetsFullyCovered (20 + i + 1)) :
    (∑ i ∈ Finset.range 20, (squareAnchorOddPointCoprimeOffsets (20 + i + 1)).card) + 38 ≤
      ∑ i ∈ Finset.range 20, paritySafeIncidenceCount (20 + i + 1) := by
  have h := sum_fullCandidate_add_freshChargeBound_le_incidence 20 20 hfull
  simpa only [mainBlock_required_seats, mainBlock_parity_capacity.1,
    mainBlock_first_slot_capacity] using h

/-- A fresh singleton need not lie in the persistent prime support of `4*r+1`. -/
theorem singletonFresh_not_bounded_by_persistent_prime_labels :
    4 ∈ lowerSingletonFreshSeats 8 ∧ 5 ∈ lowerParitySafeFreshSupport 8 4 ∧
      5 ∉ (4 * 4 + 1 : ℕ).primeFactors := by
  constructor
  · unfold lowerSingletonFreshSeats
    simp_rw [lowerParitySafeCandidates_eq_filter_Icc,
      activeSupport_eq_filter_range, freshSupport_eq_filter_range]
    decide
  constructor
  · rw [freshSupport_eq_filter_range]
    decide
  · norm_num [Nat.mem_primeFactors]

/-- One fresh direction on a two-direction support pays excess and pair mass,
while the local residual-pair mass is still zero. -/
theorem fresh_with_persistent_has_cost_without_residual :
    paritySafeActiveSupport 13 6 = {5, 7} ∧
      lowerParitySafePersistentSupport 12 6 = {5} ∧
      lowerParitySafeFreshSupport 12 6 = {7} ∧
      lowerFreshSupportExcessCharge 12 6 = 1 ∧
      (lowerParitySafeFreshPairs 12 6).card = 1 ∧
      Nat.choose ((paritySafeActiveSupport 13 6).card - 1) 2 = 0 := by
  have ha : paritySafeActiveSupport 13 6 = {5, 7} := by
    rw [activeSupport_eq_filter_range]
    decide
  have hp : lowerParitySafePersistentSupport 12 6 = {5} := by
    unfold lowerParitySafePersistentSupport
    rw [ha, oldSupport_eq_filter_range]
    decide
  have hf : lowerParitySafeFreshSupport 12 6 = {7} := by
    rw [freshSupport_eq_filter_range]
    decide
  refine ⟨ha, hp, hf, ?_, ?_, ?_⟩
  · simp [lowerFreshSupportExcessCharge, hp, hf]
  · rw [lowerFreshPairs_card_eq_mixed_add_choose_fresh, hp, hf]
    decide
  · rw [ha]
    decide

/-- A positive fresh pair need not consume local residual-pair capacity. -/
theorem fresh_pairs_not_bounded_by_local_residual :
    ¬(lowerParitySafeFreshPairs 12 6).card ≤
      Nat.choose ((paritySafeActiveSupport 13 6).card - 1) 2 := by
  have h := fresh_with_persistent_has_cost_without_residual
  rw [h.2.2.2.2.1, h.2.2.2.2.2]
  decide

/-- Candidate parity removes half of the fixed-seat address opportunities:
+prime three's shell period is three, but at seat two its candidate period is six. -/
theorem candidate_period_regression :
    (lowerCandidatePrimeAddressOffsets 3 2 10 7).card = 2 ∧
      (lowerPrimeAddressOffsets 3 10 7).card = 3 := by
  unfold lowerCandidatePrimeAddressOffsets
  simp_rw [lowerParitySafeCandidates_eq_filter_Icc]
  decide

end DkMathTest.LegendreFreshCost
