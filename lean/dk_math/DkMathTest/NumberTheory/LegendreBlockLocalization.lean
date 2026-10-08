/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.ParitySafeBlockLocalization
import DkMathTest.NumberTheory.LegendreFreshCost

#print "file: DkMathTest.NumberTheory.LegendreBlockLocalization"

namespace DkMathTest.LegendreBlockLocalization

open DkMath.NumberTheory.Legendre DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.StructuralArithmetic
open scoped BigOperators
open DkMathTest.LegendreFreshCost

/-- Computable normalization of the actual full candidate family. -/
theorem candidate_eq_filter_Icc (n : ℕ) :
    squareAnchorOddPointCoprimeOffsets n = (Finset.Icc 1 (2 * n)).filter
      (fun r => Nat.Coprime n r ∧ (n ^ 2 + r) % 2 = 1) := by
  ext r
  simp only [mem_squareAnchorOddPointCoprimeOffsets, mem_squareAnchorCoprimeOffsets,
    SquareOffset, Nat.odd_iff, Finset.mem_filter, Finset.mem_Icc]
  omega

set_option maxRecDepth 20000 in
theorem mainBlock_candidate_sum :
    (∑ i ∈ Finset.range 20, (squareAnchorOddPointCoprimeOffsets (20 + i + 1)).card) = 490 := by
  simp_rw [candidate_eq_filter_Icc]
  decide

-- Kernel reduction visits every actual candidate and active-support filter in this finite block.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
-- The kernel enumerates the actual finite filters and bounded universal statements.
theorem mainBlock_incidence_sum :
    (∑ i ∈ Finset.range 20, paritySafeIncidenceCount (20 + i + 1)) = 418 := by
  simp_rw [paritySafeIncidenceCount_eq_candidate_support_sum,
    candidate_eq_filter_Icc, activeSupport_eq_filter_range]
  decide

-- Kernel reduction visits every actual candidate and active-support filter in this finite block.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
-- The kernel enumerates the actual finite filters and bounded universal statements.
theorem mainBlock_supportExcess_sum :
    (∑ i ∈ Finset.range 20, paritySafeSupportExcess (20 + i + 1)) = 106 := by
  unfold paritySafeSupportExcess
  simp_rw [candidate_eq_filter_Icc, activeSupport_eq_filter_range]
  decide

-- Kernel reduction visits every actual candidate and active-support filter in this finite block.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
-- The kernel enumerates the actual finite filters and bounded universal statements.
theorem mainBlock_pairOverlap_sum :
    (∑ i ∈ Finset.range 20, paritySafePrimePairOverlapCount (20 + i + 1)) = 137 := by
  unfold paritySafePrimePairOverlapCount
  simp_rw [candidate_eq_filter_Icc, activeSupport_eq_filter_range]
  decide

theorem mainBlock_residualPair_sum :
    (∑ i ∈ Finset.range 20, paritySafeResidualPairMass (20 + i + 1)) = 31 := by
  have h : (∑ i ∈ Finset.range 20, paritySafePrimePairOverlapCount (20 + i + 1)) =
      (∑ i ∈ Finset.range 20, paritySafeSupportExcess (20 + i + 1)) +
      ∑ i ∈ Finset.range 20, paritySafeResidualPairMass (20 + i + 1) := by
    simp_rw [paritySafePrimePairOverlapCount_eq_supportExcess_add_residual,
      Finset.sum_add_distrib]
  rw [mainBlock_pairOverlap_sum, mainBlock_supportExcess_sum] at h
  omega

-- This finite universal check establishes the support threshold before collision sets are simplified.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
-- The kernel enumerates the actual finite filters and bounded universal statements.
theorem mainBlock_support_card_le_three :
    ∀ i ∈ Finset.range 20, ∀ r ∈ squareAnchorOddPointCoprimeOffsets (20 + i + 1),
      (paritySafeActiveSupport (20 + i + 1) r).card ≤ 3 := by
  simp_rw [candidate_eq_filter_Icc, activeSupport_eq_filter_range]
  decide

theorem mainBlock_collision_empty (i : ℕ) (hi : i ∈ Finset.range 20) :
    paritySafeRechargeExactDepthFiberCollisionSeats (20 + i + 1) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro r hr
  have hfour := paritySafeRechargeExactDepthFiberCollision_support_card_ge_four hr
  have hthree := mainBlock_support_card_le_three i hi r
    (paritySafeRechargeExactDepthFiberCollisionSeats_subset_candidate _ hr)
  omega

theorem mainBlock_fifth_empty (i : ℕ) (hi : i ∈ Finset.range 20) :
    paritySafeRechargeExactDepthFiveDirectionCollisionSeats (20 + i + 1) = ∅ := by
  simp [paritySafeRechargeExactDepthFiveDirectionCollisionSeats, mainBlock_collision_empty i hi]

theorem mainBlock_collisionSupport_sum :
    (∑ i ∈ Finset.range 20, paritySafeDepthCollisionLocalSupportCost (20 + i + 1)) = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  simp [paritySafeDepthCollisionLocalSupportCost, mainBlock_collision_empty i hi]

theorem mainBlock_outsidePair_sum :
    (∑ i ∈ Finset.range 20, paritySafePairOverlapOutsideDepthCollision (20 + i + 1)) = 137 := by
  convert mainBlock_pairOverlap_sum using 1
  apply Finset.sum_congr rfl
  intro i hi
  simp [paritySafePairOverlapOutsideDepthCollision, paritySafePrimePairOverlapCount,
    mainBlock_collision_empty i hi]

theorem mainBlock_outsideSupport_sum :
    (∑ i ∈ Finset.range 20, paritySafeSupportExcessOutsideDepthCollision (20 + i + 1)) = 106 := by
  have h : (∑ i ∈ Finset.range 20, paritySafeSupportExcess (20 + i + 1)) =
      (∑ i ∈ Finset.range 20, paritySafeSupportExcessOutsideDepthCollision (20 + i + 1)) +
      ∑ i ∈ Finset.range 20, paritySafeDepthCollisionLocalSupportCost (20 + i + 1) := by
    simp_rw [paritySafeSupportExcess_eq_outsideCollision_add_collisionSupportCost,
      Finset.sum_add_distrib]
  rw [mainBlock_supportExcess_sum, mainBlock_collisionSupport_sum] at h
  omega

/-- The constant comes from Instruction 005's checked theorem, not an extra assumption. -/
theorem mainBlock_localized_38
    (hfull : ∀ i ∈ Finset.range 20, SquareOffsetsFullyCovered (20 + i + 1)) :
    38 ≤ (∑ i ∈ Finset.range 20, paritySafeSupportExcessOutsideDepthCollision (20 + i + 1)) +
      ∑ i ∈ Finset.range 20, paritySafeDepthCollisionLocalSupportCost (20 + i + 1) := by
  have h := mainBlock_support_excess_lower_bound hfull
  simp_rw [paritySafeSupportExcess_eq_outsideCollision_add_collisionSupportCost,
    Finset.sum_add_distrib] at h
  exact h

/-- This finite block already fails the strengthened incidence balance.
The report separately checks whether the new 38 is necessary for failure. -/
theorem mainBlock_not_fullyCovered :
    ¬ (∀ i ∈ Finset.range 20, SquareOffsetsFullyCovered (20 + i + 1)) := by
  intro hfull
  have h := mainBlock_fullCover_balance_with_positive_charge hfull
  rw [mainBlock_candidate_sum, mainBlock_incidence_sum] at h
  omega

/-- The existing exact balance refutes the same block even with no temporal charge. -/
theorem mainBlock_not_fullyCovered_without_freshBound :
    ¬ (∀ i ∈ Finset.range 20, SquareOffsetsFullyCovered (20 + i + 1)) := by
  intro hfull
  have h := block_candidate_add_supportExcess_eq_incidence 20 20 hfull
  rw [mainBlock_candidate_sum, mainBlock_incidence_sum] at h
  omega

/-- A theorem-level witness extracted through the existing full-cover/escape bridge. -/
theorem mainBlock_exists_prime_squareCell :
    ∃ n ∈ Finset.Icc 21 40, ∃ p, Nat.Prime p ∧ SquareCell n p := by
  obtain ⟨i, hi, p, hp, hc⟩ := exists_prime_squareCell_of_not_block_fullyCovered
    20 20 mainBlock_not_fullyCovered
  exact ⟨20 + i + 1, Finset.mem_Icc.mpr ⟨by omega,
    by have := Finset.mem_range.mp hi; omega⟩, p, hp, hc⟩

/-- Finite arithmetic normalization of the production odd active-prime set. -/
theorem oddActive_eq_filter_range (n : ℕ) :
    squareAnchorOddActivePrimes n = (Finset.range (n + 1)).filter
      (fun q => q.Prime ∧ ¬q ∣ n ∧ q ≠ 2) := by
  ext q
  simp [mem_squareAnchorOddActivePrimes, and_left_comm]

theorem coprimeSeats_eq_filter_Icc (n : ℕ) :
    squareAnchorCoprimeOffsets n = (Finset.Icc 1 (2 * n)).filter (Nat.Coprime n) := by
  ext r
  simp only [mem_squareAnchorCoprimeOffsets, SquareOffset, Finset.mem_filter, Finset.mem_Icc]

theorem nearFirst_eq_finite (n : ℕ) :
    paritySafeNearFirstPrimes n = ((Finset.range (n + 1)).filter
      (fun q => q.Prime ∧ ¬q ∣ n ∧ q ≠ 2)).filter
      (fun p => p ^ 3 < n ^ 2 + 2 * n ∧ p ^ 3 < 2 * n) := by
  ext p
  simp [paritySafeNearFirstPrimes, paritySafeTripleGatePrimes,
    oddActive_eq_filter_range, squareBody, and_assoc]

theorem nearPairs_eq_finite (n p : ℕ) :
    paritySafeNearPrimePairsAtFirst n p =
      (((Finset.range (n + 1)).filter (fun q => q.Prime ∧ ¬q ∣ n ∧ q ≠ 2)).product
        ((Finset.range (n + 1)).filter (fun q => q.Prime ∧ ¬q ∣ n ∧ q ≠ 2))).filter
        (fun qs => p < qs.1 ∧ qs.1 < qs.2 ∧ p * qs.1 * qs.2 ≤ 2 * n) := by
  rw [paritySafeNearPrimePairsAtFirst, oddActive_eq_filter_range]

-- A bounded universal check shows every Near fiber empty; no triple waves need evaluation.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
-- The kernel enumerates the actual finite filters and bounded universal statements.
theorem mainBlock_nearPairs_empty :
    ∀ i ∈ Finset.range 20, ∀ p ∈ paritySafeNearFirstPrimes (20 + i + 1),
      paritySafeNearPrimePairsAtFirst (20 + i + 1) p = ∅ := by
  simp_rw [nearFirst_eq_finite, nearPairs_eq_finite]
  decide

theorem mainBlock_nearBudget_sum :
    (∑ i ∈ Finset.range 20, paritySafeNearFirstPrimeWaveBudget (20 + i + 1)) = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  unfold paritySafeNearFirstPrimeWaveBudget
  apply Finset.sum_eq_zero
  intro p hp
  rw [mainBlock_nearPairs_empty i hi p hp]
  simp

theorem depthBudget_eq_finite (n : ℕ) :
    squareAnchorCoprimePrimeSquareDepthBudget n =
      ∑ p ∈ (Finset.range (n + 1)).filter (fun p => p.Prime ∧ ¬p ∣ n),
        (((Finset.Icc 1 (2 * n)).filter (Nat.Coprime n)).filter
          (fun r => p ^ 2 ∣ n ^ 2 + r)).card := by
  have hp : squareAnchorNondivisorPrimes n =
      (Finset.range (n + 1)).filter (fun p => p.Prime ∧ ¬p ∣ n) := by
    ext p
    simp [squareAnchorNondivisorPrimes, primeScalesUpTo, Finset.mem_filter, and_assoc]
  unfold squareAnchorCoprimePrimeSquareDepthBudget squareAnchorCoprimePrimeSquareOffsets
  rw [hp, coprimeSeats_eq_filter_Icc]

-- This reduction counts actual prime-square hits, including prime two in the existing depth budget.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
-- The kernel enumerates the actual finite filters and bounded universal statements.
theorem mainBlock_depthBudget_sum :
    (∑ i ∈ Finset.range 20, squareAnchorCoprimePrimeSquareDepthBudget (20 + i + 1)) = 209 := by
  simp_rw [depthBudget_eq_finite]
  decide

/-- Bounded witnesses normalize the existing Fourth capacity; they add no upper universe. -/
theorem fourthCapacity_eq_finite (n : ℕ) :
    paritySafeFourthGateDualBasePairs n =
      ((((Finset.Icc 1 n).filter (fun t => Nat.Coprime (2 * n) t)).product
        ((Finset.Icc 1 n).filter (fun t => Nat.Coprime (2 * n) t))).filter
        (fun bt => n < bt.1 * bt.2)).filter
        (fun bt =>
          let k := n ^ 2 / (bt.1 * bt.2) + 1
          let s := if k % 2 = 1 then k else k + 1
          s.Prime ∧ s ≤ n ∧ ¬s ∣ n ∧ s ≠ 2 ∧
          n ^ 2 < (bt.1 * bt.2) * s ∧ (bt.1 * bt.2) * s ≤ n ^ 2 + 2 * n ∧
          2 * n < bt.1 * s ∧
          ∃ p ∈ (Finset.range (n + 1)).filter (fun p => p.Prime ∧ ¬p ∣ n ∧ p ≠ 2),
          ∃ q ∈ (Finset.range (n + 1)).filter (fun q => q.Prime ∧ ¬q ∣ n ∧ q ≠ 2),
            p < q ∧ p * q = bt.1 ∧ q < s ∧ p ^ 3 < n ^ 2 + 2 * n ∧
            p ^ 4 < n ^ 2 + 2 * n ∧
            ∀ a ∈ (Finset.range (n + 1)).filter (fun a => a.Prime ∧ ¬a ∣ n ∧ a ≠ 2),
              a < p → ¬a ∣ bt.2) := by
  have hs (b t : ℕ) : paritySafeRechargeOddShellQuotient n b t =
      (let k := n ^ 2 / (b * t) + 1; if k % 2 = 1 then k else k + 1) := by
    simp [paritySafeRechargeOddShellQuotient, Nat.odd_iff]
  have hx (b t : ℕ) :
      (∃ p q, ParitySafeRechargeExactPairWitness n b t p q ∧
        p ∈ paritySafeFourDirectionGatePrimes n) ↔
      ∃ p ∈ (Finset.range (n + 1)).filter (fun p => p.Prime ∧ ¬p ∣ n ∧ p ≠ 2),
      ∃ q ∈ (Finset.range (n + 1)).filter (fun q => q.Prime ∧ ¬q ∣ n ∧ q ≠ 2),
        p < q ∧ p * q = b ∧ q < paritySafeRechargeOddShellQuotient n b t ∧
        p ^ 3 < n ^ 2 + 2 * n ∧ p ^ 4 < n ^ 2 + 2 * n ∧
        ∀ a ∈ (Finset.range (n + 1)).filter (fun a => a.Prime ∧ ¬a ∣ n ∧ a ≠ 2),
          a < p → ¬a ∣ t := by
    constructor
    · rintro ⟨p, q, hw, hf⟩
      rcases hw with ⟨hpg, hq, hpq, hbq, hqs, hrough⟩
      obtain ⟨hp, hpc⟩ := mem_paritySafeTripleGatePrimes.mp hpg
      have hpf := (mem_paritySafeFourDirectionGatePrimes.mp hf).2
      rw [oddActive_eq_filter_range] at hp hq hrough
      exact ⟨p, hp, q, hq, hpq, hbq, hqs,
        by simpa only [squareBody] using hpc,
        by simpa only [squareBody] using hpf, hrough⟩
    · rintro ⟨p, hp, q, hq, hpq, hbq, hqs, hpc, hpf, hrough⟩
      rw [← oddActive_eq_filter_range] at hp hq hrough
      refine ⟨p, q, ?_, ?_⟩
      · exact ⟨mem_paritySafeTripleGatePrimes.mpr ⟨hp, hpc⟩,
          hq, hpq, hbq, hqs, hrough⟩
      · exact mem_paritySafeFourDirectionGatePrimes.mpr ⟨hp, hpf⟩
  ext bt
  rcases bt with ⟨b, t⟩
  simp only [mem_paritySafeFourthGateDualBasePairs, hx,
    mem_paritySafeRechargePrimeAdmissibleDualBasePairs,
    mem_paritySafeRechargeOverAnchorDualBasePairs,
    paritySafeFarCofactorBaseOffsets, Finset.mem_filter,
    mem_squareAnchorOddActivePrimes, hs]
  simp only [Finset.product_eq_sprod, Finset.mem_product, Finset.mem_filter]
  simp only [and_assoc]

-- Bounded prime witnesses make the production Fourth filter decidable in the kernel.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
-- The kernel enumerates bounded prime witnesses at each admissible dual-base pair.
theorem mainBlock_fourthCapacity_sum :
    (∑ i ∈ Finset.range 20, (paritySafeFourthGateDualBasePairs (20 + i + 1)).card) = 14 := by
  simp_rw [fourthCapacity_eq_finite]
  decide

theorem mainBlock_lowCostCapacity_sum :
    (∑ i ∈ Finset.range 20, paritySafeLowCostResidualCapacity (20 + i + 1)) = 223 := by
  simp_rw [paritySafeLowCostResidualCapacity, Finset.sum_add_distrib]
  rw [mainBlock_nearBudget_sum, mainBlock_depthBudget_sum, mainBlock_fourthCapacity_sum]

theorem mainBlock_collision_terms :
    (∑ i ∈ Finset.range 20, (paritySafeRechargeExactDepthFiberCollisionSeats (20 + i + 1)).card) = 0 ∧
    (∑ i ∈ Finset.range 20, (paritySafeRechargeExactDepthFiveDirectionCollisionSeats (20 + i + 1)).card) = 0 ∧
    (∑ i ∈ Finset.range 20, paritySafeRechargeExactDepthResidualPairCapacityExcess (20 + i + 1)) = 0 := by
  constructor
  · apply Finset.sum_eq_zero
    intro i hi
    simp [mainBlock_collision_empty i hi]
  constructor
  · apply Finset.sum_eq_zero
    intro i hi
    simp [mainBlock_fifth_empty i hi]
  · apply Finset.sum_eq_zero
    intro i hi
    simp [paritySafeRechargeExactDepthResidualPairCapacityExcess, mainBlock_collision_empty i hi]

/-- The incidence-eliminated support frontier is feasible with exact slack 490. -/
theorem mainBlock_support_frontier_slack :
    3 * (∑ i ∈ Finset.range 20, paritySafeSupportExcess (20 + i + 1)) +
      2 * (∑ i ∈ Finset.range 20, paritySafeLowCostResidualCapacity (20 + i + 1)) =
      2 * (∑ i ∈ Finset.range 20, paritySafePairOverlapOutsideDepthCollision (20 + i + 1)) +
      11 * (∑ i ∈ Finset.range 20, (paritySafeRechargeExactDepthFiberCollisionSeats (20 + i + 1)).card) +
      2 * (∑ i ∈ Finset.range 20, (paritySafeRechargeExactDepthFiveDirectionCollisionSeats (20 + i + 1)).card) + 490 := by
  rw [mainBlock_supportExcess_sum, mainBlock_lowCostCapacity_sum, mainBlock_outsidePair_sum,
    mainBlock_collision_terms.1, mainBlock_collision_terms.2.1]

/-- Evaluating the original full-cover readable frontier gives a deficit of 44, without +38. -/
theorem mainBlock_fullCover_frontier_deficit :
    2 * (∑ i ∈ Finset.range 20, paritySafePairOverlapOutsideDepthCollision (20 + i + 1)) +
      11 * (∑ i ∈ Finset.range 20, (paritySafeRechargeExactDepthFiberCollisionSeats (20 + i + 1)).card) +
      2 * (∑ i ∈ Finset.range 20, (paritySafeRechargeExactDepthFiveDirectionCollisionSeats (20 + i + 1)).card) +
      3 * (∑ i ∈ Finset.range 20, (squareAnchorOddPointCoprimeOffsets (20 + i + 1)).card) =
      3 * (∑ i ∈ Finset.range 20, paritySafeIncidenceCount (20 + i + 1)) +
      2 * (∑ i ∈ Finset.range 20, paritySafeLowCostResidualCapacity (20 + i + 1)) + 44 := by
  rw [mainBlock_outsidePair_sum, mainBlock_collision_terms.1, mainBlock_collision_terms.2.1,
    mainBlock_candidate_sum, mainBlock_incidence_sum, mainBlock_lowCostCapacity_sum]

/-- The block is also refuted by the existing readable capacity frontier, without temporal demand. -/
theorem mainBlock_not_fullyCovered_from_readable_frontier :
    ¬ (∀ i ∈ Finset.range 20, SquareOffsetsFullyCovered (20 + i + 1)) := by
  intro hfull
  have h := block_readable_frontier_of_fullyCovered 20 20 hfull
  have hd := mainBlock_fullCover_frontier_deficit
  omega

/-- The non-cancelling quantity is the existing uncovered-candidate deficit. -/
theorem mainBlock_uncovered_sum :
    (∑ i ∈ Finset.range 20, (paritySafeUncoveredCandidates (20 + i + 1)).card) = 178 := by
  have h := block_incidence_add_uncovered_eq_candidate_add_supportExcess 20 20
  rw [mainBlock_incidence_sum, mainBlock_candidate_sum, mainBlock_supportExcess_sum] at h
  omega

/-- The whole 106 units of excess are outside collisions in this actual block. -/
theorem mainBlock_excess_not_bounded_by_collisionCost :
    ¬(∑ i ∈ Finset.range 20, paritySafeSupportExcess (20 + i + 1)) ≤
      ∑ i ∈ Finset.range 20, paritySafeDepthCollisionLocalSupportCost (20 + i + 1) := by
  rw [mainBlock_supportExcess_sum, mainBlock_collisionSupport_sum]
  decide

/-- The smaller existing mixed-support example also has cost but no collision recipient. -/
theorem fresh_charge_without_collision :
    lowerFreshSupportExcessCharge 12 6 = 1 ∧
      6 ∉ paritySafeRechargeExactDepthFiberCollisionSeats 13 := by
  have h := fresh_with_persistent_has_cost_without_residual
  refine ⟨h.2.2.2.1, ?_⟩
  intro hr
  have hfour := paritySafeRechargeExactDepthFiberCollision_support_card_ge_four hr
  rw [h.1] at hfour
  norm_num at hfour

/-- Algebra-only regression: a lower bound cannot replace an upper-side variable. -/
theorem lower_bound_substitution_false :
    38 ≤ (40 : ℕ) ∧ 2 * (60 : ℕ) ≤ 3 * 40 ∧ ¬2 * (60 : ℕ) ≤ 3 * 38 := by
  decide

/-- Terminal-key equality reduces the same production keys to bounded arithmetic filters. -/
theorem terminalKeys_eq_finite (n : ℕ) :
    paritySafeTerminalSurvivingFarProductKeys n =
      let active := (Finset.range (n + 1)).filter (fun p => p.Prime ∧ ¬p ∣ n ∧ p ≠ 2)
      ((active.filter (fun p => p ^ 3 < n ^ 2 + 2 * n)).product
        (active.product active)).filter
        (fun key =>
          let m := key.1 * key.2.1 * key.2.2
          let t := n ^ 2 / m + 1
          key.1 < key.2.1 ∧ key.2.1 < key.2.2 ∧ 2 * n < m ∧
          m * t ≤ n ^ 2 + 2 * n ∧ Nat.Coprime (2 * n) t ∧
          (∀ a ∈ (Finset.range (n + 1)).filter (fun a => a.Prime ∧ ¬a ∣ n ∧ a ≠ 2),
            a < key.1 → ¬a ∣ t) ∧ t = 1) := by
  ext key
  simp only [paritySafeTerminalSurvivingFarProductKeys, paritySafeSurvivingFarProductKeys,
    paritySafeTripleGateFarTriples, paritySafeTripleGateTriples, paritySafeTripleGatePrimes,
    Finset.mem_filter, ParitySafeFarProductKeySurvives, ParitySafeFarProductKeyFitsShell,
    paritySafeFarProductWaveNextQuotient, paritySafeTripleProductModulus,
    oddActive_eq_filter_range, squareBody]
  simp only [Finset.product_eq_sprod, Finset.mem_product, Finset.mem_filter, and_assoc]

-- Ordinary kernel reduction counts the actual ordered active-prime keys.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
-- Finite triple filters and their bounded roughness predicates are enumerated in the kernel.
theorem mainBlock_terminalKeys_sum :
    (∑ i ∈ Finset.range 20, (paritySafeTerminalSurvivingFarProductKeys (20 + i + 1)).card) = 17 := by
  simp_rw [terminalKeys_eq_finite]
  decide

theorem mainBlock_lowCostAfterUnused_sum :
    (∑ i ∈ Finset.range 20, paritySafeLowCostResidualMassAfterUnused (20 + i + 1)) = 14 := by
  have h : (∑ i ∈ Finset.range 20, paritySafePairOverlapOutsideDepthCollision (20 + i + 1)) =
      (∑ i ∈ Finset.range 20, paritySafeSupportExcessOutsideDepthCollision (20 + i + 1)) +
      (∑ i ∈ Finset.range 20, (paritySafeTerminalSurvivingFarProductKeys (20 + i + 1)).card) +
      ∑ i ∈ Finset.range 20, paritySafeLowCostResidualMassAfterUnused (20 + i + 1) := by
    simp_rw [paritySafePairOverlapOutsideDepthCollision_eq_outsideSupport_add_terminal_add_lowCostAfterUnused,
      Finset.sum_add_distrib]
  rw [mainBlock_outsidePair_sum, mainBlock_outsideSupport_sum, mainBlock_terminalKeys_sum] at h
  omega

/-- The strongest mature cancellation remains feasible with exact support-charge slack 72. -/
theorem mainBlock_secondCancellation_slack :
    (∑ i ∈ Finset.range 20, paritySafeSupportExcessOutsideDepthCollision (20 + i + 1)) +
      3 * (∑ i ∈ Finset.range 20, paritySafeDepthCollisionLocalSupportCost (20 + i + 1)) =
      2 * (∑ i ∈ Finset.range 20, (paritySafeTerminalSurvivingFarProductKeys (20 + i + 1)).card) +
      9 * (∑ i ∈ Finset.range 20, (paritySafeRechargeExactDepthFiberCollisionSeats (20 + i + 1)).card) +
      3 * (∑ i ∈ Finset.range 20, (paritySafeRechargeExactDepthFiveDirectionCollisionSeats (20 + i + 1)).card) + 72 := by
  rw [mainBlock_outsideSupport_sum, mainBlock_collisionSupport_sum, mainBlock_terminalKeys_sum,
    mainBlock_collision_terms.1, mainBlock_collision_terms.2.1]

end DkMathTest.LegendreBlockLocalization
