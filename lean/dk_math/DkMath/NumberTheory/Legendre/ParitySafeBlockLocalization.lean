/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.ParitySafeFreshCost
import DkMath.NumberTheory.Legendre.ParitySafeSecondCancellationRedundancyAudit
import DkMath.NumberTheory.Legendre.Frontier

#print "file: DkMath.NumberTheory.Legendre.ParitySafeBlockLocalization"

/-!
## Finite block support-excess localization

This module transports temporal fresh-demand bounds into the existing outside
support/collision support partition. It also records the exact block
elimination of full-cover incidence. A lower bound on support excess cannot
be substituted for the upper-side occurrence of incidence in a frontier.
Finite contradiction criteria require an independently proved upper capacity.
-/

namespace DkMath.NumberTheory.Legendre

open scoped BigOperators

/-- Even empty support satisfies the local excess/pair comparison. -/
theorem activeSupport_excess_le_pair (n r : ℕ) :
    (paritySafeActiveSupport n r).card - 1 ≤
      Nat.choose (paritySafeActiveSupport n r).card 2 := by
  generalize (paritySafeActiveSupport n r).card = k
  cases k with
  | zero => simp
  | succ k =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    omega

/-- The existing exact star/residual identity needs no full-cover hypothesis. -/
theorem paritySafeSupportExcess_le_pairOverlap (n : ℕ) :
    paritySafeSupportExcess n ≤ paritySafePrimePairOverlapCount n := by
  have h := paritySafePrimePairOverlapCount_eq_supportExcess_add_residual n
  omega

/-- Localize excess without paying collision baseline or residual capacity. -/
theorem paritySafeSupportExcess_le_outsidePair_add_collisionSupportCost (n : ℕ) :
    paritySafeSupportExcess n ≤ paritySafePairOverlapOutsideDepthCollision n +
      paritySafeDepthCollisionLocalSupportCost n := by
  have he := paritySafeSupportExcess_eq_outsideCollision_add_collisionSupportCost n
  have hp := paritySafePairOverlapOutsideDepthCollision_eq_outsideSupport_add_outsideResidual n
  omega

/-- The requested longer localization follows from the sharper two-recipient bound. -/
theorem paritySafeSupportExcess_le_outsidePair_add_collisionSupport_add_baseline_add_depthResidual
    (n : ℕ) :
    paritySafeSupportExcess n ≤ paritySafePairOverlapOutsideDepthCollision n +
      paritySafeDepthCollisionLocalSupportCost n +
      (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
      paritySafeRechargeExactDepthResidualPairCapacityExcess n := by
  have h := paritySafeSupportExcess_le_outsidePair_add_collisionSupportCost n
  omega

/-- Exact production partition over any finite shell set. -/
theorem sum_supportExcess_eq_outsideSupport_add_collisionSupport (s : Finset ℕ) :
    (∑ n ∈ s, paritySafeSupportExcess n) =
      (∑ n ∈ s, paritySafeSupportExcessOutsideDepthCollision n) +
      ∑ n ∈ s, paritySafeDepthCollisionLocalSupportCost n := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun n _ =>
    paritySafeSupportExcess_eq_outsideCollision_add_collisionSupportCost n

/-- A mandatory temporal charge is placed in the exact existing support recipients. -/
theorem block_freshBound_le_outsideSupport_add_collisionSupport
    (N T : ℕ) (hfull : ∀ i ∈ Finset.range T, SquareOffsetsFullyCovered (N + i + 1)) :
    ((∑ i ∈ Finset.range T, (lowerParitySafeCandidates (N + i)).card) -
      lowerParitySafeParityPersistenceCap N T -
      (∑ i ∈ Finset.range T, (lowerFreshWithoutPersistentSeats (N + i)).card)) ≤
      (∑ i ∈ Finset.range T, paritySafeSupportExcessOutsideDepthCollision (N + i + 1)) +
      ∑ i ∈ Finset.range T, paritySafeDepthCollisionLocalSupportCost (N + i + 1) := by
  have h := sum_lowerCandidates_sub_parityCap_sub_firstSlots_le_excess N T hfull
  simp_rw [paritySafeSupportExcess_eq_outsideCollision_add_collisionSupportCost,
    Finset.sum_add_distrib] at h
  exact h

/-- The same mandatory charge is bounded by outside pairs and collision support. -/
theorem block_freshBound_le_outsidePair_add_collisionSupport
    (N T : ℕ) (hfull : ∀ i ∈ Finset.range T, SquareOffsetsFullyCovered (N + i + 1)) :
    ((∑ i ∈ Finset.range T, (lowerParitySafeCandidates (N + i)).card) -
      lowerParitySafeParityPersistenceCap N T -
      (∑ i ∈ Finset.range T, (lowerFreshWithoutPersistentSeats (N + i)).card)) ≤
      (∑ i ∈ Finset.range T, paritySafePairOverlapOutsideDepthCollision (N + i + 1)) +
      ∑ i ∈ Finset.range T, paritySafeDepthCollisionLocalSupportCost (N + i + 1) := by
  have h := sum_lowerCandidates_sub_parityCap_sub_firstSlots_le_excess N T hfull
  have hl := Finset.sum_le_sum (s := Finset.range T)
    fun i _ => paritySafeSupportExcess_le_outsidePair_add_collisionSupportCost (N + i + 1)
  rw [Finset.sum_add_distrib] at hl
  exact h.trans hl

/-- Exact full-cover incidence balance over the same successor block. -/
theorem block_candidate_add_supportExcess_eq_incidence
    (N T : ℕ) (hfull : ∀ i ∈ Finset.range T, SquareOffsetsFullyCovered (N + i + 1)) :
    (∑ i ∈ Finset.range T, (squareAnchorOddPointCoprimeOffsets (N + i + 1)).card) +
      (∑ i ∈ Finset.range T, paritySafeSupportExcess (N + i + 1)) =
      ∑ i ∈ Finset.range T, paritySafeIncidenceCount (N + i + 1) := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i hi =>
    paritySafeCandidate_card_add_supportExcess_eq_incidence_of_fullyCovered
      (by omega) (hfull i hi)

/-- The actual uncovered-candidate deficit survives without assuming full cover. -/
theorem block_incidence_add_uncovered_eq_candidate_add_supportExcess (N T : ℕ) :
    (∑ i ∈ Finset.range T, paritySafeIncidenceCount (N + i + 1)) +
      (∑ i ∈ Finset.range T, (paritySafeUncoveredCandidates (N + i + 1)).card) =
      (∑ i ∈ Finset.range T, (squareAnchorOddPointCoprimeOffsets (N + i + 1)).card) +
      ∑ i ∈ Finset.range T, paritySafeSupportExcess (N + i + 1) := by
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hc := paritySafeCoveredCandidates_card_add_uncoveredCandidates_card_eq_candidate_card (N + i + 1)
  have he := paritySafeCoveredCandidates_card_add_supportExcess_eq_incidence (N + i + 1)
  omega

/-- The existing readable frontier summed over a finite successor block. -/
theorem block_readable_frontier_of_fullyCovered
    (N T : ℕ) (hfull : ∀ i ∈ Finset.range T, SquareOffsetsFullyCovered (N + i + 1)) :
    2 * (∑ i ∈ Finset.range T, paritySafePairOverlapOutsideDepthCollision (N + i + 1)) +
      11 * (∑ i ∈ Finset.range T, (paritySafeRechargeExactDepthFiberCollisionSeats (N + i + 1)).card) +
      2 * (∑ i ∈ Finset.range T, (paritySafeRechargeExactDepthFiveDirectionCollisionSeats (N + i + 1)).card) +
      3 * (∑ i ∈ Finset.range T, (squareAnchorOddPointCoprimeOffsets (N + i + 1)).card) ≤
      3 * (∑ i ∈ Finset.range T, paritySafeIncidenceCount (N + i + 1)) +
      2 * (∑ i ∈ Finset.range T, paritySafeLowCostResidualCapacity (N + i + 1)) := by
  have h := Finset.sum_le_sum (s := Finset.range T) fun i hi =>
    two_mul_outsideCollisionPairOverlap_add_elevenCollision_add_twoFiveDirection_add_threeCandidate_le_fullCoverLowCostCapacity
      (by omega) (hfull i hi)
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum] using h

/-- Exact elimination removes incidence but retains the actual excess, not its lower bound. -/
theorem block_readable_frontier_iff_support_frontier
    (N T : ℕ) (hfull : ∀ i ∈ Finset.range T, SquareOffsetsFullyCovered (N + i + 1)) :
    (2 * (∑ i ∈ Finset.range T, paritySafePairOverlapOutsideDepthCollision (N + i + 1)) +
      11 * (∑ i ∈ Finset.range T, (paritySafeRechargeExactDepthFiberCollisionSeats (N + i + 1)).card) +
      2 * (∑ i ∈ Finset.range T, (paritySafeRechargeExactDepthFiveDirectionCollisionSeats (N + i + 1)).card) +
      3 * (∑ i ∈ Finset.range T, (squareAnchorOddPointCoprimeOffsets (N + i + 1)).card) ≤
      3 * (∑ i ∈ Finset.range T, paritySafeIncidenceCount (N + i + 1)) +
      2 * (∑ i ∈ Finset.range T, paritySafeLowCostResidualCapacity (N + i + 1))) ↔
    (2 * (∑ i ∈ Finset.range T, paritySafePairOverlapOutsideDepthCollision (N + i + 1)) +
      11 * (∑ i ∈ Finset.range T, (paritySafeRechargeExactDepthFiberCollisionSeats (N + i + 1)).card) +
      2 * (∑ i ∈ Finset.range T, (paritySafeRechargeExactDepthFiveDirectionCollisionSeats (N + i + 1)).card) ≤
      3 * (∑ i ∈ Finset.range T, paritySafeSupportExcess (N + i + 1)) +
      2 * (∑ i ∈ Finset.range T, paritySafeLowCostResidualCapacity (N + i + 1))) := by
  have h := block_candidate_add_supportExcess_eq_incidence N T hfull
  omega

/-- After the mature second cancellation, only the already-proved support charge remains. -/
theorem block_secondCancellation_iff_reducedSupportCharge (s : Finset ℕ) :
    (2 * (∑ n ∈ s, paritySafePairOverlapOutsideDepthCollision n) +
      9 * (∑ n ∈ s, (paritySafeRechargeExactDepthFiberCollisionSeats n).card) +
      3 * (∑ n ∈ s, (paritySafeRechargeExactDepthFiveDirectionCollisionSeats n).card) ≤
      3 * (∑ n ∈ s, paritySafeSupportExcess n) +
      2 * (∑ n ∈ s, paritySafeLowCostResidualMassAfterUnused n)) ↔
    (2 * (∑ n ∈ s, (paritySafeTerminalSurvivingFarProductKeys n).card) +
      9 * (∑ n ∈ s, (paritySafeRechargeExactDepthFiberCollisionSeats n).card) +
      3 * (∑ n ∈ s, (paritySafeRechargeExactDepthFiveDirectionCollisionSeats n).card) ≤
      (∑ n ∈ s, paritySafeSupportExcessOutsideDepthCollision n) +
      3 * (∑ n ∈ s, paritySafeDepthCollisionLocalSupportCost n)) := by
  have hp : (∑ n ∈ s, paritySafePairOverlapOutsideDepthCollision n) =
      (∑ n ∈ s, paritySafeSupportExcessOutsideDepthCollision n) +
      (∑ n ∈ s, (paritySafeTerminalSurvivingFarProductKeys n).card) +
      ∑ n ∈ s, paritySafeLowCostResidualMassAfterUnused n := by
    simp_rw [paritySafePairOverlapOutsideDepthCollision_eq_outsideSupport_add_terminal_add_lowCostAfterUnused,
      Finset.sum_add_distrib]
  have he := sum_supportExcess_eq_outsideSupport_add_collisionSupport s
  omega

/-- An independent upper bound below temporal demand refutes simultaneous cover. -/
theorem not_block_fullyCovered_of_localized_capacity_lt_freshBound
    (N T U : ℕ)
    (hu : (∑ i ∈ Finset.range T, paritySafePairOverlapOutsideDepthCollision (N + i + 1)) +
      (∑ i ∈ Finset.range T, paritySafeDepthCollisionLocalSupportCost (N + i + 1)) ≤ U)
    (hlt : U < (∑ i ∈ Finset.range T, (lowerParitySafeCandidates (N + i)).card) -
      lowerParitySafeParityPersistenceCap N T -
      (∑ i ∈ Finset.range T, (lowerFreshWithoutPersistentSeats (N + i)).card)) :
    ¬ (∀ i ∈ Finset.range T, SquareOffsetsFullyCovered (N + i + 1)) := by
  intro hfull
  have h := block_freshBound_le_outsidePair_add_collisionSupport N T hfull
  omega

/-- The exact candidate/incidence balance also consumes any independently checked incidence cap. -/
theorem not_block_fullyCovered_of_incidence_lt_candidate_add_freshBound
    (N T : ℕ)
    (hlt : (∑ i ∈ Finset.range T, paritySafeIncidenceCount (N + i + 1)) <
      (∑ i ∈ Finset.range T, (squareAnchorOddPointCoprimeOffsets (N + i + 1)).card) +
      ((∑ i ∈ Finset.range T, (lowerParitySafeCandidates (N + i)).card) -
        lowerParitySafeParityPersistenceCap N T -
        (∑ i ∈ Finset.range T, (lowerFreshWithoutPersistentSeats (N + i)).card))) :
    ¬ (∀ i ∈ Finset.range T, SquareOffsetsFullyCovered (N + i + 1)) := by
  intro hfull
  have h := sum_fullCandidate_add_freshChargeBound_le_incidence N T hfull
  omega

/-- Extract the existing square-cell prime witness from finite block failure. -/
theorem exists_prime_squareCell_of_not_block_fullyCovered
    (N T : ℕ)
    (hnot : ¬ (∀ i ∈ Finset.range T, SquareOffsetsFullyCovered (N + i + 1))) :
    ∃ i ∈ Finset.range T, ∃ p, Nat.Prime p ∧ SquareCell (N + i + 1) p := by
  classical
  push Not at hnot
  obtain ⟨i, hi, hn⟩ := hnot
  obtain ⟨r, hr⟩ := not_squareOffsetsFullyCovered_iff_escaping_nonempty.mp hn
  have hs := mem_escapingSquareOffsets.mp hr
  have hd := supportDisjointFrom_primeScalesUpTo_square_add_iff_not_covered.mpr hs.2
  exact ⟨i, hi, (N + i + 1) ^ 2 + r,
    prime_of_squareAnchoredSupportEscape (by omega) hs.1 hd,
    (squareCell_iff_exists_squareOffset _ _).2 ⟨r, hs.1, rfl⟩⟩

end DkMath.NumberTheory.Legendre
