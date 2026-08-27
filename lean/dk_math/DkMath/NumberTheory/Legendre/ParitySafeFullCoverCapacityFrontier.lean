/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.ParitySafeFourthDualBaseCapacity
import DkMath.NumberTheory.Legendre.ParitySafeReducedResidue

#print "file: DkMath.NumberTheory.Legendre.ParitySafeFullCoverCapacityFrontier"

/-!
## ParitySafeFullCoverCapacityFrontier

PRIM-L065 combines the finite LowCost capacity with the charged
pair-overlap ledger.  Under the full-cover hypothesis, the uncovered
candidate set is empty, so candidate cardinality and support excess become
an exact incidence balance.  The resulting frontier is also presented in
totient and reduced-quotient-interval forms.

This module is an upper-frontier and exact-rewrite layer.  It does not add
branch counting, a new capacity for depth residual excess, asymptotic
estimates, descent, a contradiction, or a Legendre/RH conclusion.  In
particular, the LowCost upper bound is not substituted into the L062 lower
frontier in the wrong direction.
-/

open scoped BigOperators

namespace DkMath.NumberTheory.Legendre

/-! ### PRIM-L065.1: residual compression -/

/-- Residual pair mass is controlled by LowCost capacity, terminal keys, and
the already named depth-residual pair capacity. -/
theorem paritySafeResidualPairMass_le_lowCostCapacity_add_terminal_add_depthResidualCapacity
    (n : ℕ) :
    paritySafeResidualPairMass n ≤
      paritySafeLowCostResidualCapacity n +
      (paritySafeTerminalSurvivingFarProductKeys n).card +
      paritySafeRechargeExactDepthResidualPairCapacityExcess n := by
  have hraw :=
    paritySafeResidualPairMass_le_near_add_terminal_add_L018Depth_add_depthResidualCapacity_add_fourth n
  have hnear :=
    paritySafeCanonicalNearResidualTripleIncidences_card_le_nearFirstPrimeWaveBudget n
  have hfourth :=
    paritySafeRechargeExactFourthDirectionPairs_card_le_fourthGateDualBase n
  unfold paritySafeLowCostResidualCapacity
  omega

/-! ### PRIM-L065.2: support-charged doubled pair-overlap frontier -/

/-- The doubled pair-overlap frontier retains the full collision charge. -/
theorem two_mul_pairOverlap_add_threeCollision_le_threeSupportExcess_add_twoLowCostCapacity_add_twoDepthResidualCapacity
    (n : ℕ) :
    2 * paritySafePrimePairOverlapCount n +
      3 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card ≤
        3 * paritySafeSupportExcess n +
        2 * paritySafeLowCostResidualCapacity n +
        2 * paritySafeRechargeExactDepthResidualPairCapacityExcess n := by
  have hover := paritySafePrimePairOverlapCount_eq_supportExcess_add_residual n
  have hres :=
    paritySafeResidualPairMass_le_lowCostCapacity_add_terminal_add_depthResidualCapacity n
  have hcharge := two_mul_terminalKeys_add_three_mul_collisionSeats_le_supportExcess n
  omega

/-! ### PRIM-L065.3: full-cover candidate balance -/

/-- Full cover leaves no uncovered parity-safe candidate. -/
theorem paritySafeUncoveredCandidates_eq_empty_of_fullyCovered
    {n : ℕ}
    (hn : 0 < n)
    (hfull : SquareOffsetsFullyCovered n) :
    paritySafeUncoveredCandidates n = ∅ := by
  ext r
  constructor
  · intro hr
    have hmem := (mem_paritySafeUncoveredCandidates_iff hn).mp hr
    exact False.elim (hmem.2 (hfull r
      (squareOffset_of_mem_squareAnchorOddPointCoprimeOffsets hmem.1)))
  · simp

/-- Under full cover, candidate cardinality plus support excess equals the
exact incidence count. -/
theorem paritySafeCandidate_card_add_supportExcess_eq_incidence_of_fullyCovered
    {n : ℕ}
    (hn : 0 < n)
    (hfull : SquareOffsetsFullyCovered n) :
    (squareAnchorOddPointCoprimeOffsets n).card +
      paritySafeSupportExcess n =
        paritySafeIncidenceCount n := by
  have hempty := paritySafeUncoveredCandidates_eq_empty_of_fullyCovered hn hfull
  have hsplit := paritySafeCoveredCandidates_card_add_uncoveredCandidates_card_eq_candidate_card n
  have hcovered : (paritySafeCoveredCandidates n).card =
      (squareAnchorOddPointCoprimeOffsets n).card := by
    simpa [hempty] using hsplit
  have hinc := paritySafeCoveredCandidates_card_add_supportExcess_eq_incidence n
  omega

/-! ### PRIM-L065.4: support-free full-cover frontier -/

/-- Full cover removes support excess from the readable capacity frontier. -/
theorem two_mul_pairOverlap_add_threeCollision_add_threeCandidate_le_fullCoverCapacity
    {n : ℕ}
    (hn : 0 < n)
    (hfull : SquareOffsetsFullyCovered n) :
    2 * paritySafePrimePairOverlapCount n +
      3 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
      3 * (squareAnchorOddPointCoprimeOffsets n).card ≤
        3 * paritySafeIncidenceCount n +
        2 * paritySafeLowCostResidualCapacity n +
        2 * paritySafeRechargeExactDepthResidualPairCapacityExcess n := by
  have hupper :=
    two_mul_pairOverlap_add_threeCollision_le_threeSupportExcess_add_twoLowCostCapacity_add_twoDepthResidualCapacity n
  have hbalance := paritySafeCandidate_card_add_supportExcess_eq_incidence_of_fullyCovered hn hfull
  omega

/-! ### PRIM-L065.5: totient form -/

/-- The full-cover frontier with the exact reduced-residue candidate count. -/
theorem two_mul_pairOverlap_add_threeCollision_add_threeTotient_le_fullCoverCapacity
    {n : ℕ}
    (hn : 0 < n)
    (hfull : SquareOffsetsFullyCovered n) :
    2 * paritySafePrimePairOverlapCount n +
      3 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
      3 * Nat.totient (2 * n) ≤
        3 * paritySafeIncidenceCount n +
        2 * paritySafeLowCostResidualCapacity n +
        2 * paritySafeRechargeExactDepthResidualPairCapacityExcess n := by
  have hfront :=
    two_mul_pairOverlap_add_threeCollision_add_threeCandidate_le_fullCoverCapacity hn hfull
  have hcard := card_squareAnchorOddPointCoprimeOffsets_eq_totient_two_mul hn
  omega

/-! ### PRIM-L065.6: reduced quotient-interval form -/

/-- The totient frontier after the exact reduced quotient-interval rewrite. -/
theorem two_mul_pairOverlap_add_threeCollision_add_threeTotient_le_reducedQuotient_fullCoverCapacity
    {n : ℕ}
    (hn : 0 < n)
    (hfull : SquareOffsetsFullyCovered n) :
    2 * paritySafePrimePairOverlapCount n +
      3 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
      3 * Nat.totient (2 * n) ≤
        3 * (∑ q ∈ squareAnchorOddActivePrimes n,
          (paritySafeReducedQuotientInterval n q).card) +
        2 * paritySafeLowCostResidualCapacity n +
        2 * paritySafeRechargeExactDepthResidualPairCapacityExcess n := by
  have hfront :=
    two_mul_pairOverlap_add_threeCollision_add_threeTotient_le_fullCoverCapacity hn hfull
  rw [paritySafeIncidenceCount_eq_reducedQuotientInterval_sum] at hfront
  exact hfront

end DkMath.NumberTheory.Legendre
