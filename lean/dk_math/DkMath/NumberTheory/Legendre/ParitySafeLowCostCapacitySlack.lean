/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.ParitySafeCollisionPairOverlapCancellation

#print "file: DkMath.NumberTheory.Legendre.ParitySafeLowCostCapacitySlack"

/-!
## ParitySafeLowCostCapacitySlack

PRIM-L069 records the unused capacity in the three branches of the L062
LowCost residual.  Each slack is the difference between its named finite
capacity and its realized cardinality.  The resulting exact decomposition is
then substituted into the L068 full-cover cancellation frontier.

This is a finite Nat ledger.  In particular, the slack is not asserted to be
zero, and the module does not turn the resulting inequality into a capacity
collapse, a descent, or a proof of Legendre's conjecture.
-/

namespace DkMath.NumberTheory.Legendre

open scoped BigOperators

/-! ### PRIM-L069.1: branch capacity slacks -/

/-- Unused Near-wave capacity after paying for the canonical near residual. -/
noncomputable def paritySafeNearWaveCapacitySlack (n : ℕ) : ℕ :=
  paritySafeNearFirstPrimeWaveBudget n -
    (paritySafeCanonicalNearResidualTripleIncidences n).card

/-- Unused prime-square depth capacity after paying for noncollision seats. -/
noncomputable def paritySafeNonCollisionDepthCapacitySlack (n : ℕ) : ℕ :=
  squareAnchorCoprimePrimeSquareDepthBudget n -
    (paritySafeRechargeExactDepthNonCollisionSeats n).card

/-- Unused Fourth-gate capacity after paying for exact Fourth pairs. -/
noncomputable def paritySafeFourthGateCapacitySlack (n : ℕ) : ℕ :=
  (paritySafeFourthGateDualBasePairs n).card -
    (paritySafeRechargeExactFourthDirectionPairs n).card

/-- The Near capacity is the realized Near mass plus its slack. -/
theorem paritySafeNearFirstPrimeWaveBudget_eq_nearResidual_add_slack
    (n : ℕ) :
    paritySafeNearFirstPrimeWaveBudget n =
      (paritySafeCanonicalNearResidualTripleIncidences n).card +
        paritySafeNearWaveCapacitySlack n := by
  have hupper :=
    paritySafeCanonicalNearResidualTripleIncidences_card_le_nearFirstPrimeWaveBudget n
  unfold paritySafeNearWaveCapacitySlack
  omega

/-- The prime-square depth capacity is the realized depth mass plus its slack. -/
theorem squareAnchorCoprimePrimeSquareDepthBudget_eq_nonCollisionDepth_add_slack
    (n : ℕ) :
    squareAnchorCoprimePrimeSquareDepthBudget n =
      (paritySafeRechargeExactDepthNonCollisionSeats n).card +
        paritySafeNonCollisionDepthCapacitySlack n := by
  have hupper :=
    paritySafeRechargeExactDepthNonCollisionSeats_card_le_primeSquareDepthBudget n
  unfold paritySafeNonCollisionDepthCapacitySlack
  omega

/-- The Fourth-gate capacity is the realized Fourth mass plus its slack. -/
theorem paritySafeFourthGateDualBase_card_eq_exactFourth_add_slack
    (n : ℕ) :
    (paritySafeFourthGateDualBasePairs n).card =
      (paritySafeRechargeExactFourthDirectionPairs n).card +
        paritySafeFourthGateCapacitySlack n := by
  have hupper := paritySafeRechargeExactFourthDirectionPairs_card_le_fourthGateDualBase n
  unfold paritySafeFourthGateCapacitySlack
  omega

/-! ### PRIM-L069.2: exact LowCost decomposition -/

/-- Sum of the unused capacities of the Near, depth, and Fourth branches. -/
noncomputable def paritySafeLowCostResidualCapacitySlack (n : ℕ) : ℕ :=
  paritySafeNearWaveCapacitySlack n +
    paritySafeNonCollisionDepthCapacitySlack n +
    paritySafeFourthGateCapacitySlack n

/-- LowCost capacity decomposes exactly into realized mass and unused slack. -/
theorem paritySafeLowCostResidualCapacity_eq_mass_add_slack (n : ℕ) :
    paritySafeLowCostResidualCapacity n =
      paritySafeLowCostResidualMass n +
        paritySafeLowCostResidualCapacitySlack n := by
  have hnear := paritySafeNearFirstPrimeWaveBudget_eq_nearResidual_add_slack n
  have hdepth :=
    squareAnchorCoprimePrimeSquareDepthBudget_eq_nonCollisionDepth_add_slack n
  have hfourth := paritySafeFourthGateDualBase_card_eq_exactFourth_add_slack n
  unfold paritySafeLowCostResidualCapacity paritySafeLowCostResidualMass
    paritySafeLowCostResidualCapacitySlack
    paritySafeNearWaveCapacitySlack paritySafeNonCollisionDepthCapacitySlack
    paritySafeFourthGateCapacitySlack
  omega

/-! ### PRIM-L069.3: zero-slack criteria -/

/-- The Near slack vanishes exactly when its upper bound is tight. -/
theorem paritySafeNearWaveCapacitySlack_eq_zero_iff (n : ℕ) :
    paritySafeNearWaveCapacitySlack n = 0 ↔
      paritySafeNearFirstPrimeWaveBudget n =
        (paritySafeCanonicalNearResidualTripleIncidences n).card := by
  have hupper :=
    paritySafeCanonicalNearResidualTripleIncidences_card_le_nearFirstPrimeWaveBudget n
  unfold paritySafeNearWaveCapacitySlack
  omega

/-- The noncollision-depth slack vanishes exactly when its upper bound is tight. -/
theorem paritySafeNonCollisionDepthCapacitySlack_eq_zero_iff (n : ℕ) :
    paritySafeNonCollisionDepthCapacitySlack n = 0 ↔
      squareAnchorCoprimePrimeSquareDepthBudget n =
        (paritySafeRechargeExactDepthNonCollisionSeats n).card := by
  have hupper :=
    paritySafeRechargeExactDepthNonCollisionSeats_card_le_primeSquareDepthBudget n
  unfold paritySafeNonCollisionDepthCapacitySlack
  omega

/-- The Fourth slack vanishes exactly when its upper bound is tight. -/
theorem paritySafeFourthGateCapacitySlack_eq_zero_iff (n : ℕ) :
    paritySafeFourthGateCapacitySlack n = 0 ↔
      (paritySafeFourthGateDualBasePairs n).card =
        (paritySafeRechargeExactFourthDirectionPairs n).card := by
  have hupper := paritySafeRechargeExactFourthDirectionPairs_card_le_fourthGateDualBase n
  unfold paritySafeFourthGateCapacitySlack
  omega

/-- Total LowCost slack vanishes exactly when all three branch bounds are tight. -/
theorem paritySafeLowCostResidualCapacitySlack_eq_zero_iff (n : ℕ) :
    paritySafeLowCostResidualCapacitySlack n = 0 ↔
      paritySafeNearWaveCapacitySlack n = 0 ∧
      paritySafeNonCollisionDepthCapacitySlack n = 0 ∧
      paritySafeFourthGateCapacitySlack n = 0 := by
  unfold paritySafeLowCostResidualCapacitySlack
  omega

/-- Equivalent tightness criterion for zero total LowCost slack. -/
theorem paritySafeLowCostResidualCapacitySlack_eq_zero_iff_all_tight
    (n : ℕ) :
    paritySafeLowCostResidualCapacitySlack n = 0 ↔
      paritySafeNearFirstPrimeWaveBudget n =
          (paritySafeCanonicalNearResidualTripleIncidences n).card ∧
      squareAnchorCoprimePrimeSquareDepthBudget n =
          (paritySafeRechargeExactDepthNonCollisionSeats n).card ∧
      (paritySafeFourthGateDualBasePairs n).card =
          (paritySafeRechargeExactFourthDirectionPairs n).card := by
  rw [paritySafeLowCostResidualCapacitySlack_eq_zero_iff]
  rw [paritySafeNearWaveCapacitySlack_eq_zero_iff,
    paritySafeNonCollisionDepthCapacitySlack_eq_zero_iff,
    paritySafeFourthGateCapacitySlack_eq_zero_iff]

/-! ### PRIM-L069.4: slack-normalized full-cover frontiers -/

/-- L068's totient frontier with realized LowCost mass and explicit slack. -/
theorem two_mul_outsideCollisionPairOverlap_add_elevenCollision_add_twoFiveDirection_add_threeTotient_le_fullCoverLowCostMass_add_slack
    {n : ℕ}
    (hn : 0 < n)
    (hfull : SquareOffsetsFullyCovered n) :
    2 * paritySafePairOverlapOutsideDepthCollision n +
      11 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
      2 * (paritySafeRechargeExactDepthFiveDirectionCollisionSeats n).card +
      3 * Nat.totient (2 * n) ≤
        3 * paritySafeIncidenceCount n +
        2 * paritySafeLowCostResidualMass n +
        2 * paritySafeLowCostResidualCapacitySlack n := by
  have hfront :=
    two_mul_outsideCollisionPairOverlap_add_elevenCollision_add_twoFiveDirection_add_threeTotient_le_fullCoverLowCostCapacity hn hfull
  have hdecomp := paritySafeLowCostResidualCapacity_eq_mass_add_slack n
  omega

/-- Reduced quotient-interval form of the slack-normalized L069 frontier. -/
theorem two_mul_outsideCollisionPairOverlap_add_elevenCollision_add_twoFiveDirection_add_threeTotient_le_reducedQuotient_fullCoverLowCostMass_add_slack
    {n : ℕ}
    (hn : 0 < n)
    (hfull : SquareOffsetsFullyCovered n) :
    2 * paritySafePairOverlapOutsideDepthCollision n +
      11 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
      2 * (paritySafeRechargeExactDepthFiveDirectionCollisionSeats n).card +
      3 * Nat.totient (2 * n) ≤
        3 * (∑ q ∈ squareAnchorOddActivePrimes n,
          (paritySafeReducedQuotientInterval n q).card) +
        2 * paritySafeLowCostResidualMass n +
        2 * paritySafeLowCostResidualCapacitySlack n := by
  have hfront :=
    two_mul_outsideCollisionPairOverlap_add_elevenCollision_add_twoFiveDirection_add_threeTotient_le_fullCoverLowCostMass_add_slack hn hfull
  rw [paritySafeIncidenceCount_eq_reducedQuotientInterval_sum] at hfront
  exact hfront

/-! ### PRIM-L069.5: required slack -/

/-- Amount by which the L068 left side overpays the realized LowCost ledger. -/
noncomputable def paritySafeFullCoverRequiredLowCostSlack (n : ℕ) : ℕ :=
  2 * paritySafePairOverlapOutsideDepthCollision n +
      11 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
      2 * (paritySafeRechargeExactDepthFiveDirectionCollisionSeats n).card +
      3 * Nat.totient (2 * n) -
    (3 * paritySafeIncidenceCount n +
      2 * paritySafeLowCostResidualMass n)

/-- Full cover requires at most twice the explicitly recorded capacity slack. -/
theorem paritySafeFullCoverRequiredLowCostSlack_le_two_capacitySlack
    {n : ℕ}
    (hn : 0 < n)
    (hfull : SquareOffsetsFullyCovered n) :
    paritySafeFullCoverRequiredLowCostSlack n ≤
      2 * paritySafeLowCostResidualCapacitySlack n := by
  have hfront :=
    two_mul_outsideCollisionPairOverlap_add_elevenCollision_add_twoFiveDirection_add_threeTotient_le_fullCoverLowCostMass_add_slack hn hfull
  unfold paritySafeFullCoverRequiredLowCostSlack
  omega

/-- If all three branch bounds are tight, the full-cover frontier has no
additional LowCost overpayment term. -/
theorem two_mul_outsideCollisionPairOverlap_add_elevenCollision_add_twoFiveDirection_add_threeTotient_le_fullCoverLowCostMass_of_capacitySlack_eq_zero
    {n : ℕ}
    (hn : 0 < n)
    (hfull : SquareOffsetsFullyCovered n)
    (hzero : paritySafeLowCostResidualCapacitySlack n = 0) :
    2 * paritySafePairOverlapOutsideDepthCollision n +
      11 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
      2 * (paritySafeRechargeExactDepthFiveDirectionCollisionSeats n).card +
      3 * Nat.totient (2 * n) ≤
        3 * paritySafeIncidenceCount n +
        2 * paritySafeLowCostResidualMass n := by
  have hfront :=
    two_mul_outsideCollisionPairOverlap_add_elevenCollision_add_twoFiveDirection_add_threeTotient_le_fullCoverLowCostMass_add_slack hn hfull
  rw [hzero] at hfront
  simpa using hfront

end DkMath.NumberTheory.Legendre
