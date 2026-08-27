/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.ParitySafeLowCostCapacitySlack

#print "file: DkMath.NumberTheory.Legendre.ParitySafeActualFiberCancellation"

/-!
## ParitySafeActualFiberCancellation

PRIM-L070 returns from the upper-capacity ledger to the actual finite
residual ledger.  The exact-depth fiber excess is separated from the larger
residual-pair capacity by a named collision slack.  Substituting this split
into the collision pair-overlap identity cancels the actual fiber excess and
leaves a capacity-free frontier.

This module is finite Nat bookkeeping.  It does not assert that either the
collision residual slack or the L069 LowCost capacity slack vanishes, and it
does not provide a descent, contradiction, or Legendre/RH conclusion.
-/

namespace DkMath.NumberTheory.Legendre

open scoped BigOperators

/-! ### PRIM-L070.1: actual residual normal form -/

/-- Exact residual mass in LowCost, terminal, collision, and fiber-excess form. -/
theorem paritySafeResidualPairMass_eq_lowCostMass_add_terminal_add_collision_add_depthFiberExcess
    (n : ℕ) :
    paritySafeResidualPairMass n =
      paritySafeLowCostResidualMass n +
      (paritySafeTerminalSurvivingFarProductKeys n).card +
      (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
      paritySafeRechargeExactDepthFiberExcess n := by
  have hres :=
    paritySafeResidualPairMass_eq_near_add_terminal_add_depthSeats_add_depthFiberExcess_add_fourth n
  have hsplit := paritySafeRechargeExactDepthSeats_card_eq_nonCollision_add_collision n
  unfold paritySafeLowCostResidualMass
  omega

/-- Pair-overlap mass in actual LowCost residual normal form. -/
theorem paritySafePrimePairOverlapCount_eq_supportExcess_add_lowCostMass_add_terminal_add_collision_add_depthFiberExcess
    (n : ℕ) :
    paritySafePrimePairOverlapCount n =
      paritySafeSupportExcess n +
      paritySafeLowCostResidualMass n +
      (paritySafeTerminalSurvivingFarProductKeys n).card +
      (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
      paritySafeRechargeExactDepthFiberExcess n := by
  have hover := paritySafePrimePairOverlapCount_eq_supportExcess_add_residual n
  have hres :=
    paritySafeResidualPairMass_eq_lowCostMass_add_terminal_add_collision_add_depthFiberExcess n
  omega

/-! ### PRIM-L070.2: actual fiber charged support frontier -/

/-- The strengthened support charge applied to the actual residual ledger. -/
theorem two_mul_pairOverlap_add_collision_add_fiveDirection_le_threeSupportExcess_add_twoLowCostMass_add_twoDepthFiberExcess
    (n : ℕ) :
    2 * paritySafePrimePairOverlapCount n +
      (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
      (paritySafeRechargeExactDepthFiveDirectionCollisionSeats n).card ≤
        3 * paritySafeSupportExcess n +
        2 * paritySafeLowCostResidualMass n +
        2 * paritySafeRechargeExactDepthFiberExcess n := by
  have hover :=
    paritySafePrimePairOverlapCount_eq_supportExcess_add_lowCostMass_add_terminal_add_collision_add_depthFiberExcess n
  have hcharge := two_mul_terminalKeys_add_three_mul_collision_add_fiveDirection_le_supportExcess n
  omega

/-! ### PRIM-L070.3: collision residual-pair slack -/

/-- Unused residual-pair room after paying for the actual fiber excess. -/
noncomputable def paritySafeDepthCollisionResidualPairSlack
    (n : ℕ) : ℕ :=
  paritySafeRechargeExactDepthResidualPairCapacityExcess n -
    paritySafeRechargeExactDepthFiberExcess n

/-- Residual-pair capacity is actual fiber excess plus unused collision room. -/
theorem paritySafeRechargeExactDepthResidualPairCapacityExcess_eq_fiberExcess_add_collisionResidualPairSlack
    (n : ℕ) :
    paritySafeRechargeExactDepthResidualPairCapacityExcess n =
      paritySafeRechargeExactDepthFiberExcess n +
      paritySafeDepthCollisionResidualPairSlack n := by
  have hupper := paritySafeRechargeExactDepthFiberExcess_le_residualPairCapacityExcess n
  unfold paritySafeDepthCollisionResidualPairSlack
  omega

/-- Collision residual slack vanishes exactly when the fiber bound is tight. -/
theorem paritySafeDepthCollisionResidualPairSlack_eq_zero_iff (n : ℕ) :
    paritySafeDepthCollisionResidualPairSlack n = 0 ↔
      paritySafeRechargeExactDepthResidualPairCapacityExcess n =
        paritySafeRechargeExactDepthFiberExcess n := by
  have hupper := paritySafeRechargeExactDepthFiberExcess_le_residualPairCapacityExcess n
  unfold paritySafeDepthCollisionResidualPairSlack
  omega

/-! ### PRIM-L070.4: exact collision mass with actual fiber -/

/-- Collision pair mass split into support cost, actual fiber excess, and slack. -/
theorem paritySafeDepthCollisionPairOverlapMass_eq_supportCost_add_collision_add_fiberExcess_add_residualSlack
    (n : ℕ) :
    paritySafeDepthCollisionPairOverlapMass n =
      paritySafeDepthCollisionLocalSupportCost n +
      (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
      paritySafeRechargeExactDepthFiberExcess n +
      paritySafeDepthCollisionResidualPairSlack n := by
  have hcollision :=
    paritySafeDepthCollisionPairOverlapMass_eq_supportCost_add_collision_add_depthResidualCapacity n
  have hcapacity :=
    paritySafeRechargeExactDepthResidualPairCapacityExcess_eq_fiberExcess_add_collisionResidualPairSlack n
  omega

/-! ### PRIM-L070.5: actual depth-fiber cancellation -/

/-- Pair-overlap cancellation after exposing the actual fiber excess. -/
theorem two_mul_outsideCollisionPairOverlap_add_twoCollisionSupportCost_add_threeCollision_add_fiveDirection_add_twoResidualSlack_le_threeSupportExcess_add_twoLowCostMass
    (n : ℕ) :
    2 * paritySafePairOverlapOutsideDepthCollision n +
      2 * paritySafeDepthCollisionLocalSupportCost n +
      3 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
      (paritySafeRechargeExactDepthFiveDirectionCollisionSeats n).card +
      2 * paritySafeDepthCollisionResidualPairSlack n ≤
        3 * paritySafeSupportExcess n +
        2 * paritySafeLowCostResidualMass n := by
  have hfront :=
    two_mul_pairOverlap_add_collision_add_fiveDirection_le_threeSupportExcess_add_twoLowCostMass_add_twoDepthFiberExcess n
  have hsplit := paritySafePrimePairOverlapCount_eq_outsideCollision_add_collisionMass n
  have hcollision :=
    paritySafeDepthCollisionPairOverlapMass_eq_supportCost_add_collision_add_fiberExcess_add_residualSlack n
  omega

/-! ### PRIM-L070.6: readable capacity-free frontier -/

/-- Capacity-free frontier with the residual collision slack retained. -/
theorem two_mul_outsideCollisionPairOverlap_add_nineCollision_add_threeFiveDirection_add_twoResidualSlack_le_threeSupportExcess_add_twoLowCostMass
    (n : ℕ) :
    2 * paritySafePairOverlapOutsideDepthCollision n +
      9 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
      3 * (paritySafeRechargeExactDepthFiveDirectionCollisionSeats n).card +
      2 * paritySafeDepthCollisionResidualPairSlack n ≤
        3 * paritySafeSupportExcess n +
        2 * paritySafeLowCostResidualMass n := by
  have hfront :=
    two_mul_outsideCollisionPairOverlap_add_twoCollisionSupportCost_add_threeCollision_add_fiveDirection_add_twoResidualSlack_le_threeSupportExcess_add_twoLowCostMass n
  have hcharge := three_mul_collision_add_fiveDirection_card_le_depthCollisionLocalSupportCost n
  omega

/-! ### PRIM-L070.7: full-cover consumers -/

/-- Candidate-card form of the capacity-free full-cover frontier. -/
theorem two_mul_outsideCollisionPairOverlap_add_nineCollision_add_threeFiveDirection_add_twoResidualSlack_add_threeCandidate_le_fullCoverActualMass
    {n : ℕ}
    (hn : 0 < n)
    (hfull : SquareOffsetsFullyCovered n) :
    2 * paritySafePairOverlapOutsideDepthCollision n +
      9 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
      3 * (paritySafeRechargeExactDepthFiveDirectionCollisionSeats n).card +
      2 * paritySafeDepthCollisionResidualPairSlack n +
      3 * (squareAnchorOddPointCoprimeOffsets n).card ≤
        3 * paritySafeIncidenceCount n +
        2 * paritySafeLowCostResidualMass n := by
  have hfront :=
    two_mul_outsideCollisionPairOverlap_add_nineCollision_add_threeFiveDirection_add_twoResidualSlack_le_threeSupportExcess_add_twoLowCostMass n
  have hbalance := paritySafeCandidate_card_add_supportExcess_eq_incidence_of_fullyCovered hn hfull
  omega

/-- Totient form of the capacity-free full-cover frontier. -/
theorem two_mul_outsideCollisionPairOverlap_add_nineCollision_add_threeFiveDirection_add_twoResidualSlack_add_threeTotient_le_fullCoverActualMass
    {n : ℕ}
    (hn : 0 < n)
    (hfull : SquareOffsetsFullyCovered n) :
    2 * paritySafePairOverlapOutsideDepthCollision n +
      9 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
      3 * (paritySafeRechargeExactDepthFiveDirectionCollisionSeats n).card +
      2 * paritySafeDepthCollisionResidualPairSlack n +
      3 * Nat.totient (2 * n) ≤
        3 * paritySafeIncidenceCount n +
        2 * paritySafeLowCostResidualMass n := by
  have hfront :=
    two_mul_outsideCollisionPairOverlap_add_nineCollision_add_threeFiveDirection_add_twoResidualSlack_add_threeCandidate_le_fullCoverActualMass hn hfull
  have hcard := card_squareAnchorOddPointCoprimeOffsets_eq_totient_two_mul hn
  omega

/-- Reduced quotient-interval form of the capacity-free frontier. -/
theorem two_mul_outsideCollisionPairOverlap_add_nineCollision_add_threeFiveDirection_add_twoResidualSlack_add_threeTotient_le_reducedQuotient_fullCoverActualMass
    {n : ℕ}
    (hn : 0 < n)
    (hfull : SquareOffsetsFullyCovered n) :
    2 * paritySafePairOverlapOutsideDepthCollision n +
      9 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
      3 * (paritySafeRechargeExactDepthFiveDirectionCollisionSeats n).card +
      2 * paritySafeDepthCollisionResidualPairSlack n +
      3 * Nat.totient (2 * n) ≤
        3 * (∑ q ∈ squareAnchorOddActivePrimes n,
          (paritySafeReducedQuotientInterval n q).card) +
        2 * paritySafeLowCostResidualMass n := by
  have hfront :=
    two_mul_outsideCollisionPairOverlap_add_nineCollision_add_threeFiveDirection_add_twoResidualSlack_add_threeTotient_le_fullCoverActualMass hn hfull
  rw [paritySafeIncidenceCount_eq_reducedQuotientInterval_sum] at hfront
  exact hfront

end DkMath.NumberTheory.Legendre
