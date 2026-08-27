/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.ParitySafeTerminalSupportCost

#print "file: DkMath.NumberTheory.Legendre.ParitySafeChargedResidualLedger"

/-!
## ParitySafeChargedResidualLedger

PRIM-L061 combines the accepted support-excess charge from L060V with the
exact residual pair-overlap decomposition.  Collision seats consume one unit
of depth-fiber excess, so the terminal and collision charges can be displayed
as a charged residual normal form.

All statements here are finite identities or inequalities.  The module does
not introduce new branch counting, asymptotics, descent, or a contradiction.
-/

namespace DkMath.NumberTheory.Legendre

open scoped BigOperators

/-! ### PRIM-L061.1: collision count versus fiber excess -/

/-- Every collision seat contributes at least one unit of depth-fiber excess. -/
theorem paritySafeRechargeExactDepthFiberCollisionSeats_card_le_fiberExcess
    (n : ℕ) :
    (paritySafeRechargeExactDepthFiberCollisionSeats n).card ≤
      paritySafeRechargeExactDepthFiberExcess n := by
  rw [paritySafeRechargeExactDepthFiberExcess_eq_collision_sum]
  calc
    (paritySafeRechargeExactDepthFiberCollisionSeats n).card =
        ∑ _r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n, 1 := by
      simp
    _ ≤ ∑ r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n,
        ((paritySafeRechargeExactDepthPairsAtSeat n r).card - 1) := by
      apply Finset.sum_le_sum
      intro r hr
      have hcollision :=
        (mem_paritySafeRechargeExactDepthFiberCollisionSeats.mp hr).2
      omega

/-! ### PRIM-L061.2: support-charge slack -/

/-- The L060V support charge leaves a nonnegative residual slack. -/
theorem exists_terminalCollisionSupportChargeSlack
    (n : ℕ) :
    ∃ k : ℕ,
      paritySafeSupportExcess n =
        2 * (paritySafeTerminalSurvivingFarProductKeys n).card +
        3 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card + k := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le
    (two_mul_terminalKeys_add_three_mul_collisionSeats_le_supportExcess n)
  refine ⟨k, ?_⟩
  omega

/-! ### PRIM-L061.3: exact charged residual normal form -/

/-- The pair-overlap ledger in terminal/collision charged normal form.

The existential `k` records precisely the unused support excess; no natural
number subtraction is introduced into the public API. -/
theorem exists_paritySafePrimePairOverlapCount_charged_normal_form
    (n : ℕ) :
    ∃ k : ℕ,
      paritySafePrimePairOverlapCount n =
        (paritySafeCanonicalNearResidualTripleIncidences n).card +
        3 * (paritySafeTerminalSurvivingFarProductKeys n).card +
        (paritySafeRechargeExactDepthSeats n).card +
        paritySafeRechargeExactDepthFiberExcess n +
        (paritySafeRechargeExactFourthDirectionPairs n).card +
        3 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
        k := by
  obtain ⟨k, hk⟩ := exists_terminalCollisionSupportChargeSlack n
  refine ⟨k, ?_⟩
  rw [paritySafePrimePairOverlapCount_eq_supportExcess_add_residual,
    paritySafeResidualPairMass_eq_near_add_terminal_add_depthSeats_add_depthFiberExcess_add_fourth,
    hk]
  omega

/-! ### PRIM-L061.4--L061.5: weighted residual frontier -/

/-- The charged residual weight is bounded by the exact pair-overlap count. -/
theorem paritySafeChargedResidualWeight_le_primePairOverlapCount
    (n : ℕ) :
    (paritySafeCanonicalNearResidualTripleIncidences n).card +
      3 * (paritySafeTerminalSurvivingFarProductKeys n).card +
      (paritySafeRechargeExactDepthSeats n).card +
      paritySafeRechargeExactDepthFiberExcess n +
      (paritySafeRechargeExactFourthDirectionPairs n).card +
      3 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card ≤
        paritySafePrimePairOverlapCount n := by
  obtain ⟨k, hk⟩ :=
    exists_paritySafePrimePairOverlapCount_charged_normal_form n
  omega

/-- One unit of fiber excess per collision yields the readable lower frontier.

Here the depth-seat term already pays the collision seat itself, while the
extra collision coefficient accounts for its support charge and one fiber
excess unit. -/
theorem paritySafeNear_add_threeTerminal_add_depthSeats_add_fourCollision_add_fourth_le_primePairOverlapCount
    (n : ℕ) :
    (paritySafeCanonicalNearResidualTripleIncidences n).card +
      3 * (paritySafeTerminalSurvivingFarProductKeys n).card +
      (paritySafeRechargeExactDepthSeats n).card +
      4 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
      (paritySafeRechargeExactFourthDirectionPairs n).card ≤
        paritySafePrimePairOverlapCount n := by
  have hcollision :=
    paritySafeRechargeExactDepthFiberCollisionSeats_card_le_fiberExcess n
  have hweight := paritySafeChargedResidualWeight_le_primePairOverlapCount n
  omega

/-! ### PRIM-L061.6: global coprime pair-capacity consumer -/

/-- The charged residual frontier fits inside the coprime pair capacity. -/
theorem paritySafeNear_add_threeTerminal_add_depthSeats_add_fourCollision_add_fourth_le_coprimePrimePairOverlapCount
    (n : ℕ) :
    (paritySafeCanonicalNearResidualTripleIncidences n).card +
      3 * (paritySafeTerminalSurvivingFarProductKeys n).card +
      (paritySafeRechargeExactDepthSeats n).card +
      4 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
      (paritySafeRechargeExactFourthDirectionPairs n).card ≤
        squareAnchorCoprimePrimePairOverlapCount n := by
  exact
    (paritySafeNear_add_threeTerminal_add_depthSeats_add_fourCollision_add_fourth_le_primePairOverlapCount n).trans
      (paritySafePrimePairOverlapCount_le_squareAnchorCoprimePrimePairOverlapCount n)

end DkMath.NumberTheory.Legendre
