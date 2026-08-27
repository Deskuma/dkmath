/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.ParitySafeUnusedResidualPairRouting

#print "file: DkMath.NumberTheory.Legendre.ParitySafeSecondCancellationRedundancyAudit"

/-!
## ParitySafeSecondCancellationRedundancyAudit

PRIM-L073 audits the second-cancellation frontier by splitting the existing
candidate ledger into the exact-depth collision surface and its complement.
The resulting identities decide whether the L072 frontier contributes a new
obstruction or only rewrites the established terminal/collision support
charge.  This module adds no new capacity, wave count, prime direction,
descent, analytic estimate, Legendre statement, or RH statement.
-/

namespace DkMath.NumberTheory.Legendre

open scoped BigOperators

noncomputable section
local instance classicalDecidableSecondCancellation (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-! ### PRIM-L073.1: outside support cost -/

/-- Support excess on candidate seats outside the depth-collision surface. -/
noncomputable def paritySafeSupportExcessOutsideDepthCollision
    (n : ℕ) : ℕ :=
  ∑ r ∈
      (squareAnchorOddPointCoprimeOffsets n \
        paritySafeRechargeExactDepthFiberCollisionSeats n),
    ((paritySafeActiveSupport n r).card - 1)

theorem paritySafeSupportExcess_eq_outsideCollision_add_collisionSupportCost
    (n : ℕ) :
    paritySafeSupportExcess n =
      paritySafeSupportExcessOutsideDepthCollision n +
      paritySafeDepthCollisionLocalSupportCost n := by
  have hsub := paritySafeRechargeExactDepthFiberCollisionSeats_subset_candidate n
  have hdisjoint : Disjoint
      (squareAnchorOddPointCoprimeOffsets n \
        paritySafeRechargeExactDepthFiberCollisionSeats n)
      (paritySafeRechargeExactDepthFiberCollisionSeats n) :=
    Finset.sdiff_disjoint
  have hunion := Finset.sdiff_union_of_subset hsub
  unfold paritySafeSupportExcess
    paritySafeSupportExcessOutsideDepthCollision
    paritySafeDepthCollisionLocalSupportCost
  calc
    (∑ r ∈ squareAnchorOddPointCoprimeOffsets n,
        ((paritySafeActiveSupport n r).card - 1)) =
        ∑ r ∈ (squareAnchorOddPointCoprimeOffsets n \
          paritySafeRechargeExactDepthFiberCollisionSeats n) ∪
            paritySafeRechargeExactDepthFiberCollisionSeats n,
          ((paritySafeActiveSupport n r).card - 1) := by
      rw [hunion]
    _ = (∑ r ∈ squareAnchorOddPointCoprimeOffsets n \
          paritySafeRechargeExactDepthFiberCollisionSeats n,
        ((paritySafeActiveSupport n r).card - 1)) +
        ∑ r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n,
          ((paritySafeActiveSupport n r).card - 1) := by
      rw [Finset.sum_union hdisjoint]

/-! ### PRIM-L073.2: outside and collision residual masses -/

/-- Residual pair mass on candidate seats outside the collision surface. -/
noncomputable def paritySafeResidualPairMassOutsideDepthCollision
    (n : ℕ) : ℕ :=
  ∑ r ∈
      (squareAnchorOddPointCoprimeOffsets n \
        paritySafeRechargeExactDepthFiberCollisionSeats n),
    Nat.choose ((paritySafeActiveSupport n r).card - 1) 2

/-- Residual pair mass on the exact-depth collision surface. -/
noncomputable def paritySafeDepthCollisionResidualPairMass
    (n : ℕ) : ℕ :=
  ∑ r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n,
    Nat.choose ((paritySafeActiveSupport n r).card - 1) 2

theorem paritySafeResidualPairMass_eq_outsideCollision_add_collisionResidual
    (n : ℕ) :
    paritySafeResidualPairMass n =
      paritySafeResidualPairMassOutsideDepthCollision n +
      paritySafeDepthCollisionResidualPairMass n := by
  have hsub := paritySafeRechargeExactDepthFiberCollisionSeats_subset_candidate n
  have hdisjoint : Disjoint
      (squareAnchorOddPointCoprimeOffsets n \
        paritySafeRechargeExactDepthFiberCollisionSeats n)
      (paritySafeRechargeExactDepthFiberCollisionSeats n) :=
    Finset.sdiff_disjoint
  have hunion := Finset.sdiff_union_of_subset hsub
  unfold paritySafeResidualPairMass
    paritySafeResidualPairMassOutsideDepthCollision
    paritySafeDepthCollisionResidualPairMass
  calc
    (∑ r ∈ squareAnchorOddPointCoprimeOffsets n,
        Nat.choose ((paritySafeActiveSupport n r).card - 1) 2) =
        ∑ r ∈ (squareAnchorOddPointCoprimeOffsets n \
          paritySafeRechargeExactDepthFiberCollisionSeats n) ∪
            paritySafeRechargeExactDepthFiberCollisionSeats n,
          Nat.choose ((paritySafeActiveSupport n r).card - 1) 2 := by
      rw [hunion]
    _ = (∑ r ∈ squareAnchorOddPointCoprimeOffsets n \
          paritySafeRechargeExactDepthFiberCollisionSeats n,
        Nat.choose ((paritySafeActiveSupport n r).card - 1) 2) +
        ∑ r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n,
          Nat.choose ((paritySafeActiveSupport n r).card - 1) 2 := by
      rw [Finset.sum_union hdisjoint]

private theorem choose_two_eq_sub_one_add_choose_sub_one_l073 (k : ℕ) :
    Nat.choose k 2 = (k - 1) + Nat.choose (k - 1) 2 := by
  cases k with
  | zero => simp
  | succ k =>
    cases k with
    | zero => simp
    | succ k =>
      rw [Nat.choose_succ_succ]
      simp [Nat.choose_succ_succ, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc]

theorem paritySafePairOverlapOutsideDepthCollision_eq_outsideSupport_add_outsideResidual
    (n : ℕ) :
    paritySafePairOverlapOutsideDepthCollision n =
      paritySafeSupportExcessOutsideDepthCollision n +
      paritySafeResidualPairMassOutsideDepthCollision n := by
  unfold paritySafePairOverlapOutsideDepthCollision
    paritySafeSupportExcessOutsideDepthCollision
    paritySafeResidualPairMassOutsideDepthCollision
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  exact choose_two_eq_sub_one_add_choose_sub_one_l073
    (paritySafeActiveSupport n r).card

/-! ### PRIM-L073.3: actual collision residual decomposition -/

theorem paritySafeDepthCollisionResidualPairMass_eq_collision_add_fiberExcess_add_unused
    (n : ℕ) :
    paritySafeDepthCollisionResidualPairMass n =
      (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
      paritySafeRechargeExactDepthFiberExcess n +
      paritySafeDepthCollisionUnusedResidualPairMass n := by
  have hlocal : paritySafeDepthCollisionPairOverlapMass n =
      paritySafeDepthCollisionLocalSupportCost n +
      paritySafeDepthCollisionResidualPairMass n := by
    unfold paritySafeDepthCollisionPairOverlapMass
      paritySafeDepthCollisionLocalSupportCost
      paritySafeDepthCollisionResidualPairMass
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    exact choose_two_eq_sub_one_add_choose_sub_one_l073
      (paritySafeActiveSupport n r).card
  have hactual :=
    paritySafeDepthCollisionPairOverlapMass_eq_supportCost_add_collision_add_fiberExcess_add_residualSlack n
  have hslack := paritySafeDepthCollisionResidualPairSlack_eq_unusedResidualPairMass n
  omega

/-! ### PRIM-L073.4: the outside residual identity -/

theorem paritySafeResidualPairMassOutsideDepthCollision_eq_terminal_add_lowCostAfterUnused
    (n : ℕ) :
    paritySafeResidualPairMassOutsideDepthCollision n =
      (paritySafeTerminalSurvivingFarProductKeys n).card +
      paritySafeLowCostResidualMassAfterUnused n := by
  have htotal :=
    paritySafeResidualPairMass_eq_lowCostMass_add_terminal_add_collision_add_depthFiberExcess n
  have hsplit := paritySafeResidualPairMass_eq_outsideCollision_add_collisionResidual n
  have hcollision :=
    paritySafeDepthCollisionResidualPairMass_eq_collision_add_fiberExcess_add_unused n
  have hlow := paritySafeLowCostResidualMass_eq_unused_add_afterUnused n
  omega

theorem paritySafePairOverlapOutsideDepthCollision_eq_outsideSupport_add_terminal_add_lowCostAfterUnused
    (n : ℕ) :
    paritySafePairOverlapOutsideDepthCollision n =
      paritySafeSupportExcessOutsideDepthCollision n +
      (paritySafeTerminalSurvivingFarProductKeys n).card +
      paritySafeLowCostResidualMassAfterUnused n := by
  have hpair := paritySafePairOverlapOutsideDepthCollision_eq_outsideSupport_add_outsideResidual n
  have hres := paritySafeResidualPairMassOutsideDepthCollision_eq_terminal_add_lowCostAfterUnused n
  omega

/-! ### PRIM-L073.5: terminal charge on the outside support region -/

theorem two_mul_terminalKeys_le_outsideDepthCollisionSupportCost
    (n : ℕ) :
    2 * (paritySafeTerminalSurvivingFarProductKeys n).card ≤
      paritySafeSupportExcessOutsideDepthCollision n := by
  have hdisjoint :=
    paritySafeTerminalFarProductSeats_disjoint_depthFiberCollisionSeats n
  have htermSub : paritySafeTerminalFarProductSeats n ⊆
      squareAnchorOddPointCoprimeOffsets n \
        paritySafeRechargeExactDepthFiberCollisionSeats n := by
    intro r hr
    exact Finset.mem_sdiff.mpr ⟨
      paritySafeTerminalFarProductSeats_subset_candidate n hr,
      fun hcollision => Finset.disjoint_left.mp hdisjoint hr hcollision⟩
  have hsumle :
      (∑ r ∈ paritySafeTerminalFarProductSeats n,
        ((paritySafeActiveSupport n r).card - 1)) ≤
      ∑ r ∈ squareAnchorOddPointCoprimeOffsets n \
        paritySafeRechargeExactDepthFiberCollisionSeats n,
        ((paritySafeActiveSupport n r).card - 1) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg htermSub
    intro r _ _
    exact Nat.zero_le _
  calc
    2 * (paritySafeTerminalSurvivingFarProductKeys n).card =
        2 * (paritySafeTerminalFarProductSeats n).card := by
      rw [paritySafeTerminalFarProductSeats_card_eq_terminalKeys]
    _ = ∑ r ∈ paritySafeTerminalFarProductSeats n,
        ((paritySafeActiveSupport n r).card - 1) := by
      exact (paritySafeTerminalFarProductSeats_supportCost_sum_eq n).symm
    _ ≤ _ := hsumle

/-! ### PRIM-L073.6: reduced support-charge frontier -/

theorem twoTerminal_add_nineCollision_add_threeFiveDirection_le_outsideSupport_add_threeCollisionSupport
    (n : ℕ) :
    2 * (paritySafeTerminalSurvivingFarProductKeys n).card +
      9 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
      3 * (paritySafeRechargeExactDepthFiveDirectionCollisionSeats n).card ≤
        paritySafeSupportExcessOutsideDepthCollision n +
        3 * paritySafeDepthCollisionLocalSupportCost n := by
  have hterm := two_mul_terminalKeys_le_outsideDepthCollisionSupportCost n
  have hcharge := three_mul_collision_add_fiveDirection_card_le_depthCollisionLocalSupportCost n
  omega

/-! ### PRIM-L073.7: redundancy of the second cancellation -/

theorem twoOutsidePair_add_nineCollision_add_threeFiveDirection_le_threeSupport_add_twoAfterUnused
    (n : ℕ) :
    2 * paritySafePairOverlapOutsideDepthCollision n +
      9 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
      3 * (paritySafeRechargeExactDepthFiveDirectionCollisionSeats n).card ≤
        3 * paritySafeSupportExcess n +
        2 * paritySafeLowCostResidualMassAfterUnused n := by
  have hpair :=
    paritySafePairOverlapOutsideDepthCollision_eq_outsideSupport_add_terminal_add_lowCostAfterUnused n
  have hsupp := paritySafeSupportExcess_eq_outsideCollision_add_collisionSupportCost n
  have hcharge :=
    twoTerminal_add_nineCollision_add_threeFiveDirection_le_outsideSupport_add_threeCollisionSupport n
  omega

theorem paritySafeSecondCancellationFrontier_iff_reducedSupportCharge
    (n : ℕ) :
    (2 * paritySafePairOverlapOutsideDepthCollision n +
        9 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
        3 * (paritySafeRechargeExactDepthFiveDirectionCollisionSeats n).card ≤
      3 * paritySafeSupportExcess n +
        2 * paritySafeLowCostResidualMassAfterUnused n) ↔
    (2 * (paritySafeTerminalSurvivingFarProductKeys n).card +
        9 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
        3 * (paritySafeRechargeExactDepthFiveDirectionCollisionSeats n).card ≤
      paritySafeSupportExcessOutsideDepthCollision n +
        3 * paritySafeDepthCollisionLocalSupportCost n) := by
  have hpair :=
    paritySafePairOverlapOutsideDepthCollision_eq_outsideSupport_add_terminal_add_lowCostAfterUnused n
  have hsupp := paritySafeSupportExcess_eq_outsideCollision_add_collisionSupportCost n
  omega

/-! ### PRIM-L073.8: full-cover form of the same equivalence -/

theorem paritySafeFullCoverSecondCancellationFrontier_iff_reducedSupportCharge
    {n : ℕ}
    (hn : 0 < n)
    (hfull : SquareOffsetsFullyCovered n) :
    (2 * paritySafePairOverlapOutsideDepthCollision n +
        9 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
        3 * (paritySafeRechargeExactDepthFiveDirectionCollisionSeats n).card +
        3 * Nat.totient (2 * n) ≤
      3 * paritySafeIncidenceCount n +
        2 * paritySafeLowCostResidualMassAfterUnused n) ↔
    (2 * (paritySafeTerminalSurvivingFarProductKeys n).card +
        9 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
        3 * (paritySafeRechargeExactDepthFiveDirectionCollisionSeats n).card ≤
      paritySafeSupportExcessOutsideDepthCollision n +
        3 * paritySafeDepthCollisionLocalSupportCost n) := by
  have hpair :=
    paritySafePairOverlapOutsideDepthCollision_eq_outsideSupport_add_terminal_add_lowCostAfterUnused n
  have hsupp := paritySafeSupportExcess_eq_outsideCollision_add_collisionSupportCost n
  have hbalance := paritySafeCandidate_card_add_supportExcess_eq_incidence_of_fullyCovered hn hfull
  have hcard := card_squareAnchorOddPointCoprimeOffsets_eq_totient_two_mul hn
  omega

end
end DkMath.NumberTheory.Legendre
