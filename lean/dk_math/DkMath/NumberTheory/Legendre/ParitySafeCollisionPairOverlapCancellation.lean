/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.ParitySafeFifthDirectionGate

#print "file: DkMath.NumberTheory.Legendre.ParitySafeCollisionPairOverlapCancellation"

/-!
## ParitySafeCollisionPairOverlapCancellation

PRIM-L068 identifies the depth residual-pair capacity as an internal part of
the collision pair-overlap mass.  The collision surface is split from its
candidate complement, and the collision summand is rewritten as local support
cost plus one collision unit plus the L058 residual term.

This removes the named depth-residual and higher-support capacities from the
resulting full-cover frontier.  It is an exact finite ledger calculation; it
does not introduce a fifth-wave count, a descent, an analytic estimate, or a
Legendre/RH conclusion.
-/

namespace DkMath.NumberTheory.Legendre

open scoped BigOperators

noncomputable section
local instance classicalDecidableCollisionCancellation (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-! ### PRIM-L068.1: named collision support cost -/

/-- The candidate-side local support cost of all exact-depth collision seats. -/
noncomputable def paritySafeDepthCollisionLocalSupportCost (n : ℕ) : ℕ :=
  ∑ r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n,
    ((paritySafeActiveSupport n r).card - 1)

/-- The L067 strengthened collision charge in the named local-cost notation. -/
theorem three_mul_collision_add_fiveDirection_card_le_depthCollisionLocalSupportCost
    (n : ℕ) :
    3 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
      (paritySafeRechargeExactDepthFiveDirectionCollisionSeats n).card ≤
        paritySafeDepthCollisionLocalSupportCost n := by
  simpa [paritySafeDepthCollisionLocalSupportCost] using
    (three_mul_collision_add_fiveDirection_card_le_localSupportCost n)

/-! ### PRIM-L068.2: collision and outside pair-overlap masses -/

/-- Pair-overlap mass contributed by exact-depth collision seats. -/
noncomputable def paritySafeDepthCollisionPairOverlapMass (n : ℕ) : ℕ :=
  ∑ r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n,
    Nat.choose (paritySafeActiveSupport n r).card 2

/-- Pair-overlap mass on candidate seats outside the exact-depth collision
surface. -/
noncomputable def paritySafePairOverlapOutsideDepthCollision (n : ℕ) : ℕ :=
  ∑ r ∈
      (squareAnchorOddPointCoprimeOffsets n \
        paritySafeRechargeExactDepthFiberCollisionSeats n),
    Nat.choose (paritySafeActiveSupport n r).card 2

/-- Exact split of the pair-overlap ledger into collision and outside mass. -/
theorem paritySafePrimePairOverlapCount_eq_outsideCollision_add_collisionMass
    (n : ℕ) :
    paritySafePrimePairOverlapCount n =
      paritySafePairOverlapOutsideDepthCollision n +
      paritySafeDepthCollisionPairOverlapMass n := by
  have hsub := paritySafeRechargeExactDepthFiberCollisionSeats_subset_candidate n
  have hdisjoint : Disjoint
      (squareAnchorOddPointCoprimeOffsets n \
        paritySafeRechargeExactDepthFiberCollisionSeats n)
      (paritySafeRechargeExactDepthFiberCollisionSeats n) :=
    Finset.sdiff_disjoint
  have hunion := Finset.sdiff_union_of_subset hsub
  unfold paritySafePrimePairOverlapCount
    paritySafePairOverlapOutsideDepthCollision
    paritySafeDepthCollisionPairOverlapMass
  calc
    (∑ r ∈ squareAnchorOddPointCoprimeOffsets n,
        Nat.choose (paritySafeActiveSupport n r).card 2) =
        ∑ r ∈ (squareAnchorOddPointCoprimeOffsets n \
          paritySafeRechargeExactDepthFiberCollisionSeats n) ∪
            paritySafeRechargeExactDepthFiberCollisionSeats n,
          Nat.choose (paritySafeActiveSupport n r).card 2 := by
      rw [hunion]
    _ = (∑ r ∈ squareAnchorOddPointCoprimeOffsets n \
          paritySafeRechargeExactDepthFiberCollisionSeats n,
        Nat.choose (paritySafeActiveSupport n r).card 2) +
        ∑ r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n,
          Nat.choose (paritySafeActiveSupport n r).card 2 := by
      rw [Finset.sum_union hdisjoint]

/-! ### PRIM-L068.3: local collision pair identity -/

private theorem choose_two_eq_sub_one_add_choose_sub_one (k : ℕ) :
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

/-- On a collision seat, pair-overlap mass is local support cost, one collision
unit, and the exact L058 residual capacity. -/
theorem paritySafeDepthCollision_localPairOverlap_eq_supportCost_add_one_add_residualCapacity
    {n r : ℕ}
    (hr : r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n) :
    Nat.choose (paritySafeActiveSupport n r).card 2 =
      ((paritySafeActiveSupport n r).card - 1) +
      1 +
      (Nat.choose ((paritySafeActiveSupport n r).card - 1) 2 - 1) := by
  have hfour := paritySafeRechargeExactDepthFiberCollision_support_card_ge_four hr
  have hchoosepos : 0 < Nat.choose ((paritySafeActiveSupport n r).card - 1) 2 := by
    apply Nat.choose_pos
    omega
  have hbin := choose_two_eq_sub_one_add_choose_sub_one
    (paritySafeActiveSupport n r).card
  omega

/-! ### PRIM-L068.4: exact collision mass decomposition -/

/-- Exact collision pair-overlap decomposition into support cost, collision
baseline, and depth residual capacity. -/
theorem paritySafeDepthCollisionPairOverlapMass_eq_supportCost_add_collision_add_depthResidualCapacity
    (n : ℕ) :
    paritySafeDepthCollisionPairOverlapMass n =
      paritySafeDepthCollisionLocalSupportCost n +
      (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
      paritySafeRechargeExactDepthResidualPairCapacityExcess n := by
  unfold paritySafeDepthCollisionPairOverlapMass
    paritySafeDepthCollisionLocalSupportCost
    paritySafeRechargeExactDepthResidualPairCapacityExcess
  calc
    (∑ r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n,
        Nat.choose (paritySafeActiveSupport n r).card 2) =
        ∑ r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n,
          (((paritySafeActiveSupport n r).card - 1) + 1 +
            (Nat.choose ((paritySafeActiveSupport n r).card - 1) 2 - 1)) := by
      apply Finset.sum_congr rfl
      intro r hr
      exact paritySafeDepthCollision_localPairOverlap_eq_supportCost_add_one_add_residualCapacity hr
    _ = (∑ r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n,
          ((paritySafeActiveSupport n r).card - 1)) +
          (∑ _r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n, 1) +
          ∑ r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n,
            (Nat.choose ((paritySafeActiveSupport n r).card - 1) 2 - 1) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ = _ := by simp [Nat.add_assoc, Nat.add_comm]

/-! ### PRIM-L068.5: eliminate depth residual capacity -/

/-- The L065 doubled frontier after exact collision-mass cancellation; the
named depth residual capacity no longer appears in the conclusion. -/
theorem two_mul_outsideCollisionPairOverlap_add_twoCollisionSupportCost_add_fiveCollision_le_threeSupportExcess_add_twoLowCostCapacity
    (n : ℕ) :
    2 * paritySafePairOverlapOutsideDepthCollision n +
      2 * paritySafeDepthCollisionLocalSupportCost n +
      5 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card ≤
        3 * paritySafeSupportExcess n +
        2 * paritySafeLowCostResidualCapacity n := by
  have hfront :=
    two_mul_pairOverlap_add_threeCollision_le_threeSupportExcess_add_twoLowCostCapacity_add_twoDepthResidualCapacity n
  have hsplit := paritySafePrimePairOverlapCount_eq_outsideCollision_add_collisionMass n
  have hcollision :=
    paritySafeDepthCollisionPairOverlapMass_eq_supportCost_add_collision_add_depthResidualCapacity n
  omega

/-! ### PRIM-L068.6: readable fifth-charge frontier -/

/-- The collision frontier after replacing local residual capacity by the
L067 fifth-direction support charge. -/
theorem two_mul_outsideCollisionPairOverlap_add_elevenCollision_add_twoFiveDirection_le_threeSupportExcess_add_twoLowCostCapacity
    (n : ℕ) :
    2 * paritySafePairOverlapOutsideDepthCollision n +
      11 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
      2 * (paritySafeRechargeExactDepthFiveDirectionCollisionSeats n).card ≤
        3 * paritySafeSupportExcess n +
        2 * paritySafeLowCostResidualCapacity n := by
  have hcancel :=
    two_mul_outsideCollisionPairOverlap_add_twoCollisionSupportCost_add_fiveCollision_le_threeSupportExcess_add_twoLowCostCapacity n
  have hcharge :=
    three_mul_collision_add_fiveDirection_card_le_depthCollisionLocalSupportCost n
  omega

/-! ### PRIM-L068.7: full-cover candidate and totient frontiers -/

/-- Full-cover candidate-card form of the cancellation frontier. -/
theorem two_mul_outsideCollisionPairOverlap_add_elevenCollision_add_twoFiveDirection_add_threeCandidate_le_fullCoverLowCostCapacity
    {n : ℕ}
    (hn : 0 < n)
    (hfull : SquareOffsetsFullyCovered n) :
    2 * paritySafePairOverlapOutsideDepthCollision n +
      11 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
      2 * (paritySafeRechargeExactDepthFiveDirectionCollisionSeats n).card +
      3 * (squareAnchorOddPointCoprimeOffsets n).card ≤
        3 * paritySafeIncidenceCount n +
        2 * paritySafeLowCostResidualCapacity n := by
  have hfront :=
    two_mul_outsideCollisionPairOverlap_add_elevenCollision_add_twoFiveDirection_le_threeSupportExcess_add_twoLowCostCapacity n
  have hbalance := paritySafeCandidate_card_add_supportExcess_eq_incidence_of_fullyCovered hn hfull
  omega

/-- Totient form of the L068 full-cover cancellation frontier. -/
theorem two_mul_outsideCollisionPairOverlap_add_elevenCollision_add_twoFiveDirection_add_threeTotient_le_fullCoverLowCostCapacity
    {n : ℕ}
    (hn : 0 < n)
    (hfull : SquareOffsetsFullyCovered n) :
    2 * paritySafePairOverlapOutsideDepthCollision n +
      11 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
      2 * (paritySafeRechargeExactDepthFiveDirectionCollisionSeats n).card +
      3 * Nat.totient (2 * n) ≤
        3 * paritySafeIncidenceCount n +
        2 * paritySafeLowCostResidualCapacity n := by
  have hfront :=
    two_mul_outsideCollisionPairOverlap_add_elevenCollision_add_twoFiveDirection_add_threeCandidate_le_fullCoverLowCostCapacity hn hfull
  have hcard := card_squareAnchorOddPointCoprimeOffsets_eq_totient_two_mul hn
  omega

/-- Reduced quotient-interval form of the L068 full-cover cancellation
frontier. -/
theorem two_mul_outsideCollisionPairOverlap_add_elevenCollision_add_twoFiveDirection_add_threeTotient_le_reducedQuotient_fullCoverLowCostCapacity
    {n : ℕ}
    (hn : 0 < n)
    (hfull : SquareOffsetsFullyCovered n) :
    2 * paritySafePairOverlapOutsideDepthCollision n +
      11 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
      2 * (paritySafeRechargeExactDepthFiveDirectionCollisionSeats n).card +
      3 * Nat.totient (2 * n) ≤
        3 * (∑ q ∈ squareAnchorOddActivePrimes n,
          (paritySafeReducedQuotientInterval n q).card) +
        2 * paritySafeLowCostResidualCapacity n := by
  have hfront :=
    two_mul_outsideCollisionPairOverlap_add_elevenCollision_add_twoFiveDirection_add_threeTotient_le_fullCoverLowCostCapacity hn hfull
  rw [paritySafeIncidenceCount_eq_reducedQuotientInterval_sum] at hfront
  exact hfront

end
end DkMath.NumberTheory.Legendre
