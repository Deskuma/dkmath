/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.ParitySafeChargedResidualLedger

#print "file: DkMath.NumberTheory.Legendre.ParitySafeLowCostResidualSplit"

/-!
## ParitySafeLowCostResidualSplit

PRIM-L062 splits exact-depth seats into collision and noncollision fibers.
Collision seats carry the already charged support cost together with their
depth-seat base and one unit of fiber excess, exposing effective weight five.
The remaining low-cost residual consists of near incidences, noncollision
depth seats, and fourth-direction incidences.

The module is a finite ledger refinement only.  It does not add near counting,
fourth-direction injectivity, descent, or a contradiction.
-/

namespace DkMath.NumberTheory.Legendre

open scoped BigOperators

/-! ### PRIM-L062.1: exact depth split -/

/-- Exact-depth seats that are not collision seats. -/
noncomputable def paritySafeRechargeExactDepthNonCollisionSeats
    (n : ℕ) : Finset ℕ :=
  paritySafeRechargeExactDepthSeats n \
    paritySafeRechargeExactDepthFiberCollisionSeats n

@[simp] theorem mem_paritySafeRechargeExactDepthNonCollisionSeats
    {n r : ℕ} :
    r ∈ paritySafeRechargeExactDepthNonCollisionSeats n ↔
      r ∈ paritySafeRechargeExactDepthSeats n ∧
      r ∉ paritySafeRechargeExactDepthFiberCollisionSeats n := by
  simp [paritySafeRechargeExactDepthNonCollisionSeats]

/-- Collision seats are a subset of the occupied exact-depth seats. -/
theorem paritySafeRechargeExactDepthFiberCollisionSeats_subset_depthSeats
    (n : ℕ) :
    paritySafeRechargeExactDepthFiberCollisionSeats n ⊆
      paritySafeRechargeExactDepthSeats n := by
  intro r hr
  exact (mem_paritySafeRechargeExactDepthFiberCollisionSeats.mp hr).1

/-- Noncollision and collision depth seats are disjoint. -/
theorem paritySafeRechargeExactDepthNonCollision_collision_disjoint
    (n : ℕ) :
    Disjoint
      (paritySafeRechargeExactDepthNonCollisionSeats n)
      (paritySafeRechargeExactDepthFiberCollisionSeats n) := by
  rw [Finset.disjoint_left]
  intro r hnoncollision hcollision
  exact (mem_paritySafeRechargeExactDepthNonCollisionSeats.mp hnoncollision).2
    hcollision

/-- The noncollision/collision union recovers all exact-depth seats. -/
theorem paritySafeRechargeExactDepthNonCollision_collision_union
    (n : ℕ) :
    paritySafeRechargeExactDepthNonCollisionSeats n ∪
        paritySafeRechargeExactDepthFiberCollisionSeats n =
      paritySafeRechargeExactDepthSeats n := by
  ext r
  constructor
  · intro hr
    rcases Finset.mem_union.mp hr with hnoncollision | hcollision
    · exact (mem_paritySafeRechargeExactDepthNonCollisionSeats.mp hnoncollision).1
    · exact (mem_paritySafeRechargeExactDepthFiberCollisionSeats.mp hcollision).1
  · intro hr
    by_cases hcollision :
        r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n
    · exact Finset.mem_union.mpr (Or.inr hcollision)
    · exact Finset.mem_union.mpr (Or.inl
        (mem_paritySafeRechargeExactDepthNonCollisionSeats.mpr
          ⟨hr, hcollision⟩))

/-- Exact-depth seat cardinality split into noncollision and collision seats. -/
theorem paritySafeRechargeExactDepthSeats_card_eq_nonCollision_add_collision
    (n : ℕ) :
    (paritySafeRechargeExactDepthSeats n).card =
      (paritySafeRechargeExactDepthNonCollisionSeats n).card +
      (paritySafeRechargeExactDepthFiberCollisionSeats n).card := by
  rw [← paritySafeRechargeExactDepthNonCollision_collision_union n]
  exact Finset.card_union_of_disjoint
    (paritySafeRechargeExactDepthNonCollision_collision_disjoint n)

/-! ### PRIM-L062.2: noncollision fiber semantics -/

/-- A noncollision depth seat has exactly one depth pair in its fiber. -/
theorem paritySafeRechargeExactDepthPairsAtSeat_card_eq_one_of_mem_nonCollision
    {n r : ℕ}
    (hr : r ∈ paritySafeRechargeExactDepthNonCollisionSeats n) :
    (paritySafeRechargeExactDepthPairsAtSeat n r).card = 1 := by
  have hmem := mem_paritySafeRechargeExactDepthNonCollisionSeats.mp hr
  have hpos :=
    paritySafeRechargeExactDepthPairsAtSeat_card_pos_of_mem_depthSeats hmem.1
  have hnot : ¬ 2 ≤
      (paritySafeRechargeExactDepthPairsAtSeat n r).card := by
    intro htwo
    apply hmem.2
    exact mem_paritySafeRechargeExactDepthFiberCollisionSeats.mpr
      ⟨hmem.1, htwo⟩
  omega

/-! ### PRIM-L062.3: noncollision upper-control consumer -/

/-- Noncollision depth seats remain bounded by the L018 prime-square budget. -/
theorem paritySafeRechargeExactDepthNonCollisionSeats_card_le_primeSquareDepthBudget
    (n : ℕ) :
    (paritySafeRechargeExactDepthNonCollisionSeats n).card ≤
      squareAnchorCoprimePrimeSquareDepthBudget n := by
  apply (Finset.card_le_card ?_).trans
    (paritySafeRechargeExactDepthSeats_card_le_primeSquareDepthBudget n)
  intro r hr
  exact (mem_paritySafeRechargeExactDepthNonCollisionSeats.mp hr).1

/-! ### PRIM-L062.4: explicit collision weight five -/

/-- The readable weight-five lower frontier at prime-pair overlap level. -/
theorem paritySafeNear_add_threeTerminal_add_nonCollisionDepth_add_fiveCollision_add_fourth_le_primePairOverlapCount
    (n : ℕ) :
    (paritySafeCanonicalNearResidualTripleIncidences n).card +
      3 * (paritySafeTerminalSurvivingFarProductKeys n).card +
      (paritySafeRechargeExactDepthNonCollisionSeats n).card +
      5 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
      (paritySafeRechargeExactFourthDirectionPairs n).card ≤
        paritySafePrimePairOverlapCount n := by
  have hfrontier :=
    paritySafeNear_add_threeTerminal_add_depthSeats_add_fourCollision_add_fourth_le_primePairOverlapCount n
  rw [paritySafeRechargeExactDepthSeats_card_eq_nonCollision_add_collision] at hfrontier
  omega

/-- The weight-five lower frontier transported to coprime pair capacity. -/
theorem paritySafeNear_add_threeTerminal_add_nonCollisionDepth_add_fiveCollision_add_fourth_le_coprimePrimePairOverlapCount
    (n : ℕ) :
    (paritySafeCanonicalNearResidualTripleIncidences n).card +
      3 * (paritySafeTerminalSurvivingFarProductKeys n).card +
      (paritySafeRechargeExactDepthNonCollisionSeats n).card +
      5 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
      (paritySafeRechargeExactFourthDirectionPairs n).card ≤
        squareAnchorCoprimePrimePairOverlapCount n := by
  exact
    (paritySafeNear_add_threeTerminal_add_nonCollisionDepth_add_fiveCollision_add_fourth_le_primePairOverlapCount n).trans
      (paritySafePrimePairOverlapCount_le_squareAnchorCoprimePrimePairOverlapCount n)

/-! ### PRIM-L062.5: readable low-cost residual -/

/-- The uncharged finite residual: near, noncollision depth, and fourth. -/
noncomputable def paritySafeLowCostResidualMass (n : ℕ) : ℕ :=
  (paritySafeCanonicalNearResidualTripleIncidences n).card +
  (paritySafeRechargeExactDepthNonCollisionSeats n).card +
  (paritySafeRechargeExactFourthDirectionPairs n).card

/-- The low-cost residual plus terminal/collision charges fits in pair overlap. -/
theorem paritySafeLowCostResidualMass_add_threeTerminal_add_fiveCollision_le_pairOverlap
    (n : ℕ) :
    paritySafeLowCostResidualMass n +
      3 * (paritySafeTerminalSurvivingFarProductKeys n).card +
      5 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card ≤
        paritySafePrimePairOverlapCount n := by
  unfold paritySafeLowCostResidualMass
  have hfrontier :=
    paritySafeNear_add_threeTerminal_add_nonCollisionDepth_add_fiveCollision_add_fourth_le_primePairOverlapCount n
  omega

/-- The low-cost residual frontier transported to coprime pair capacity. -/
theorem paritySafeLowCostResidualMass_add_threeTerminal_add_fiveCollision_le_coprimePrimePairOverlap
    (n : ℕ) :
    paritySafeLowCostResidualMass n +
      3 * (paritySafeTerminalSurvivingFarProductKeys n).card +
      5 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card ≤
        squareAnchorCoprimePrimePairOverlapCount n := by
  exact
    (paritySafeLowCostResidualMass_add_threeTerminal_add_fiveCollision_le_pairOverlap n).trans
      (paritySafePrimePairOverlapCount_le_squareAnchorCoprimePrimePairOverlapCount n)

end DkMath.NumberTheory.Legendre
