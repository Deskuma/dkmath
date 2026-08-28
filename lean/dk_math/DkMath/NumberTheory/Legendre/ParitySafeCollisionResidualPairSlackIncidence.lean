/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.ParitySafeActualFiberCancellation

#print "file: DkMath.NumberTheory.Legendre.ParitySafeCollisionResidualPairSlackIncidence"

/-!
## ParitySafeCollisionResidualPairSlackIncidence

PRIM-L071 realizes the abstract collision residual-pair slack as a finite
sum of local unused-pair cardinalities.  At each collision seat, the existing
reverse-key map sends the exact-depth fiber into the canonical residual-pair
universe; the complement of that image is the unused local mass.

The module therefore turns zero slack into a structural saturation statement
and positive slack into an actual unused residual-pair witness.  It does not
interpret such a witness as a new prime direction, a wave, a descent step,
or a contradiction.
-/

namespace DkMath.NumberTheory.Legendre

open scoped BigOperators

/-! ### PRIM-L071.1: fixed-seat realized image -/

/-- Residual-pair image of the exact-depth fiber at a fixed seat. -/
noncomputable def paritySafeRechargeExactDepthResidualPairImageAtSeat
    (n r : ℕ) : Finset (ℕ × ℕ) :=
  (paritySafeRechargeExactDepthPairsAtSeat n r).image
    (fun bt => (paritySafeRechargeExactKeyOfPair n bt).2)

/-- The realized residual-pair image lies in the canonical local universe. -/
theorem paritySafeRechargeExactDepthResidualPairImageAtSeat_subset_canonicalResidualPairs
    {n r : ℕ} :
    paritySafeRechargeExactDepthResidualPairImageAtSeat n r ⊆
      paritySafeCanonicalResidualPairsAtSeat n r := by
  intro qs hqs
  rcases Finset.mem_image.mp hqs with ⟨bt, hbt, rfl⟩
  exact paritySafeRechargeExactDepthPair_residualPair_mem hbt

/-- Fixed-seat image cardinality equals the exact-depth fiber cardinality. -/
theorem paritySafeRechargeExactDepthResidualPairImageAtSeat_card_eq_fiber
    (n r : ℕ) :
    (paritySafeRechargeExactDepthResidualPairImageAtSeat n r).card =
      (paritySafeRechargeExactDepthPairsAtSeat n r).card := by
  unfold paritySafeRechargeExactDepthResidualPairImageAtSeat
  apply Finset.card_image_of_injOn
  exact paritySafeRechargeExactDepthPair_residualPair_injectiveOn

/-! ### PRIM-L071.2: local unused residual pairs -/

/-- Residual pairs in the canonical target not realized by the depth fiber. -/
noncomputable def paritySafeDepthCollisionUnusedResidualPairsAtSeat
    (n r : ℕ) : Finset (ℕ × ℕ) :=
  paritySafeCanonicalResidualPairsAtSeat n r \
    paritySafeRechargeExactDepthResidualPairImageAtSeat n r

/-- A collision seat is a covered parity-safe candidate. -/
theorem paritySafeDepthFiberCollisionSeat_mem_covered
    {n r : ℕ}
    (hr : r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n) :
    r ∈ paritySafeCoveredCandidates n := by
  have hseat := (mem_paritySafeRechargeExactDepthFiberCollisionSeats.mp hr).1
  rcases paritySafeRechargeExactDepthPairsAtSeat_nonempty_of_mem_depthSeats hseat with
    ⟨bt, hbt⟩
  exact paritySafeRechargeExactDepthPair_mem_covered hbt

/-- Local unused-pair cardinality is target capacity minus fiber cardinality. -/
theorem paritySafeDepthCollisionUnusedResidualPairsAtSeat_card_eq_capacity_sub_fiber
    {n r : ℕ}
    (hr : r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n) :
    (paritySafeDepthCollisionUnusedResidualPairsAtSeat n r).card =
      Nat.choose ((paritySafeActiveSupport n r).card - 1) 2 -
        (paritySafeRechargeExactDepthPairsAtSeat n r).card := by
  have hsubset :=
    paritySafeRechargeExactDepthResidualPairImageAtSeat_subset_canonicalResidualPairs
      (n := n) (r := r)
  have htarget := paritySafeCanonicalResidualPairsAtSeat_card_eq_choose
    (paritySafeDepthFiberCollisionSeat_mem_covered hr)
  have himage := paritySafeRechargeExactDepthResidualPairImageAtSeat_card_eq_fiber n r
  unfold paritySafeDepthCollisionUnusedResidualPairsAtSeat
  rw [Finset.card_sdiff_of_subset hsubset, htarget, himage]

/-! ### PRIM-L071.3: global unused residual-pair mass -/

/-- Sum of local residual pairs unused by collision-seat depth fibers. -/
noncomputable def paritySafeDepthCollisionUnusedResidualPairMass
    (n : ℕ) : ℕ :=
  ∑ r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n,
    (paritySafeDepthCollisionUnusedResidualPairsAtSeat n r).card

/-- Residual-pair capacity splits into actual fiber excess and unused mass. -/
theorem paritySafeRechargeExactDepthResidualPairCapacityExcess_eq_fiberExcess_add_unusedResidualPairMass
    (n : ℕ) :
    paritySafeRechargeExactDepthResidualPairCapacityExcess n =
      paritySafeRechargeExactDepthFiberExcess n +
        paritySafeDepthCollisionUnusedResidualPairMass n := by
  rw [paritySafeRechargeExactDepthFiberExcess_eq_collision_sum]
  unfold paritySafeRechargeExactDepthResidualPairCapacityExcess
    paritySafeDepthCollisionUnusedResidualPairMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  have hseat := (mem_paritySafeRechargeExactDepthFiberCollisionSeats.mp hr).1
  have hcollision := (mem_paritySafeRechargeExactDepthFiberCollisionSeats.mp hr).2
  have hcapacity := paritySafeRechargeExactDepthPairsAtSeat_card_le_choose_support hseat
  have hunused :=
    paritySafeDepthCollisionUnusedResidualPairsAtSeat_card_eq_capacity_sub_fiber hr
  rw [hunused]
  omega

/-- L070's abstract collision slack is exactly the unused residual-pair mass. -/
theorem paritySafeDepthCollisionResidualPairSlack_eq_unusedResidualPairMass
    (n : ℕ) :
    paritySafeDepthCollisionResidualPairSlack n =
      paritySafeDepthCollisionUnusedResidualPairMass n := by
  have hcapacity :=
    paritySafeRechargeExactDepthResidualPairCapacityExcess_eq_fiberExcess_add_unusedResidualPairMass n
  unfold paritySafeDepthCollisionResidualPairSlack
  omega

/-! ### PRIM-L071.4: saturation at zero slack -/

/-- Local unused-pair emptiness is equivalent to image saturation. -/
theorem paritySafeDepthCollisionUnusedResidualPairsAtSeat_eq_empty_iff_image_eq_target
    {n r : ℕ}
    (_hr : r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n) :
    paritySafeDepthCollisionUnusedResidualPairsAtSeat n r = ∅ ↔
      paritySafeRechargeExactDepthResidualPairImageAtSeat n r =
        paritySafeCanonicalResidualPairsAtSeat n r := by
  have hsubset :=
    paritySafeRechargeExactDepthResidualPairImageAtSeat_subset_canonicalResidualPairs
      (n := n) (r := r)
  constructor
  · intro hzero
    have htarget_subset := Finset.sdiff_eq_empty_iff_subset.mp hzero
    exact Finset.Subset.antisymm hsubset htarget_subset
  · intro heq
    apply Finset.sdiff_eq_empty_iff_subset.mpr
    rw [heq]

/-- Zero collision slack means every local image saturates its target. -/
theorem paritySafeDepthCollisionResidualPairSlack_eq_zero_iff_all_collision_images_saturate
    (n : ℕ) :
    paritySafeDepthCollisionResidualPairSlack n = 0 ↔
      ∀ r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n,
        paritySafeRechargeExactDepthResidualPairImageAtSeat n r =
          paritySafeCanonicalResidualPairsAtSeat n r := by
  rw [paritySafeDepthCollisionResidualPairSlack_eq_unusedResidualPairMass]
  unfold paritySafeDepthCollisionUnusedResidualPairMass
  rw [Finset.sum_eq_zero_iff_of_nonneg]
  · constructor
    · intro hzero r hr
      apply (paritySafeDepthCollisionUnusedResidualPairsAtSeat_eq_empty_iff_image_eq_target hr).mp
      exact Finset.card_eq_zero.mp (hzero r hr)
    · intro hsat r hr
      exact Finset.card_eq_zero.mpr
        ((paritySafeDepthCollisionUnusedResidualPairsAtSeat_eq_empty_iff_image_eq_target hr).mpr
          (hsat r hr))
  · intro r hr
    exact Nat.zero_le _

/-- Zero slack gives surjectivity from the exact fiber onto each local target. -/
theorem paritySafeDepthCollision_residualPair_surjective_of_slack_eq_zero
    {n r : ℕ}
    (hzero : paritySafeDepthCollisionResidualPairSlack n = 0)
    (hr : r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n)
    {qs : ℕ × ℕ}
    (hqs : qs ∈ paritySafeCanonicalResidualPairsAtSeat n r) :
    ∃ bt ∈ paritySafeRechargeExactDepthPairsAtSeat n r,
      (paritySafeRechargeExactKeyOfPair n bt).2 = qs := by
  have hsat :=
    (paritySafeDepthCollisionResidualPairSlack_eq_zero_iff_all_collision_images_saturate n).mp
      hzero r hr
  have himage : qs ∈ paritySafeRechargeExactDepthResidualPairImageAtSeat n r := by
    rw [hsat]
    exact hqs
  rcases Finset.mem_image.mp himage with ⟨bt, hbt, hpair⟩
  exact ⟨bt, hbt, hpair⟩

/-! ### PRIM-L071.5: positive slack witnesses -/

/-- Positive slack produces a collision seat with an unused residual pair. -/
theorem exists_unused_collisionResidualPair_of_residualPairSlack_pos
    {n : ℕ}
    (hpos : 0 < paritySafeDepthCollisionResidualPairSlack n) :
    ∃ r,
      r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n ∧
      (paritySafeDepthCollisionUnusedResidualPairsAtSeat n r).Nonempty := by
  rw [paritySafeDepthCollisionResidualPairSlack_eq_unusedResidualPairMass] at hpos
  unfold paritySafeDepthCollisionUnusedResidualPairMass at hpos
  have hwitness :=
    (Finset.sum_pos_iff_of_nonneg (fun _ _ => Nat.zero_le _)).mp hpos
  rcases hwitness with ⟨r, hr, hcard⟩
  exact ⟨r, hr, Finset.card_pos.mp hcard⟩

/-- Positive slack produces an explicitly unrealized canonical residual pair. -/
theorem exists_unrealized_collisionResidualPair_of_residualPairSlack_pos
    {n : ℕ}
    (hpos : 0 < paritySafeDepthCollisionResidualPairSlack n) :
    ∃ r qs,
      r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n ∧
      qs ∈ paritySafeCanonicalResidualPairsAtSeat n r ∧
      qs ∉ paritySafeRechargeExactDepthResidualPairImageAtSeat n r := by
  rcases exists_unused_collisionResidualPair_of_residualPairSlack_pos hpos with
    ⟨r, hr, hnonempty⟩
  rcases hnonempty with ⟨qs, hqs⟩
  rcases Finset.mem_sdiff.mp hqs with ⟨hcanonical, hnotimage⟩
  exact ⟨r, qs, hr, hcanonical, hnotimage⟩

/-! ### PRIM-L071.6: L070 frontier with realized unused mass -/

/-- L070 readable frontier with the abstract slack replaced by unused mass. -/
theorem two_mul_outsideCollisionPairOverlap_add_nineCollision_add_threeFiveDirection_add_twoUnusedResidualPairMass_le_threeSupportExcess_add_twoLowCostMass
    (n : ℕ) :
    2 * paritySafePairOverlapOutsideDepthCollision n +
      9 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
      3 * (paritySafeRechargeExactDepthFiveDirectionCollisionSeats n).card +
      2 * paritySafeDepthCollisionUnusedResidualPairMass n ≤
        3 * paritySafeSupportExcess n +
        2 * paritySafeLowCostResidualMass n := by
  have hfront :=
    two_mul_outsideCollisionPairOverlap_add_nineCollision_add_threeFiveDirection_add_twoResidualSlack_le_threeSupportExcess_add_twoLowCostMass n
  have hslack := paritySafeDepthCollisionResidualPairSlack_eq_unusedResidualPairMass n
  omega

/-- Totient full-cover form with realized unused residual-pair mass. -/
theorem two_mul_outsideCollisionPairOverlap_add_nineCollision_add_threeFiveDirection_add_twoUnusedResidualPairMass_add_threeTotient_le_fullCoverActualMass
    {n : ℕ}
    (hn : 0 < n)
    (hfull : SquareOffsetsFullyCovered n) :
    2 * paritySafePairOverlapOutsideDepthCollision n +
      9 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
      3 * (paritySafeRechargeExactDepthFiveDirectionCollisionSeats n).card +
      2 * paritySafeDepthCollisionUnusedResidualPairMass n +
      3 * Nat.totient (2 * n) ≤
        3 * paritySafeIncidenceCount n +
        2 * paritySafeLowCostResidualMass n := by
  have hfront :=
    two_mul_outsideCollisionPairOverlap_add_nineCollision_add_threeFiveDirection_add_twoResidualSlack_add_threeTotient_le_fullCoverActualMass hn hfull
  have hslack := paritySafeDepthCollisionResidualPairSlack_eq_unusedResidualPairMass n
  omega

/-- Reduced quotient-interval form with realized unused residual-pair mass. -/
theorem two_mul_outsideCollisionPairOverlap_add_nineCollision_add_threeFiveDirection_add_twoUnusedResidualPairMass_add_threeTotient_le_reducedQuotient_fullCoverActualMass
    {n : ℕ}
    (hn : 0 < n)
    (hfull : SquareOffsetsFullyCovered n) :
    2 * paritySafePairOverlapOutsideDepthCollision n +
      9 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
      3 * (paritySafeRechargeExactDepthFiveDirectionCollisionSeats n).card +
      2 * paritySafeDepthCollisionUnusedResidualPairMass n +
      3 * Nat.totient (2 * n) ≤
        3 * (∑ q ∈ squareAnchorOddActivePrimes n,
          (paritySafeReducedQuotientInterval n q).card) +
        2 * paritySafeLowCostResidualMass n := by
  have hfront :=
    two_mul_outsideCollisionPairOverlap_add_nineCollision_add_threeFiveDirection_add_twoUnusedResidualPairMass_add_threeTotient_le_fullCoverActualMass hn hfull
  rw [paritySafeIncidenceCount_eq_reducedQuotientInterval_sum] at hfront
  exact hfront

end DkMath.NumberTheory.Legendre
