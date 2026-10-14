/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.CoarseTownDeletionCapacity

#print "file: DkMath.NumberTheory.Legendre.CoarseTownSurvivorCapacity"

/-! Actual support capacity inside the certified survivor world. -/

namespace DkMath.NumberTheory.Legendre

open DkMath.NumberTheory.Primitive DkMath.NumberTheory.StructuralArithmetic
open DkMath.Combinatorics

theorem card_fullTown_pairwiseOldSupportDisjoint_le_outsidePrimes_of_fullyCovered
    {S : Finset ℕ} (hS : KnownPrimeScales S) {n : ℕ} {R : Finset ℕ}
    (hR : R ⊆ coarsePrimeWorldFullTown S n)
    (hf : PairwiseOldSupportDisjointSquareSeatFamily n R)
    (hc : SquareOffsetsFullyCovered n) : R.card ≤ (coarseOutsidePrimes S n).card := by
  apply card_le_supportUniverse R (squareOffsetPrimeSupport n) (coarseOutsidePrimes S n)
  · intro a ha
    exact squareOffsetCovered_iff_primeSupport_nonempty.mp (hc a (hf.1 a ha))
  · intro a ha
    exact coarse_survivor_support_outside (coarseFullTown_survivor hS (hR ha))
  · exact hf.2

theorem not_fullyCovered_of_fullTown_survivor_capacity
    {S : Finset ℕ} (hS : KnownPrimeScales S) {n : ℕ} {R : Finset ℕ}
    (hR : R ⊆ coarsePrimeWorldFullTown S n)
    (hf : PairwiseOldSupportDisjointSquareSeatFamily n R)
    (h : (coarseOutsidePrimes S n).card < R.card) : ¬ SquareOffsetsFullyCovered n := by
  intro hc
  exact (not_le_of_gt h) (card_fullTown_pairwiseOldSupportDisjoint_le_outsidePrimes_of_fullyCovered
    hS hR hf hc)

/-- Pointwise use of the established Frontier equivalence. -/
theorem exists_prime_squareCell_of_not_fullyCovered {n : ℕ} (hn : 0 < n)
    (h : ¬ SquareOffsetsFullyCovered n) : ∃ p, p.Prime ∧ SquareCell n p := by
  -- Supply only this anchor to the existing escape-to-prime arithmetic.
  obtain ⟨r, hr⟩ := not_squareOffsetsFullyCovered_iff_escaping_nonempty.mp h
  have hs := mem_escapingSquareOffsets.mp hr
  exact ⟨n ^ 2 + r, prime_of_squareAnchoredSupportEscape hn hs.1
    (supportDisjointFrom_primeScalesUpTo_square_add_iff_not_covered.mpr hs.2),
    (squareCell_iff_exists_squareOffset n (n ^ 2 + r)).mpr ⟨r, hs.1, rfl⟩⟩

theorem exists_prime_squareCell_of_fullTown_survivor_capacity
    {S : Finset ℕ} (hS : KnownPrimeScales S) {n : ℕ} {R : Finset ℕ} (hn : 0 < n)
    (hR : R ⊆ coarsePrimeWorldFullTown S n)
    (hf : PairwiseOldSupportDisjointSquareSeatFamily n R)
    (h : (coarseOutsidePrimes S n).card < R.card) : ∃ p, p.Prime ∧ SquareCell n p :=
  exists_prime_squareCell_of_not_fullyCovered hn
    (not_fullyCovered_of_fullTown_survivor_capacity hS hR hf h)

theorem not_fullyCovered_of_coarseTown_outside_deletion_deficit
    {S : Finset ℕ} (hS : KnownPrimeScales S) {n : ℕ}
    (h : (coarseOutsidePrimes S n).card + (coarseTownDeletionVertices S n).card <
      (coarsePrimeWorldFullTown S n).card) : ¬ SquareOffsetsFullyCovered n := by
  apply not_fullyCovered_of_fullTown_survivor_capacity hS
    (coarseTownPackingRemainder_subset S n) (coarseTownPackingRemainder_family S n)
  have hp := card_coarseTownDeletion_partition S n
  omega

theorem exists_prime_squareCell_of_coarseTown_outside_deletion_deficit
    {S : Finset ℕ} (hS : KnownPrimeScales S) {n : ℕ} (hn : 0 < n)
    (h : (coarseOutsidePrimes S n).card + (coarseTownDeletionVertices S n).card <
      (coarsePrimeWorldFullTown S n).card) : ∃ p, p.Prime ∧ SquareCell n p :=
  exists_prime_squareCell_of_not_fullyCovered hn
    (not_fullyCovered_of_coarseTown_outside_deletion_deficit hS h)

theorem coarseTown_outside_deletion_deficit_of_old_deficit (S : Finset ℕ) {n : ℕ}
    (h : (primeScalesUpTo n).card + (coarseTownDeletionVertices S n).card <
      (coarsePrimeWorldFullTown S n).card) :
    (coarseOutsidePrimes S n).card + (coarseTownDeletionVertices S n).card <
      (coarsePrimeWorldFullTown S n).card := by
  have ht : (coarseOutsidePrimes S n).card ≤ (primeScalesUpTo n).card :=
    Finset.card_le_card Finset.sdiff_subset
  omega

noncomputable abbrev coarseTownRightDeletionVertices (S : Finset ℕ) (n : ℕ) :=
  supportCollisionRightDeletionVertices (coarsePrimeWorldFullTown S n) (squareOffsetPrimeSupport n)

noncomputable abbrev coarseTownRightPackingRemainder (S : Finset ℕ) (n : ℕ) :=
  supportPackingRightRemainder (coarsePrimeWorldFullTown S n) (squareOffsetPrimeSupport n)

theorem coarseTownRightPackingRemainder_subset (S : Finset ℕ) (n : ℕ) :
    coarseTownRightPackingRemainder S n ⊆ coarsePrimeWorldFullTown S n := Finset.sdiff_subset

theorem coarseTownRightDeletionVertices_subset (S : Finset ℕ) (n : ℕ) :
    coarseTownRightDeletionVertices S n ⊆ coarsePrimeWorldFullTown S n :=
  supportCollisionRightDeletionVertices_subset _ _

theorem coarseTownRightPackingRemainder_family (S : Finset ℕ) (n : ℕ) :
    PairwiseOldSupportDisjointSquareSeatFamily n (coarseTownRightPackingRemainder S n) := by
  refine ⟨?_, supportPackingRightRemainder_pairwiseDisjoint _ _⟩
  intro a ha
  exact mem_squareOffsets.mp (coarseFullTown_subset_squareOffsets S n
    (coarseTownRightPackingRemainder_subset S n ha))

theorem card_coarseTownRightDeletion_partition (S : Finset ℕ) (n : ℕ) :
    (coarsePrimeWorldFullTown S n).card = (coarseTownRightPackingRemainder S n).card +
      (coarseTownRightDeletionVertices S n).card := card_supportPackingRight_partition _ _

theorem not_fullyCovered_of_coarseTown_outside_right_deletion_deficit
    {S : Finset ℕ} (hS : KnownPrimeScales S) {n : ℕ}
    (h : (coarseOutsidePrimes S n).card + (coarseTownRightDeletionVertices S n).card <
      (coarsePrimeWorldFullTown S n).card) : ¬ SquareOffsetsFullyCovered n := by
  apply not_fullyCovered_of_fullTown_survivor_capacity hS
    (coarseTownRightPackingRemainder_subset S n) (coarseTownRightPackingRemainder_family S n)
  have hp := card_coarseTownRightDeletion_partition S n
  omega

theorem exists_prime_squareCell_of_coarseTown_outside_right_deletion_deficit
    {S : Finset ℕ} (hS : KnownPrimeScales S) {n : ℕ} (hn : 0 < n)
    (h : (coarseOutsidePrimes S n).card + (coarseTownRightDeletionVertices S n).card <
      (coarsePrimeWorldFullTown S n).card) : ∃ p, p.Prime ∧ SquareCell n p :=
  exists_prime_squareCell_of_not_fullyCovered hn
    (not_fullyCovered_of_coarseTown_outside_right_deletion_deficit hS h)

/-- Computable minimum-fiber compression of the existing right endpoint carrier. -/
def coarseTownRightDeletionByFibers (S : Finset ℕ) (n : ℕ) : Finset ℕ :=
  (primeScalesUpTo n).biUnion (fun q =>
    let F := coarseTownDivisibilityFiber S n q
    if h : F.Nonempty then F.erase (F.min' h) else ∅)

theorem coarseTownRightDeletionVertices_eq_fibers (S : Finset ℕ) (n : ℕ) :
    coarseTownRightDeletionVertices S n = coarseTownRightDeletionByFibers S n := by
  classical
  have hmin (F : Finset ℕ) (a : ℕ) :
      a ∈ (if h : F.Nonempty then F.erase (F.min' h) else ∅) ↔
        a ∈ F ∧ ∃ b ∈ F, b < a := by
    by_cases h : F.Nonempty
    · simp only [dite_eq_left h, Finset.mem_erase]
      constructor
      · rintro ⟨hne, ha⟩
        exact ⟨ha, F.min' h, Finset.min'_mem F h, lt_of_le_of_ne (Finset.min'_le F a ha) hne.symm⟩
      · rintro ⟨ha, b, hb, hlt⟩
        exact ⟨by have := Finset.min'_le F b hb; omega, ha⟩
    · have he := Finset.not_nonempty_iff_eq_empty.mp h
      simp [he]
  ext a
  rw [mem_supportCollisionRightDeletionVertices]
  change (∃ b, (b, a) ∈ supportCollisionEdges (coarsePrimeWorldFullTown S n)
    (squareOffsetPrimeSupport n)) ↔ _
  simp only [coarseTownRightDeletionByFibers, Finset.mem_biUnion, hmin]
  constructor
  · rintro ⟨b, hb⟩
    obtain ⟨hbV, haV, hlt, hnd⟩ := mem_supportCollisionEdges.mp hb
    obtain ⟨q, hq⟩ := Finset.not_disjoint_iff_nonempty_inter.mp hnd
    have hqb := mem_squareOffsetPrimeSupport.mp (Finset.mem_inter.mp hq).1
    have hqa := mem_squareOffsetPrimeSupport.mp (Finset.mem_inter.mp hq).2
    exact ⟨q, mem_primeScalesUpTo.mpr ⟨hqa.1, hqa.2.1⟩,
      Finset.mem_filter.mpr ⟨haV, hqa.2.2⟩, b,
      Finset.mem_filter.mpr ⟨hbV, hqb.2.2⟩, hlt⟩
  · rintro ⟨q, hq, ha, b, hb, hlt⟩
    have hp := mem_primeScalesUpTo.mp hq
    have ha' := Finset.mem_filter.mp ha
    have hb' := Finset.mem_filter.mp hb
    refine ⟨b, mem_supportCollisionEdges.mpr ⟨hb'.1, ha'.1, hlt, ?_⟩⟩
    intro hd
    exact Finset.disjoint_left.mp hd
      (mem_squareOffsetPrimeSupport.mpr ⟨hp.1, hp.2, hb'.2⟩)
      (mem_squareOffsetPrimeSupport.mpr ⟨hp.1, hp.2, ha'.2⟩)

end DkMath.NumberTheory.Legendre
