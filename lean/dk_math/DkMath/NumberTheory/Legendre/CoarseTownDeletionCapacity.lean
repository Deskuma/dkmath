/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.CoarseTownSupportPacking
import DkMath.NumberTheory.Legendre.OldSupportCapacityCertificate
import Mathlib.Data.Finset.Lattice.Fold

#print "file: DkMath.NumberTheory.Legendre.CoarseTownDeletionCapacity"

/-! Exact deterministic deletion capacity and a theorem-backed prime-fiber computation. -/

namespace DkMath.NumberTheory.Legendre

open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.StructuralArithmetic
open DkMath.Combinatorics

/-- The exact first-endpoint deletion carrier specialized to full-town support. -/
noncomputable abbrev coarseTownDeletionVertices (S : Finset ℕ) (n : ℕ) : Finset ℕ :=
  supportCollisionDeletionVertices (coarsePrimeWorldFullTown S n) (squareOffsetPrimeSupport n)

noncomputable abbrev coarseTownPackingRemainder (S : Finset ℕ) (n : ℕ) : Finset ℕ :=
  supportPackingRemainder (coarsePrimeWorldFullTown S n) (squareOffsetPrimeSupport n)

@[simp] theorem mem_coarseTownDeletionVertices {S : Finset ℕ} {n a : ℕ} :
    a ∈ coarseTownDeletionVertices S n ↔ ∃ b, (a,b) ∈ coarseTownSupportCollisionEdges S n :=
  mem_supportCollisionDeletionVertices

@[simp] theorem mem_coarseTownPackingRemainder {S : Finset ℕ} {n a : ℕ} :
    a ∈ coarseTownPackingRemainder S n ↔
      a ∈ coarsePrimeWorldFullTown S n ∧ a ∉ coarseTownDeletionVertices S n :=
  mem_supportPackingRemainder

theorem coarseTownDeletionVertices_subset (S : Finset ℕ) (n : ℕ) :
    coarseTownDeletionVertices S n ⊆ coarsePrimeWorldFullTown S n :=
  supportCollisionDeletionVertices_subset _ _

theorem coarseTownPackingRemainder_subset (S : Finset ℕ) (n : ℕ) :
    coarseTownPackingRemainder S n ⊆ coarsePrimeWorldFullTown S n :=
  supportPackingRemainder_subset _ _

theorem disjoint_coarseTownRemainder_deletion (S : Finset ℕ) (n : ℕ) :
    Disjoint (coarseTownPackingRemainder S n) (coarseTownDeletionVertices S n) :=
  disjoint_supportPackingRemainder_deletion _ _

theorem coarseTownRemainder_union_deletion (S : Finset ℕ) (n : ℕ) :
    coarseTownPackingRemainder S n ∪ coarseTownDeletionVertices S n = coarsePrimeWorldFullTown S n :=
  supportPackingRemainder_union_deletion _ _

theorem coarseTownPackingRemainder_family (S : Finset ℕ) (n : ℕ) :
    PairwiseOldSupportDisjointSquareSeatFamily n (coarseTownPackingRemainder S n) := by
  refine ⟨?_, supportPackingRemainder_pairwiseDisjoint _ _⟩
  intro a ha
  exact mem_squareOffsets.mp (coarseFullTown_subset_squareOffsets S n
    (coarseTownPackingRemainder_subset S n ha))

theorem card_coarseTownDeletion_partition (S : Finset ℕ) (n : ℕ) :
    (coarsePrimeWorldFullTown S n).card =
      (coarseTownPackingRemainder S n).card + (coarseTownDeletionVertices S n).card :=
  card_supportPacking_partition _ _

theorem card_coarseTownPackingRemainder (S : Finset ℕ) (n : ℕ) :
    (coarseTownPackingRemainder S n).card =
      (coarsePrimeWorldFullTown S n).card - (coarseTownDeletionVertices S n).card := by
  rw [card_coarseTownDeletion_partition S n]
  omega

theorem coarseTownDeletion_period_partition {S : Finset ℕ} (hS : KnownPrimeScales S) (n : ℕ) :
    coarsePrimeWorldPeriodCount S n * Nat.totient (primeWorldModulus S) =
      (coarseTownPackingRemainder S n).card + (coarseTownDeletionVertices S n).card := by
  rw [← card_coarsePrimeWorldFullTown hS n, card_coarseTownDeletion_partition]

theorem card_coarseTownDeletionVertices_le_edges (S : Finset ℕ) (n : ℕ) :
    (coarseTownDeletionVertices S n).card ≤ (coarseTownSupportCollisionEdges S n).card :=
  card_supportCollisionDeletionVertices_le_edges _ _

theorem coarseTown_deletion_deficit_of_edge_deficit (S : Finset ℕ) {n : ℕ}
    (h : (primeScalesUpTo n).card + (coarseTownSupportCollisionEdges S n).card <
      (coarsePrimeWorldFullTown S n).card) :
    (primeScalesUpTo n).card + (coarseTownDeletionVertices S n).card <
      (coarsePrimeWorldFullTown S n).card :=
  lt_of_le_of_lt (Nat.add_le_add_left (card_coarseTownDeletionVertices_le_edges S n) _) h

theorem not_fullyCovered_of_coarseTown_deletion_deficit (S : Finset ℕ) {n : ℕ}
    (h : (primeScalesUpTo n).card + (coarseTownDeletionVertices S n).card <
      (coarsePrimeWorldFullTown S n).card) : ¬ SquareOffsetsFullyCovered n := by
  apply not_fullyCovered_of_primeWorld_card_lt_pairwiseOldSupportDisjointSquareSeatFamilies
    (coarseTownPackingRemainder_family S n)
  have hp := card_coarseTownDeletion_partition S n
  omega

theorem exists_prime_squareCell_of_coarseTown_deletion_deficit (S : Finset ℕ) {n : ℕ}
    (hn : 0 < n)
    (h : (primeScalesUpTo n).card + (coarseTownDeletionVertices S n).card <
      (coarsePrimeWorldFullTown S n).card) : ∃ p, p.Prime ∧ SquareCell n p := by
  apply exists_prime_squareCell_of_primeWorld_card_lt_pairwiseOldSupportDisjointSquareSeatFamilies
    hn (coarseTownPackingRemainder_family S n)
  have hp := card_coarseTownDeletion_partition S n
  omega

/-- Exact arithmetic fiber implementation, not precomputed support labels. -/
def coarseTownDivisibilityFiber (S : Finset ℕ) (n q : ℕ) : Finset ℕ :=
  oldSupportSeatFiber n (coarsePrimeWorldFullTown S n) q

/-- A cheap computation of the same deletion carrier: omit the maximum of each prime fiber. -/
def coarseTownDeletionByFibers (S : Finset ℕ) (n : ℕ) : Finset ℕ :=
  (primeScalesUpTo n).biUnion (fun q =>
    let F := coarseTownDivisibilityFiber S n q
    F.filter (fun a => a < F.sup id))

/-- Exact prime-fiber compression of the symbolic first-endpoint deletion. -/
theorem coarseTownDeletionVertices_eq_fibers (S : Finset ℕ) (n : ℕ) :
    coarseTownDeletionVertices S n = coarseTownDeletionByFibers S n := by
  classical
  ext a
  rw [mem_coarseTownDeletionVertices]
  simp only [coarseTownDeletionByFibers, Finset.mem_biUnion, Finset.mem_filter, Finset.lt_sup_iff]
  constructor
  · rintro ⟨b, hab⟩
    obtain ⟨ha, hb, hlt, hnd⟩ := mem_coarseTownSupportCollisionEdges.mp hab
    obtain ⟨q, hq⟩ := Finset.not_disjoint_iff_nonempty_inter.mp hnd
    have hqa := mem_squareOffsetPrimeSupport.mp (Finset.mem_inter.mp hq).1
    have hqb := mem_squareOffsetPrimeSupport.mp (Finset.mem_inter.mp hq).2
    exact ⟨q, mem_primeScalesUpTo.mpr ⟨hqa.1, hqa.2.1⟩,
      Finset.mem_filter.mpr ⟨ha, hqa.2.2⟩,
      b, Finset.mem_filter.mpr ⟨hb, hqb.2.2⟩, hlt⟩
  · rintro ⟨q, hq, ha, b, hb, hlt⟩
    have ha' := Finset.mem_filter.mp ha
    have hb' := Finset.mem_filter.mp hb
    have hp := mem_primeScalesUpTo.mp hq
    refine ⟨b, mem_coarseTownSupportCollisionEdges.mpr ⟨ha'.1, hb'.1, hlt, ?_⟩⟩
    intro hdisj
    exact Finset.disjoint_left.mp hdisj
      (mem_squareOffsetPrimeSupport.mpr ⟨hp.1, hp.2, ha'.2⟩)
      (mem_squareOffsetPrimeSupport.mpr ⟨hp.1, hp.2, hb'.2⟩)

end DkMath.NumberTheory.Legendre
