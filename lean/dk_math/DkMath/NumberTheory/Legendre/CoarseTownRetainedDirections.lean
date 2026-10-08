/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.CoarseTownDeletionConservation
import DkMath.Combinatorics.FinsetSupportDirections

#print "file: DkMath.NumberTheory.Legendre.CoarseTownRetainedDirections"

/-! Retained actual directions and the exact two components of selector loss. -/
namespace DkMath.NumberTheory.Legendre

open DkMath.Combinatorics DkMath.NumberTheory.Primitive DkMath.NumberTheory.StructuralArithmetic

noncomputable def coarseTownRetainedSupportedSeats (S : Finset ℕ) (n : ℕ) :=
  supportedSeats (coarseTownPackingRemainder S n) (squareOffsetPrimeSupport n)

noncomputable def coarseTownRepresentedPrimes (S : Finset ℕ) (n : ℕ) :=
  representedDirections (coarseTownPackingRemainder S n) (squareOffsetPrimeSupport n)

noncomputable def coarseTownUnrepresentedActivePrimes (S : Finset ℕ) (n : ℕ) :=
  coarseFullTownActivePrimes S n \ coarseTownRepresentedPrimes S n

noncomputable def coarseTownRetainedSupportExcess (S : Finset ℕ) (n : ℕ) :=
  retainedExcess (coarseTownPackingRemainder S n) (squareOffsetPrimeSupport n)

@[simp] theorem mem_coarseTownRetainedSupportedSeats {S : Finset ℕ} {n a : ℕ} :
    a ∈ coarseTownRetainedSupportedSeats S n ↔
      a ∈ coarseTownPackingRemainder S n ∧ (squareOffsetPrimeSupport n a).Nonempty := by
  classical
  exact Finset.mem_filter

/-- Exact carrier partition, shared by every retained family containing uncovered seats. -/
theorem coarseTown_retained_partition (S : Finset ℕ) (n : ℕ) {R : Finset ℕ}
    (hR : R ⊆ coarsePrimeWorldFullTown S n) (hU : coarseFullTownUncoveredSeats S n ⊆ R) :
    coarseFullTownUncoveredSeats S n ∪ supportedSeats R (squareOffsetPrimeSupport n) = R ∧
      Disjoint (coarseFullTownUncoveredSeats S n) (supportedSeats R (squareOffsetPrimeSupport n)) := by
  classical
  have he : emptySupportSeats R (squareOffsetPrimeSupport n) =
      coarseFullTownUncoveredSeats S n := by
    ext a
    simp only [emptySupportSeats,Finset.mem_filter,mem_coarseFullTownUncoveredSeats]
    exact ⟨fun h => ⟨hR h.1,h.2⟩,fun h => ⟨hU (mem_coarseFullTownUncoveredSeats.mpr h),h.2⟩⟩
  rw [← he]
  exact ⟨emptySupportSeats_union_supported R (squareOffsetPrimeSupport n),
    disjoint_emptySupportSeats_supported R (squareOffsetPrimeSupport n)⟩

/-- Shared cardinality adapter derived from the exact disjoint carrier partition. -/
theorem coarseTown_card_retained_split (S : Finset ℕ) (n : ℕ) {R : Finset ℕ}
    (hR : R ⊆ coarsePrimeWorldFullTown S n) (hU : coarseFullTownUncoveredSeats S n ⊆ R) :
    R.card = (coarseFullTownUncoveredSeats S n).card +
      (supportedSeats R (squareOffsetPrimeSupport n)).card := by
  have h := coarseTown_retained_partition S n hR hU
  have hc := Finset.card_union_of_disjoint h.2
  rw [h.1] at hc
  exact hc

theorem coarseTown_represented_subset_active {S : Finset ℕ} (hS : KnownPrimeScales S)
    (n : ℕ) {R : Finset ℕ} (hR : R ⊆ coarsePrimeWorldFullTown S n) :
    representedDirections R (squareOffsetPrimeSupport n) ⊆ coarseFullTownActivePrimes S n := by
  intro q hq
  obtain ⟨a,ha,hqa⟩ := Finset.mem_biUnion.mp hq
  exact mem_coarseFullTownActivePrimes.mpr
    ⟨coarse_survivor_support_outside (coarseFullTown_survivor hS (hR ha)) hqa,
      a,Finset.mem_filter.mpr ⟨hR ha,hqa⟩⟩

/-- Shared loss decomposition for either orientation, using only its exact remainder ledger. -/
theorem coarseTown_retained_loss_decomposition {S : Finset ℕ} (hS : KnownPrimeScales S)
    (n : ℕ) {R : Finset ℕ} {L : ℕ} (hR : R ⊆ coarsePrimeWorldFullTown S n)
    (hU : coarseFullTownUncoveredSeats S n ⊆ R)
    (hd : (R : Set ℕ).PairwiseDisjoint (squareOffsetPrimeSupport n))
    (hl : R.card + L = (coarseFullTownUncoveredSeats S n).card +
      (coarseFullTownActivePrimes S n).card) :
    L = (coarseFullTownActivePrimes S n \ representedDirections R (squareOffsetPrimeSupport n)).card +
      retainedExcess R (squareOffsetPrimeSupport n) := by
  have hs := coarseTown_card_retained_split S n hR hU
  have hr := card_representedDirections R (squareOffsetPrimeSupport n) hd
  have ha := Finset.card_sdiff_add_card_eq_card (coarseTown_represented_subset_active hS n hR)
  omega

def coarseTownFiberMaximumAt (S : Finset ℕ) (n q a : ℕ) : Prop :=
  a ∈ coarseFullTownPrimeFiber S n q ∧ ∀ b ∈ coarseFullTownPrimeFiber S n q, b ≤ a

def coarseTownFiberMinimumAt (S : Finset ℕ) (n q a : ℕ) : Prop :=
  a ∈ coarseFullTownPrimeFiber S n q ∧ ∀ b ∈ coarseFullTownPrimeFiber S n q, a ≤ b

theorem mem_coarseTownPackingRemainder_iff_maxima {S : Finset ℕ} {n a : ℕ}
    (ha : a ∈ coarsePrimeWorldFullTown S n) :
    a ∈ coarseTownPackingRemainder S n ↔
      ∀ q ∈ squareOffsetPrimeSupport n a, coarseTownFiberMaximumAt S n q a := by
  rw [mem_supportPackingRemainder_iff_maxima ha]
  constructor
  · intro hm q hq
    exact ⟨Finset.mem_filter.mpr ⟨ha,hq⟩,fun b hb =>
      hm q hq b (Finset.mem_filter.mp hb).1 (Finset.mem_filter.mp hb).2⟩
  · intro hm q hq b hb hqb
    exact (hm q hq).2 b (Finset.mem_filter.mpr ⟨hb,hqb⟩)

theorem mem_coarseTownRightPackingRemainder_iff_minima {S : Finset ℕ} {n a : ℕ}
    (ha : a ∈ coarsePrimeWorldFullTown S n) :
    a ∈ coarseTownRightPackingRemainder S n ↔
      ∀ q ∈ squareOffsetPrimeSupport n a, coarseTownFiberMinimumAt S n q a := by
  rw [mem_supportPackingRightRemainder_iff_minima ha]
  constructor
  · intro hm q hq
    exact ⟨Finset.mem_filter.mpr ⟨ha,hq⟩,fun b hb =>
      hm q hq b (Finset.mem_filter.mp hb).1 (Finset.mem_filter.mp hb).2⟩
  · intro hm q hq b hb hqb
    exact (hm q hq).2 b (Finset.mem_filter.mpr ⟨hb,hqb⟩)

theorem coarseFullTownUncoveredSeats_subset_remainder (S : Finset ℕ) (n : ℕ) :
    coarseFullTownUncoveredSeats S n ⊆ coarseTownPackingRemainder S n := by
  intro a ha
  have h := mem_coarseFullTownUncoveredSeats.mp ha
  apply (mem_coarseTownPackingRemainder_iff_maxima h.1).mpr
  rw [h.2]
  simp

theorem coarseFullTownUncoveredSeats_subset_rightRemainder (S : Finset ℕ) (n : ℕ) :
    coarseFullTownUncoveredSeats S n ⊆ coarseTownRightPackingRemainder S n := by
  intro a ha
  have h := mem_coarseFullTownUncoveredSeats.mp ha
  apply (mem_coarseTownRightPackingRemainder_iff_minima h.1).mpr
  rw [h.2]
  simp

theorem coarseTown_remainder_partition (S : Finset ℕ) (n : ℕ) :
    coarseFullTownUncoveredSeats S n ∪ coarseTownRetainedSupportedSeats S n =
      coarseTownPackingRemainder S n ∧
      Disjoint (coarseFullTownUncoveredSeats S n) (coarseTownRetainedSupportedSeats S n) :=
  coarseTown_retained_partition S n (coarseTownPackingRemainder_subset S n)
    (coarseFullTownUncoveredSeats_subset_remainder S n)

theorem coarseTown_remainder_card_split (S : Finset ℕ) (n : ℕ) :
    (coarseTownPackingRemainder S n).card = (coarseFullTownUncoveredSeats S n).card +
      (coarseTownRetainedSupportedSeats S n).card :=
  coarseTown_card_retained_split S n (coarseTownPackingRemainder_subset S n)
    (coarseFullTownUncoveredSeats_subset_remainder S n)

theorem coarseTownRepresentedPrimes_subset_active {S : Finset ℕ} (hS : KnownPrimeScales S) (n : ℕ) :
    coarseTownRepresentedPrimes S n ⊆ coarseFullTownActivePrimes S n :=
  coarseTown_represented_subset_active hS n (coarseTownPackingRemainder_subset S n)

theorem coarseTownRepresentedPrimes_subset_outside {S : Finset ℕ} (hS : KnownPrimeScales S) (n : ℕ) :
    coarseTownRepresentedPrimes S n ⊆ coarseOutsidePrimes S n :=
  (coarseTownRepresentedPrimes_subset_active hS n).trans (coarseFullTownActivePrimes_subset S n)

theorem coarseTownRepresentedPrimes_unique (S : Finset ℕ) (n : ℕ) {q : ℕ}
    (hq : q ∈ coarseTownRepresentedPrimes S n) :
    ∃! a, a ∈ coarseTownPackingRemainder S n ∧ q ∈ squareOffsetPrimeSupport n a :=
  representedDirections_unique _ _ (coarseTownPackingRemainder_family S n).2 hq

theorem coarseTown_active_partition {S : Finset ℕ} (hS : KnownPrimeScales S) (n : ℕ) :
    coarseTownRepresentedPrimes S n ∪ coarseTownUnrepresentedActivePrimes S n =
      coarseFullTownActivePrimes S n :=
  Finset.union_sdiff_of_subset (coarseTownRepresentedPrimes_subset_active hS n)

theorem coarseTown_active_partition_disjoint (S : Finset ℕ) (n : ℕ) :
    Disjoint (coarseTownRepresentedPrimes S n) (coarseTownUnrepresentedActivePrimes S n) :=
  Finset.disjoint_sdiff

theorem coarseTown_active_card_partition {S : Finset ℕ} (hS : KnownPrimeScales S) (n : ℕ) :
    (coarseTownRepresentedPrimes S n).card + (coarseTownUnrepresentedActivePrimes S n).card =
      (coarseFullTownActivePrimes S n).card := by
  unfold coarseTownUnrepresentedActivePrimes
  have h := Finset.card_sdiff_add_card_eq_card (coarseTownRepresentedPrimes_subset_active hS n)
  omega

theorem coarseTown_represented_card_split (S : Finset ℕ) (n : ℕ) :
    (coarseTownRepresentedPrimes S n).card = (coarseTownRetainedSupportedSeats S n).card +
      coarseTownRetainedSupportExcess S n :=
  card_representedDirections _ _ (coarseTownPackingRemainder_family S n).2

theorem coarseTown_loss_decomposition {S : Finset ℕ} (hS : KnownPrimeScales S) (n : ℕ) :
    coarseTownSupportLoss S n = (coarseTownUnrepresentedActivePrimes S n).card +
      coarseTownRetainedSupportExcess S n :=
  coarseTown_retained_loss_decomposition hS n (coarseTownPackingRemainder_subset S n)
    (coarseFullTownUncoveredSeats_subset_remainder S n) (coarseTownPackingRemainder_family S n).2
    (coarseTown_remainder_add_loss_eq_uncovered_add_active hS n)

end DkMath.NumberTheory.Legendre
