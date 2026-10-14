/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.CoarseTownRetainedDirections

#print "file: DkMath.NumberTheory.Legendre.CoarseTownSymmetricDeletion"

/-! Minimum-fiber conservation and a transparent better-of-two selector. -/
namespace DkMath.NumberTheory.Legendre

open DkMath.Combinatorics DkMath.NumberTheory.Primitive DkMath.NumberTheory.StructuralArithmetic
open scoped BigOperators

@[simp] theorem mem_coarseTownRightPackingRemainder {S : Finset ℕ} {n a : ℕ} :
    a ∈ coarseTownRightPackingRemainder S n ↔
      a ∈ coarsePrimeWorldFullTown S n ∧ a ∉ coarseTownRightDeletionVertices S n :=
  Finset.mem_sdiff

noncomputable def coarseTownNonminimumFiberSeats (S : Finset ℕ) (n q : ℕ) : Finset ℕ := by
  classical
  let F := coarseFullTownPrimeFiber S n q
  exact F.filter (fun a => ∃ b ∈ F, b < a)

@[simp] theorem mem_coarseTownNonminimumFiberSeats {S : Finset ℕ} {n q a : ℕ} :
    a ∈ coarseTownNonminimumFiberSeats S n q ↔
      a ∈ coarseFullTownPrimeFiber S n q ∧ ∃ b ∈ coarseFullTownPrimeFiber S n q, b < a := by
  classical
  exact Finset.mem_filter

theorem card_coarseTownNonminimumFiberSeats_add_indicator (S : Finset ℕ) (n q : ℕ) :
    (coarseTownNonminimumFiberSeats S n q).card +
      (if (coarseFullTownPrimeFiber S n q).Nonempty then 1 else 0) =
        (coarseFullTownPrimeFiber S n q).card := by
  classical
  exact card_nonmaximum_add_indicator (α := ℕᵒᵈ) (coarseFullTownPrimeFiber S n q)

noncomputable def coarseTownRightDeletionWitnessPrimes (S : Finset ℕ) (n a : ℕ) : Finset ℕ := by
  classical
  exact (coarseOutsidePrimes S n).filter (fun q => a ∈ coarseTownNonminimumFiberSeats S n q)

noncomputable def coarseTownRightDeletionMultiplicity (S : Finset ℕ) (n a : ℕ) :=
  (coarseTownRightDeletionWitnessPrimes S n a).card

noncomputable def coarseTownRightDeletionMass (S : Finset ℕ) (n : ℕ) :=
  ∑ a ∈ coarsePrimeWorldFullTown S n, coarseTownRightDeletionMultiplicity S n a

noncomputable def coarseTownRightDeletionOverlap (S : Finset ℕ) (n : ℕ) :=
  ∑ a ∈ coarseTownRightDeletionVertices S n, (coarseTownRightDeletionMultiplicity S n a - 1)

noncomputable def coarseTownRightSupportLoss (S : Finset ℕ) (n : ℕ) :=
  coarseFullTownSupportExcess S n - coarseTownRightDeletionOverlap S n

theorem coarseTownRightDeletionWitnessPrimes_subset_support (S : Finset ℕ) (n a : ℕ) :
    coarseTownRightDeletionWitnessPrimes S n a ⊆ squareOffsetPrimeSupport n a := by
  intro q hq
  exact (Finset.mem_filter.mp (mem_coarseTownNonminimumFiberSeats.mp
    (Finset.mem_filter.mp hq).2).1).2

theorem mem_coarseTownRightDeletionVertices_iff_multiplicity_pos
    {S : Finset ℕ} (hS : KnownPrimeScales S) (n a : ℕ) :
    a ∈ coarseTownRightDeletionVertices S n ↔ 0 < coarseTownRightDeletionMultiplicity S n a := by
  classical
  rw [coarseTownRightDeletionMultiplicity,Finset.card_pos]
  constructor
  · intro ha
    obtain ⟨b,hab⟩ := mem_supportCollisionRightDeletionVertices.mp ha
    obtain ⟨hbV,haV,hlt,hnd⟩ := mem_supportCollisionEdges.mp hab
    obtain ⟨q,hq⟩ := Finset.not_disjoint_iff_nonempty_inter.mp hnd
    have hqa := (Finset.mem_inter.mp hq).2
    refine ⟨q,Finset.mem_filter.mpr ⟨?_,?_⟩⟩
    · exact coarse_survivor_support_outside (coarseFullTown_survivor hS haV) hqa
    · exact mem_coarseTownNonminimumFiberSeats.mpr ⟨Finset.mem_filter.mpr ⟨haV,hqa⟩,
        b,Finset.mem_filter.mpr ⟨hbV,(Finset.mem_inter.mp hq).1⟩,hlt⟩
  · rintro ⟨q,hq⟩
    have h := mem_coarseTownNonminimumFiberSeats.mp (Finset.mem_filter.mp hq).2
    obtain ⟨b,hb,hlt⟩ := h.2
    have haF := Finset.mem_filter.mp h.1
    have hbF := Finset.mem_filter.mp hb
    refine mem_supportCollisionRightDeletionVertices.mpr ⟨b,
      mem_supportCollisionEdges.mpr ⟨hbF.1,haF.1,hlt,?_⟩⟩
    intro hd
    exact Finset.disjoint_left.mp hd hbF.2 haF.2

theorem coarseTownRightDeletionMass_eq_nonminimum_sum (S : Finset ℕ) (n : ℕ) :
    coarseTownRightDeletionMass S n =
      ∑ q ∈ coarseOutsidePrimes S n, (coarseTownNonminimumFiberSeats S n q).card := by
  classical
  apply sum_witness_cards
  intro q _hq a ha
  exact (Finset.mem_filter.mp (mem_coarseTownNonminimumFiberSeats.mp ha).1).1

theorem coarseTownRightDeletionMass_eq_left (S : Finset ℕ) (n : ℕ) :
    coarseTownRightDeletionMass S n = coarseTownDeletionMass S n := by
  rw [coarseTownRightDeletionMass_eq_nonminimum_sum,coarseTownDeletionMass_eq_nonmaximum_sum]
  apply Finset.sum_congr rfl
  intro q _hq
  have hl := card_coarseTownNonmaximumFiberSeats_add_indicator S n q
  have hr := card_coarseTownNonminimumFiberSeats_add_indicator S n q
  omega

theorem coarseTownRightDeletionMass_add_active_eq_incidence (S : Finset ℕ) (n : ℕ) :
    coarseTownRightDeletionMass S n + (coarseFullTownActivePrimes S n).card =
      coarseFullTownIncidence S n := by
  rw [coarseTownRightDeletionMass_eq_left,coarseTownDeletionMass_add_active_eq_incidence]

theorem card_rightDeletion_add_overlap_eq_mass {S : Finset ℕ} (hS : KnownPrimeScales S) (n : ℕ) :
    (coarseTownRightDeletionVertices S n).card + coarseTownRightDeletionOverlap S n =
      coarseTownRightDeletionMass S n := by
  classical
  have he : coarseTownRightDeletionVertices S n = (coarsePrimeWorldFullTown S n).filter
      (fun a => 0 < coarseTownRightDeletionMultiplicity S n a) := by
    ext a
    rw [Finset.mem_filter,← mem_coarseTownRightDeletionVertices_iff_multiplicity_pos hS]
    exact ⟨fun h => ⟨coarseTownRightDeletionVertices_subset S n h,h⟩,fun h => h.2⟩
  unfold coarseTownRightDeletionOverlap coarseTownRightDeletionMass
  rw [show (coarseTownRightDeletionVertices S n).card =
    ∑ _a ∈ coarseTownRightDeletionVertices S n, (1 : ℕ) from by simp]
  rw [← Finset.sum_add_distrib,he,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _ha
  by_cases h : 0 < coarseTownRightDeletionMultiplicity S n a
  · simp only [ite_eq_left h]; omega
  · simp only [ite_eq_right h]; omega

theorem coarseTownRightDeletionOverlap_le_supportExcess (S : Finset ℕ) (n : ℕ) :
    coarseTownRightDeletionOverlap S n ≤ coarseFullTownSupportExcess S n := by
  unfold coarseTownRightDeletionOverlap coarseFullTownSupportExcess
  calc
    _ ≤ ∑ a ∈ coarseTownRightDeletionVertices S n, ((squareOffsetPrimeSupport n a).card - 1) := by
      apply Finset.sum_le_sum
      intro a _ha
      exact Nat.sub_le_sub_right (Finset.card_le_card
        (coarseTownRightDeletionWitnessPrimes_subset_support S n a)) 1
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (coarseTownRightDeletionVertices_subset S n)
      (fun _ _ _ => Nat.zero_le _)

theorem coarseTownRight_remainder_conservation {S : Finset ℕ} (hS : KnownPrimeScales S) (n : ℕ) :
    (coarseTownRightPackingRemainder S n).card + coarseFullTownSupportExcess S n =
      (coarseFullTownUncoveredSeats S n).card + (coarseFullTownActivePrimes S n).card +
        coarseTownRightDeletionOverlap S n := by
  have hp := card_coarseTownRightDeletion_partition S n
  have hs := coarseFullTownIncidence_add_uncovered_eq_card_add_excess hS n
  have hm := coarseTownRightDeletionMass_add_active_eq_incidence S n
  have ho := card_rightDeletion_add_overlap_eq_mass hS n
  omega

theorem coarseTownRight_remainder_add_loss {S : Finset ℕ} (hS : KnownPrimeScales S) (n : ℕ) :
    (coarseTownRightPackingRemainder S n).card + coarseTownRightSupportLoss S n =
      (coarseFullTownUncoveredSeats S n).card + (coarseFullTownActivePrimes S n).card := by
  have hm := coarseTownRight_remainder_conservation hS n
  have ho := coarseTownRightDeletionOverlap_le_supportExcess S n
  unfold coarseTownRightSupportLoss
  omega

noncomputable def coarseTownRightRetainedSupportedSeats (S : Finset ℕ) (n : ℕ) :=
  supportedSeats (coarseTownRightPackingRemainder S n) (squareOffsetPrimeSupport n)

noncomputable def coarseTownRightRepresentedPrimes (S : Finset ℕ) (n : ℕ) :=
  representedDirections (coarseTownRightPackingRemainder S n) (squareOffsetPrimeSupport n)

noncomputable def coarseTownRightUnrepresentedActivePrimes (S : Finset ℕ) (n : ℕ) :=
  coarseFullTownActivePrimes S n \ coarseTownRightRepresentedPrimes S n

noncomputable def coarseTownRightRetainedSupportExcess (S : Finset ℕ) (n : ℕ) :=
  retainedExcess (coarseTownRightPackingRemainder S n) (squareOffsetPrimeSupport n)

@[simp] theorem mem_coarseTownRightRetainedSupportedSeats {S : Finset ℕ} {n a : ℕ} :
    a ∈ coarseTownRightRetainedSupportedSeats S n ↔
      a ∈ coarseTownRightPackingRemainder S n ∧ (squareOffsetPrimeSupport n a).Nonempty := by
  classical
  exact Finset.mem_filter

theorem coarseTownRightRepresentedPrimes_subset_active {S : Finset ℕ} (hS : KnownPrimeScales S) (n : ℕ) :
    coarseTownRightRepresentedPrimes S n ⊆ coarseFullTownActivePrimes S n :=
  coarseTown_represented_subset_active hS n (coarseTownRightPackingRemainder_subset S n)

theorem coarseTownRightRepresentedPrimes_unique (S : Finset ℕ) (n : ℕ) {q : ℕ}
    (hq : q ∈ coarseTownRightRepresentedPrimes S n) :
    ∃! a, a ∈ coarseTownRightPackingRemainder S n ∧ q ∈ squareOffsetPrimeSupport n a :=
  representedDirections_unique _ _ (coarseTownRightPackingRemainder_family S n).2 hq

theorem coarseTownRight_remainder_partition (S : Finset ℕ) (n : ℕ) :
    coarseFullTownUncoveredSeats S n ∪ coarseTownRightRetainedSupportedSeats S n =
      coarseTownRightPackingRemainder S n ∧
      Disjoint (coarseFullTownUncoveredSeats S n) (coarseTownRightRetainedSupportedSeats S n) :=
  coarseTown_retained_partition S n (coarseTownRightPackingRemainder_subset S n)
    (coarseFullTownUncoveredSeats_subset_rightRemainder S n)

theorem coarseTownRight_remainder_card_split (S : Finset ℕ) (n : ℕ) :
    (coarseTownRightPackingRemainder S n).card = (coarseFullTownUncoveredSeats S n).card +
      (coarseTownRightRetainedSupportedSeats S n).card :=
  coarseTown_card_retained_split S n (coarseTownRightPackingRemainder_subset S n)
    (coarseFullTownUncoveredSeats_subset_rightRemainder S n)

theorem coarseTownRight_active_card_partition {S : Finset ℕ} (hS : KnownPrimeScales S) (n : ℕ) :
    (coarseTownRightRepresentedPrimes S n).card + (coarseTownRightUnrepresentedActivePrimes S n).card =
      (coarseFullTownActivePrimes S n).card := by
  unfold coarseTownRightUnrepresentedActivePrimes
  have h := Finset.card_sdiff_add_card_eq_card (coarseTownRightRepresentedPrimes_subset_active hS n)
  omega

theorem coarseTownRight_represented_card_split (S : Finset ℕ) (n : ℕ) :
    (coarseTownRightRepresentedPrimes S n).card = (coarseTownRightRetainedSupportedSeats S n).card +
      coarseTownRightRetainedSupportExcess S n :=
  card_representedDirections _ _ (coarseTownRightPackingRemainder_family S n).2

theorem coarseTownRight_loss_decomposition {S : Finset ℕ} (hS : KnownPrimeScales S) (n : ℕ) :
    coarseTownRightSupportLoss S n = (coarseTownRightUnrepresentedActivePrimes S n).card +
      coarseTownRightRetainedSupportExcess S n :=
  coarseTown_retained_loss_decomposition hS n (coarseTownRightPackingRemainder_subset S n)
    (coarseFullTownUncoveredSeats_subset_rightRemainder S n) (coarseTownRightPackingRemainder_family S n).2
    (coarseTownRight_remainder_add_loss hS n)

theorem coarseTown_orientation_loss_identity {S : Finset ℕ} (hS : KnownPrimeScales S) (n : ℕ) :
    (coarseTownPackingRemainder S n).card + coarseTownSupportLoss S n =
      (coarseTownRightPackingRemainder S n).card + coarseTownRightSupportLoss S n :=
  (coarseTown_remainder_add_loss_eq_uncovered_add_active hS n).trans
    (coarseTownRight_remainder_add_loss hS n).symm

theorem coarseTown_orientation_overlap_identity {S : Finset ℕ} (hS : KnownPrimeScales S) (n : ℕ) :
    (coarseTownRightPackingRemainder S n).card + coarseTownDeletionOverlap S n =
      (coarseTownPackingRemainder S n).card + coarseTownRightDeletionOverlap S n := by
  have hl := coarseTown_remainder_conservation hS n
  have hr := coarseTownRight_remainder_conservation hS n
  omega

/-- Prefer the right orientation on ties; only two certified remainders are compared. -/
noncomputable def coarseTownBetterRemainder (S : Finset ℕ) (n : ℕ) : Finset ℕ :=
  if (coarseTownPackingRemainder S n).card ≤ (coarseTownRightPackingRemainder S n).card
  then coarseTownRightPackingRemainder S n else coarseTownPackingRemainder S n

noncomputable def coarseTownBetterLoss (S : Finset ℕ) (n : ℕ) :=
  min (coarseTownSupportLoss S n) (coarseTownRightSupportLoss S n)

theorem coarseTownBetterRemainder_subset (S : Finset ℕ) (n : ℕ) :
    coarseTownBetterRemainder S n ⊆ coarsePrimeWorldFullTown S n := by
  unfold coarseTownBetterRemainder
  split
  · exact coarseTownRightPackingRemainder_subset S n
  · exact coarseTownPackingRemainder_subset S n

theorem coarseTownBetterRemainder_family (S : Finset ℕ) (n : ℕ) :
    PairwiseOldSupportDisjointSquareSeatFamily n (coarseTownBetterRemainder S n) := by
  unfold coarseTownBetterRemainder
  split
  · exact coarseTownRightPackingRemainder_family S n
  · exact coarseTownPackingRemainder_family S n

theorem card_coarseTownBetterRemainder (S : Finset ℕ) (n : ℕ) :
    (coarseTownBetterRemainder S n).card =
      max (coarseTownPackingRemainder S n).card (coarseTownRightPackingRemainder S n).card := by
  unfold coarseTownBetterRemainder
  split_ifs with h
  · exact (max_eq_right h).symm
  · exact (max_eq_left (by omega)).symm

theorem coarseTownBetter_remainder_add_loss {S : Finset ℕ} (hS : KnownPrimeScales S) (n : ℕ) :
    (coarseTownBetterRemainder S n).card + coarseTownBetterLoss S n =
      (coarseFullTownUncoveredSeats S n).card + (coarseFullTownActivePrimes S n).card := by
  rw [card_coarseTownBetterRemainder]
  unfold coarseTownBetterLoss
  have hl := coarseTown_remainder_add_loss_eq_uncovered_add_active hS n
  have hr := coarseTownRight_remainder_add_loss hS n
  omega

theorem card_coarseTownBetterRemainder_le_outside_of_fullyCovered
    {S : Finset ℕ} (hS : KnownPrimeScales S) {n : ℕ} (hc : SquareOffsetsFullyCovered n) :
    (coarseTownBetterRemainder S n).card ≤ (coarseOutsidePrimes S n).card :=
  card_fullTown_pairwiseOldSupportDisjoint_le_outsidePrimes_of_fullyCovered hS
    (coarseTownBetterRemainder_subset S n) (coarseTownBetterRemainder_family S n) hc

theorem coarseTownBetter_deficit_iff_loss_frontier {S : Finset ℕ} (hS : KnownPrimeScales S) (n : ℕ) :
    (coarseOutsidePrimes S n).card < (coarseTownBetterRemainder S n).card ↔
      coarseTownBetterLoss S n +
        ((coarseOutsidePrimes S n).card - (coarseFullTownActivePrimes S n).card) <
          (coarseFullTownUncoveredSeats S n).card := by
  have h := coarseTownBetter_remainder_add_loss hS n
  have ha := card_coarseFullTownActivePrimes_le S n
  omega

theorem not_fullyCovered_of_coarseTownBetter_deficit {S : Finset ℕ} (hS : KnownPrimeScales S) {n : ℕ}
    (h : (coarseOutsidePrimes S n).card < (coarseTownBetterRemainder S n).card) :
    ¬ SquareOffsetsFullyCovered n :=
  not_fullyCovered_of_fullTown_survivor_capacity hS (coarseTownBetterRemainder_subset S n)
    (coarseTownBetterRemainder_family S n) h

theorem exists_prime_squareCell_of_coarseTownBetter_deficit {S : Finset ℕ}
    (hS : KnownPrimeScales S) {n : ℕ} (hn : 0 < n)
    (h : (coarseOutsidePrimes S n).card < (coarseTownBetterRemainder S n).card) :
    ∃ p, p.Prime ∧ SquareCell n p :=
  exists_prime_squareCell_of_not_fullyCovered hn (not_fullyCovered_of_coarseTownBetter_deficit hS h)

theorem coarseTownBetterLoss_eq_min (S : Finset ℕ) (n : ℕ) :
    coarseTownBetterLoss S n = min (coarseTownSupportLoss S n) (coarseTownRightSupportLoss S n) := rfl

theorem coarseTownRight_active_partition {S : Finset ℕ} (hS : KnownPrimeScales S) (n : ℕ) :
    coarseTownRightRepresentedPrimes S n ∪ coarseTownRightUnrepresentedActivePrimes S n =
      coarseFullTownActivePrimes S n :=
  Finset.union_sdiff_of_subset (coarseTownRightRepresentedPrimes_subset_active hS n)

theorem coarseTownRight_active_partition_disjoint (S : Finset ℕ) (n : ℕ) :
    Disjoint (coarseTownRightRepresentedPrimes S n) (coarseTownRightUnrepresentedActivePrimes S n) :=
  Finset.disjoint_sdiff

end DkMath.NumberTheory.Legendre
