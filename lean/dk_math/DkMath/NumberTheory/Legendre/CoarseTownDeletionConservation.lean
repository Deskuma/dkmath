/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.CoarseTownSurvivorCapacity

#print "file: DkMath.NumberTheory.Legendre.CoarseTownDeletionConservation"

/-! Exact actual-support and nonmaximum-witness ledgers for complete-period towns. -/

namespace DkMath.NumberTheory.Legendre

open DkMath.NumberTheory.Primitive DkMath.NumberTheory.StructuralArithmetic
open scoped BigOperators

noncomputable def coarseFullTownActivePrimes (S : Finset ℕ) (n : ℕ) : Finset ℕ := by
  classical
  exact (coarseOutsidePrimes S n).filter (fun q => (coarseFullTownPrimeFiber S n q).Nonempty)

@[simp] theorem mem_coarseFullTownActivePrimes {S : Finset ℕ} {n q : ℕ} :
    q ∈ coarseFullTownActivePrimes S n ↔
      q ∈ coarseOutsidePrimes S n ∧ (coarseFullTownPrimeFiber S n q).Nonempty := by
  classical
  exact Finset.mem_filter

theorem coarseFullTownActivePrimes_subset (S : Finset ℕ) (n : ℕ) :
    coarseFullTownActivePrimes S n ⊆ coarseOutsidePrimes S n := Finset.filter_subset _ _

theorem card_coarseFullTownActivePrimes_le (S : Finset ℕ) (n : ℕ) :
    (coarseFullTownActivePrimes S n).card ≤ (coarseOutsidePrimes S n).card :=
  Finset.card_le_card (coarseFullTownActivePrimes_subset S n)

noncomputable def coarseFullTownUncoveredSeats (S : Finset ℕ) (n : ℕ) : Finset ℕ := by
  classical
  exact (coarsePrimeWorldFullTown S n).filter (fun a => squareOffsetPrimeSupport n a = ∅)

@[simp] theorem mem_coarseFullTownUncoveredSeats {S : Finset ℕ} {n a : ℕ} :
    a ∈ coarseFullTownUncoveredSeats S n ↔
      a ∈ coarsePrimeWorldFullTown S n ∧ squareOffsetPrimeSupport n a = ∅ := by
  classical
  exact Finset.mem_filter

theorem coarseFullTownUncoveredSeats_eq_empty_of_fullyCovered (S : Finset ℕ) {n : ℕ}
    (hc : SquareOffsetsFullyCovered n) : coarseFullTownUncoveredSeats S n = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  have h := mem_coarseFullTownUncoveredSeats.mp ha
  have hp := squareOffsetCovered_iff_primeSupport_nonempty.mp
    (hc a (mem_squareOffsets.mp (coarseFullTown_subset_squareOffsets S n h.1)))
  rw [h.2] at hp
  exact Finset.not_nonempty_empty hp

noncomputable def coarseFullTownSupportExcess (S : Finset ℕ) (n : ℕ) : ℕ :=
  ∑ a ∈ coarsePrimeWorldFullTown S n, ((squareOffsetPrimeSupport n a).card - 1)

theorem coarseFullTownIncidence_add_uncovered_eq_card_add_excess
    {S : Finset ℕ} (hS : KnownPrimeScales S) (n : ℕ) :
    coarseFullTownIncidence S n + (coarseFullTownUncoveredSeats S n).card =
      (coarsePrimeWorldFullTown S n).card + coarseFullTownSupportExcess S n := by
  classical
  rw [coarseFullTownIncidence_eq_support_sum hS n]
  unfold coarseFullTownUncoveredSeats coarseFullTownSupportExcess
  rw [Finset.card_filter, ← Finset.sum_add_distrib]
  rw [show (coarsePrimeWorldFullTown S n).card =
    ∑ _a ∈ coarsePrimeWorldFullTown S n, (1 : ℕ) from by simp]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _ha
  by_cases he : squareOffsetPrimeSupport n a = ∅
  · simp [he]
  · have hp : 0 < (squareOffsetPrimeSupport n a).card :=
      Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr he)
    simp only [ite_eq_right he]
    omega

/-- Seats of the actual fiber with a strictly larger witness in that same fiber. -/
noncomputable def coarseTownNonmaximumFiberSeats (S : Finset ℕ) (n q : ℕ) : Finset ℕ := by
  classical
  let F := coarseFullTownPrimeFiber S n q
  exact F.filter (fun a => ∃ b ∈ F, a < b)

@[simp] theorem mem_coarseTownNonmaximumFiberSeats {S : Finset ℕ} {n q a : ℕ} :
    a ∈ coarseTownNonmaximumFiberSeats S n q ↔
      a ∈ coarseFullTownPrimeFiber S n q ∧ ∃ b ∈ coarseFullTownPrimeFiber S n q, a < b := by
  classical
  exact Finset.mem_filter

theorem card_coarseTownNonmaximumFiberSeats_add_indicator (S : Finset ℕ) (n q : ℕ) :
    (coarseTownNonmaximumFiberSeats S n q).card +
      (if (coarseFullTownPrimeFiber S n q).Nonempty then 1 else 0) =
        (coarseFullTownPrimeFiber S n q).card := by
  classical
  let F := coarseFullTownPrimeFiber S n q
  change (F.filter (fun a => ∃ b ∈ F, a < b)).card + (if F.Nonempty then 1 else 0) = F.card
  by_cases h : F.Nonempty
  · have he : F.filter (fun a => ∃ b ∈ F, a < b) = F.erase (F.max' h) := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨ha, b, hb, hab⟩
        have hm := Finset.le_max' F b hb
        exact ⟨by omega, ha⟩
      · rintro ⟨hne, ha⟩
        exact ⟨ha, F.max' h, Finset.max'_mem F h,
          lt_of_le_of_ne (Finset.le_max' F a ha) hne⟩
    rw [he, ite_eq_left h]
    exact Finset.card_erase_add_one (Finset.max'_mem F h)
  · have he := Finset.not_nonempty_iff_eq_empty.mp h
    simp [he]

noncomputable def coarseTownDeletionWitnessPrimes (S : Finset ℕ) (n a : ℕ) : Finset ℕ := by
  classical
  exact (coarseOutsidePrimes S n).filter (fun q => a ∈ coarseTownNonmaximumFiberSeats S n q)

noncomputable def coarseTownDeletionMultiplicity (S : Finset ℕ) (n a : ℕ) : ℕ :=
  (coarseTownDeletionWitnessPrimes S n a).card

theorem coarseTownDeletionWitnessPrimes_subset_support (S : Finset ℕ) (n a : ℕ) :
    coarseTownDeletionWitnessPrimes S n a ⊆ squareOffsetPrimeSupport n a := by
  intro q hq
  have h := Finset.mem_filter.mp hq
  exact (Finset.mem_filter.mp (mem_coarseTownNonmaximumFiberSeats.mp h.2).1).2

theorem mem_coarseTownDeletionVertices_iff_multiplicity_pos
    {S : Finset ℕ} (hS : KnownPrimeScales S) (n a : ℕ) :
    a ∈ coarseTownDeletionVertices S n ↔ 0 < coarseTownDeletionMultiplicity S n a := by
  classical
  rw [coarseTownDeletionMultiplicity, Finset.card_pos, Finset.nonempty_iff_ne_empty]
  constructor
  · intro ha
    obtain ⟨b, hab⟩ := mem_coarseTownDeletionVertices.mp ha
    obtain ⟨haV, hbV, hlt, hnd⟩ := mem_coarseTownSupportCollisionEdges.mp hab
    obtain ⟨q, hq⟩ := Finset.not_disjoint_iff_nonempty_inter.mp hnd
    have hqa := (Finset.mem_inter.mp hq).1
    have hqb := (Finset.mem_inter.mp hq).2
    apply Finset.nonempty_iff_ne_empty.mp
    refine ⟨q, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
    · exact coarse_survivor_support_outside (coarseFullTown_survivor hS haV) hqa
    · exact mem_coarseTownNonmaximumFiberSeats.mpr ⟨Finset.mem_filter.mpr ⟨haV,hqa⟩,
        b, Finset.mem_filter.mpr ⟨hbV,hqb⟩,hlt⟩
  · intro ha
    obtain ⟨q,hq⟩ := Finset.nonempty_iff_ne_empty.mpr ha
    have h := mem_coarseTownNonmaximumFiberSeats.mp (Finset.mem_filter.mp hq).2
    obtain ⟨b,hb,hlt⟩ := h.2
    have haF := Finset.mem_filter.mp h.1
    have hbF := Finset.mem_filter.mp hb
    refine mem_coarseTownDeletionVertices.mpr ⟨b,
      mem_coarseTownSupportCollisionEdges.mpr ⟨haF.1,hbF.1,hlt,?_⟩⟩
    intro hd
    exact Finset.disjoint_left.mp hd haF.2 hbF.2

theorem mem_coarseTownDeletionByFibers_iff_multiplicity_pos
    {S : Finset ℕ} (hS : KnownPrimeScales S) (n a : ℕ) :
    a ∈ coarseTownDeletionByFibers S n ↔ 0 < coarseTownDeletionMultiplicity S n a := by
  rw [← coarseTownDeletionVertices_eq_fibers]
  exact mem_coarseTownDeletionVertices_iff_multiplicity_pos hS n a

noncomputable def coarseTownDeletionMass (S : Finset ℕ) (n : ℕ) : ℕ :=
  ∑ a ∈ coarsePrimeWorldFullTown S n, coarseTownDeletionMultiplicity S n a

theorem coarseTownDeletionMass_eq_nonmaximum_sum (S : Finset ℕ) (n : ℕ) :
    coarseTownDeletionMass S n =
      ∑ q ∈ coarseOutsidePrimes S n, (coarseTownNonmaximumFiberSeats S n q).card := by
  classical
  unfold coarseTownDeletionMass coarseTownDeletionMultiplicity coarseTownDeletionWitnessPrimes
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _hq
  rw [Finset.sum_boole]
  have he : (coarsePrimeWorldFullTown S n).filter
      (fun a => a ∈ coarseTownNonmaximumFiberSeats S n q) =
        coarseTownNonmaximumFiberSeats S n q := by
    ext a
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨(Finset.mem_filter.mp
      (mem_coarseTownNonmaximumFiberSeats.mp h).1).1,h⟩⟩
  rw [he]
  simp only [Nat.cast_id]

theorem coarseTownDeletionMass_add_active_eq_incidence (S : Finset ℕ) (n : ℕ) :
    coarseTownDeletionMass S n + (coarseFullTownActivePrimes S n).card =
      coarseFullTownIncidence S n := by
  classical
  rw [coarseTownDeletionMass_eq_nonmaximum_sum]
  unfold coarseFullTownActivePrimes coarseFullTownIncidence
  rw [Finset.card_filter, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun q _hq => card_coarseTownNonmaximumFiberSeats_add_indicator S n q)

noncomputable def coarseTownDeletionOverlap (S : Finset ℕ) (n : ℕ) : ℕ :=
  ∑ a ∈ coarseTownDeletionVertices S n, (coarseTownDeletionMultiplicity S n a - 1)

theorem card_deletion_add_overlap_eq_mass {S : Finset ℕ} (hS : KnownPrimeScales S) (n : ℕ) :
    (coarseTownDeletionVertices S n).card + coarseTownDeletionOverlap S n =
      coarseTownDeletionMass S n := by
  classical
  have he : coarseTownDeletionVertices S n =
      (coarsePrimeWorldFullTown S n).filter (fun a => 0 < coarseTownDeletionMultiplicity S n a) := by
    ext a
    rw [Finset.mem_filter, ← mem_coarseTownDeletionVertices_iff_multiplicity_pos hS]
    exact ⟨fun h => ⟨coarseTownDeletionVertices_subset S n h,h⟩, fun h => h.2⟩
  unfold coarseTownDeletionOverlap coarseTownDeletionMass
  rw [show (coarseTownDeletionVertices S n).card =
    ∑ _a ∈ coarseTownDeletionVertices S n, (1 : ℕ) from by simp]
  rw [← Finset.sum_add_distrib, he, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _ha
  by_cases h : 0 < coarseTownDeletionMultiplicity S n a
  · simp only [ite_eq_left h]
    omega
  · simp only [ite_eq_right h]
    omega

theorem coarseTownDeletion_primeFiber_conservation {S : Finset ℕ} (hS : KnownPrimeScales S) (n : ℕ) :
    (coarseTownDeletionVertices S n).card + coarseTownDeletionOverlap S n +
      (coarseFullTownActivePrimes S n).card = coarseFullTownIncidence S n := by
  rw [card_deletion_add_overlap_eq_mass hS n, coarseTownDeletionMass_add_active_eq_incidence]

/-- Unconditional in full-cover status; S is certified so all actual support lies outside S. -/
theorem coarseTown_remainder_conservation {S : Finset ℕ} (hS : KnownPrimeScales S) (n : ℕ) :
    (coarseTownPackingRemainder S n).card + coarseFullTownSupportExcess S n =
      (coarseFullTownUncoveredSeats S n).card + (coarseFullTownActivePrimes S n).card +
        coarseTownDeletionOverlap S n := by
  have hp := card_coarseTownDeletion_partition S n
  have hs := coarseFullTownIncidence_add_uncovered_eq_card_add_excess hS n
  have hf := coarseTownDeletion_primeFiber_conservation hS n
  omega

theorem coarseTown_remainder_conservation_of_fullyCovered {S : Finset ℕ}
    (hS : KnownPrimeScales S) {n : ℕ} (hc : SquareOffsetsFullyCovered n) :
    (coarseTownPackingRemainder S n).card + coarseFullTownSupportExcess S n =
      (coarseFullTownActivePrimes S n).card + coarseTownDeletionOverlap S n := by
  have h := coarseTown_remainder_conservation hS n
  rw [coarseFullTownUncoveredSeats_eq_empty_of_fullyCovered S hc, Finset.card_empty] at h
  simpa using h

theorem coarseTown_fullCover_conservation_frontier {S : Finset ℕ}
    (hS : KnownPrimeScales S) {n : ℕ} (hc : SquareOffsetsFullyCovered n) :
    (coarseFullTownActivePrimes S n).card + coarseTownDeletionOverlap S n ≤
      (coarseOutsidePrimes S n).card + coarseFullTownSupportExcess S n := by
  have hm := coarseTown_remainder_conservation_of_fullyCovered hS hc
  have hcapa := card_fullTown_pairwiseOldSupportDisjoint_le_outsidePrimes_of_fullyCovered hS
    (coarseTownPackingRemainder_subset S n) (coarseTownPackingRemainder_family S n) hc
  omega

theorem not_fullyCovered_of_coarseTown_conservation_deficit {S : Finset ℕ}
    (hS : KnownPrimeScales S) {n : ℕ}
    (h : (coarseOutsidePrimes S n).card + coarseFullTownSupportExcess S n <
      (coarseFullTownActivePrimes S n).card + coarseTownDeletionOverlap S n) :
    ¬ SquareOffsetsFullyCovered n := by
  intro hc
  exact (not_le_of_gt h) (coarseTown_fullCover_conservation_frontier hS hc)

theorem exists_prime_squareCell_of_coarseTown_conservation_deficit {S : Finset ℕ}
    (hS : KnownPrimeScales S) {n : ℕ} (hn : 0 < n)
    (h : (coarseOutsidePrimes S n).card + coarseFullTownSupportExcess S n <
      (coarseFullTownActivePrimes S n).card + coarseTownDeletionOverlap S n) :
    ∃ p, p.Prime ∧ SquareCell n p :=
  exists_prime_squareCell_of_not_fullyCovered hn
    (not_fullyCovered_of_coarseTown_conservation_deficit hS h)

/-- The exact reparameterization retains the uncovered-seat term. -/
theorem coarseTown_outside_deficit_iff_conservation_with_uncovered
    {S : Finset ℕ} (hS : KnownPrimeScales S) (n : ℕ) :
    (coarseOutsidePrimes S n).card + (coarseTownDeletionVertices S n).card <
        (coarsePrimeWorldFullTown S n).card ↔
      (coarseOutsidePrimes S n).card + coarseFullTownSupportExcess S n <
        (coarseFullTownUncoveredSeats S n).card + (coarseFullTownActivePrimes S n).card +
          coarseTownDeletionOverlap S n := by
  have hp := card_coarseTownDeletion_partition S n
  have hm := coarseTown_remainder_conservation hS n
  omega

theorem coarseTown_outside_deficit_iff_conservation_of_uncovered_empty
    {S : Finset ℕ} (hS : KnownPrimeScales S) {n : ℕ}
    (hu : coarseFullTownUncoveredSeats S n = ∅) :
    (coarseOutsidePrimes S n).card + (coarseTownDeletionVertices S n).card <
        (coarsePrimeWorldFullTown S n).card ↔
      (coarseOutsidePrimes S n).card + coarseFullTownSupportExcess S n <
        (coarseFullTownActivePrimes S n).card + coarseTownDeletionOverlap S n := by
  rw [coarseTown_outside_deficit_iff_conservation_with_uncovered hS, hu, Finset.card_empty,
    zero_add]

/-- Repeated deletion charges are already part of support excess, even without full cover. -/
theorem coarseTownDeletionOverlap_le_supportExcess (S : Finset ℕ) (n : ℕ) :
    coarseTownDeletionOverlap S n ≤ coarseFullTownSupportExcess S n := by
  classical
  unfold coarseTownDeletionOverlap coarseFullTownSupportExcess
  calc
    _ ≤ ∑ a ∈ coarseTownDeletionVertices S n, ((squareOffsetPrimeSupport n a).card - 1) := by
      apply Finset.sum_le_sum
      intro a _ha
      exact Nat.sub_le_sub_right (Finset.card_le_card
        (coarseTownDeletionWitnessPrimes_subset_support S n a)) 1
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (coarseTownDeletionVertices_subset S n)
      (fun _ _ _ => Nat.zero_le _)

/-- Consequently the uncovered-free strict frontier is never satisfied by actual support. -/
theorem coarseTown_conservation_frontier_unconditional (S : Finset ℕ) (n : ℕ) :
    (coarseFullTownActivePrimes S n).card + coarseTownDeletionOverlap S n ≤
      (coarseOutsidePrimes S n).card + coarseFullTownSupportExcess S n :=
  Nat.add_le_add (card_coarseFullTownActivePrimes_le S n)
    (coarseTownDeletionOverlap_le_supportExcess S n)

/-- Exact arithmetic normal form for bounded computation, with no support labels. -/
theorem coarseFullTownPrimeFiber_eq_divisibility_of_mem {S : Finset ℕ} {n q : ℕ}
    (hq : q ∈ coarseOutsidePrimes S n) :
    coarseFullTownPrimeFiber S n q = coarseTownDivisibilityFiber S n q := by
  have hp := mem_primeScalesUpTo.mp (Finset.mem_sdiff.mp hq).1
  ext a
  simp only [coarseFullTownPrimeFiber, coarseTownDivisibilityFiber, oldSupportSeatFiber,
    Finset.mem_filter, mem_squareOffsetPrimeSupport]
  exact ⟨fun h => ⟨h.1,h.2.2.2⟩, fun h => ⟨h.1,hp.1,hp.2,h.2⟩⟩

theorem coarseFullTownIncidence_eq_divisibility_sum (S : Finset ℕ) (n : ℕ) :
    coarseFullTownIncidence S n =
      ∑ q ∈ coarseOutsidePrimes S n, (coarseTownDivisibilityFiber S n q).card := by
  unfold coarseFullTownIncidence
  exact Finset.sum_congr rfl (fun _ hq => congrArg Finset.card
    (coarseFullTownPrimeFiber_eq_divisibility_of_mem hq))

theorem coarseFullTownActivePrimes_eq_divisibility_filter (S : Finset ℕ) (n : ℕ) :
    coarseFullTownActivePrimes S n = (coarseOutsidePrimes S n).filter
      (fun q => (coarseTownDivisibilityFiber S n q).Nonempty) := by
  classical
  apply Finset.filter_congr
  intro q hq
  rw [coarseFullTownPrimeFiber_eq_divisibility_of_mem hq]

theorem card_coarseTownNonmaximumFiberSeats_of_nonempty {S : Finset ℕ} {n q : ℕ}
    (h : (coarseFullTownPrimeFiber S n q).Nonempty) :
    (coarseTownNonmaximumFiberSeats S n q).card + 1 = (coarseFullTownPrimeFiber S n q).card := by
  simpa only [ite_eq_left h] using card_coarseTownNonmaximumFiberSeats_add_indicator S n q

theorem coarseTownNonmaximumFiberSeats_eq_empty_of_empty {S : Finset ℕ} {n q : ℕ}
    (h : coarseFullTownPrimeFiber S n q = ∅) : coarseTownNonmaximumFiberSeats S n q = ∅ := by
  classical
  simp only [coarseTownNonmaximumFiberSeats, h, Finset.filter_empty]

@[simp] theorem mem_coarseTownDeletionWitnessPrimes {S : Finset ℕ} {n a q : ℕ} :
    q ∈ coarseTownDeletionWitnessPrimes S n a ↔
      q ∈ coarseOutsidePrimes S n ∧ a ∈ coarseTownNonmaximumFiberSeats S n q := by
  classical
  exact Finset.mem_filter

/-- Supported seats lost by the maximum-fiber selector; overlap is already bounded by excess. -/
noncomputable def coarseTownSupportLoss (S : Finset ℕ) (n : ℕ) : ℕ :=
  coarseFullTownSupportExcess S n - coarseTownDeletionOverlap S n

theorem coarseTown_overlap_add_loss_eq_excess (S : Finset ℕ) (n : ℕ) :
    coarseTownDeletionOverlap S n + coarseTownSupportLoss S n = coarseFullTownSupportExcess S n :=
  Nat.add_sub_of_le (coarseTownDeletionOverlap_le_supportExcess S n)

/-- A Nat-safe cancellation exposing the selector's exact loss coordinate. -/
theorem coarseTown_remainder_add_loss_eq_uncovered_add_active
    {S : Finset ℕ} (hS : KnownPrimeScales S) (n : ℕ) :
    (coarseTownPackingRemainder S n).card + coarseTownSupportLoss S n =
      (coarseFullTownUncoveredSeats S n).card + (coarseFullTownActivePrimes S n).card := by
  have hm := coarseTown_remainder_conservation hS n
  have hl := coarseTown_overlap_add_loss_eq_excess S n
  omega

/-- Correct nonvacuous frontier: uncovered seats exceed selector loss plus inactive directions. -/
theorem coarseTown_outside_deficit_iff_loss_add_inactive_lt_uncovered
    {S : Finset ℕ} (hS : KnownPrimeScales S) (n : ℕ) :
    (coarseOutsidePrimes S n).card + (coarseTownDeletionVertices S n).card <
        (coarsePrimeWorldFullTown S n).card ↔
      coarseTownSupportLoss S n +
        ((coarseOutsidePrimes S n).card - (coarseFullTownActivePrimes S n).card) <
          (coarseFullTownUncoveredSeats S n).card := by
  have hp := card_coarseTownDeletion_partition S n
  have hl := coarseTown_remainder_add_loss_eq_uncovered_add_active hS n
  have ha := card_coarseFullTownActivePrimes_le S n
  omega

theorem exists_prime_squareCell_of_coarseTown_loss_frontier
    {S : Finset ℕ} (hS : KnownPrimeScales S) {n : ℕ} (hn : 0 < n)
    (h : coarseTownSupportLoss S n +
      ((coarseOutsidePrimes S n).card - (coarseFullTownActivePrimes S n).card) <
        (coarseFullTownUncoveredSeats S n).card) : ∃ p, p.Prime ∧ SquareCell n p :=
  exists_prime_squareCell_of_coarseTown_outside_deletion_deficit hS hn
    ((coarseTown_outside_deficit_iff_loss_add_inactive_lt_uncovered hS n).mpr h)

end DkMath.NumberTheory.Legendre
