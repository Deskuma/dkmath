/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.CoarseTownTerminalProduct

#print "file: DkMath.NumberTheory.Legendre.CoarseTownSourceMultiplicity"

/-! Exact missing-direction endpoint sums and comparison of product capacities. -/
namespace DkMath.NumberTheory.Legendre

open DkMath.Combinatorics DkMath.NumberTheory.Primitive DkMath.NumberTheory.StructuralArithmetic
open scoped BigOperators

theorem coarseTown_deleted_terminal_subset_missing {S : Finset ℕ} (hS : KnownPrimeScales S)
    {n a : ℕ} (ha : a ∈ coarseTownDeletionVertices S n) :
    coarseTownTerminalPrimesAt S n a ⊆ coarseTownUnrepresentedActivePrimes S n := by
  intro q hq
  have h := mem_coarseTownTerminalPrimesAt.mp hq
  exact (coarseTownMax_unrepresented_iff_deleted
    (coarseTownTerminalPrimesAt_subset_active hS (coarseTownDeletionVertices_subset _ _ ha) hq) h.2).mpr ha

theorem coarseTown_rightDeleted_terminal_subset_missing {S : Finset ℕ} (hS : KnownPrimeScales S)
    {n a : ℕ} (ha : a ∈ coarseTownRightDeletionVertices S n) :
    coarseTownMinimumTerminalPrimesAt S n a ⊆ coarseTownRightUnrepresentedActivePrimes S n := by
  intro q hq
  have h := mem_coarseTownMinimumTerminalPrimesAt.mp hq
  exact (coarseTownMin_unrepresented_iff_deleted
    (coarseTownMinimumTerminalPrimesAt_subset_active hS (coarseTownRightDeletionVertices_subset _ _ ha) hq) h.2).mpr ha

theorem coarseTown_missing_unique_terminal {S : Finset ℕ} {n q : ℕ}
    (hq : q ∈ coarseTownUnrepresentedActivePrimes S n) :
    ∃! a, a ∈ coarseTownDeletionVertices S n ∧ q ∈ coarseTownTerminalPrimesAt S n a := by
  have hqa := (Finset.mem_sdiff.mp hq).1
  obtain ⟨a,ha,hu⟩ := existsUnique_coarseTownFiberMaximumAt hqa
  refine ⟨a,⟨(coarseTownMax_unrepresented_iff_deleted hqa ha).mp hq,
    mem_coarseTownTerminalPrimesAt.mpr ⟨(Finset.mem_filter.mp ha.1).2,ha⟩⟩,?_⟩
  intro b hb
  exact hu b (mem_coarseTownTerminalPrimesAt.mp hb.2).2

theorem coarseTown_rightMissing_unique_terminal {S : Finset ℕ} {n q : ℕ}
    (hq : q ∈ coarseTownRightUnrepresentedActivePrimes S n) :
    ∃! a, a ∈ coarseTownRightDeletionVertices S n ∧ q ∈ coarseTownMinimumTerminalPrimesAt S n a := by
  have hqa := (Finset.mem_sdiff.mp hq).1
  obtain ⟨a,ha,hu⟩ := existsUnique_coarseTownFiberMinimumAt hqa
  refine ⟨a,⟨(coarseTownMin_unrepresented_iff_deleted hqa ha).mp hq,
    mem_coarseTownMinimumTerminalPrimesAt.mpr ⟨(Finset.mem_filter.mp ha.1).2,ha⟩⟩,?_⟩
  intro b hb
  exact hu b (mem_coarseTownMinimumTerminalPrimesAt.mp hb.2).2

theorem coarseTown_terminal_fibers_pairwiseDisjoint (S : Finset ℕ) (n : ℕ) :
    (coarseTownDeletionVertices S n : Set ℕ).PairwiseDisjoint (coarseTownTerminalPrimesAt S n) := by
  intro a _ha b _hb hab
  change Disjoint (coarseTownTerminalPrimesAt S n a) (coarseTownTerminalPrimesAt S n b)
  rw [Finset.disjoint_left]
  intro q hqa hqb
  have ha := (mem_coarseTownTerminalPrimesAt.mp hqa).2
  have hb := (mem_coarseTownTerminalPrimesAt.mp hqb).2
  have hba := ha.2 b hb.1
  have hab' := hb.2 a ha.1
  exact hab (by omega)

theorem coarseTown_minimum_terminal_fibers_pairwiseDisjoint (S : Finset ℕ) (n : ℕ) :
    (coarseTownRightDeletionVertices S n : Set ℕ).PairwiseDisjoint (coarseTownMinimumTerminalPrimesAt S n) := by
  intro a _ha b _hb hab
  change Disjoint (coarseTownMinimumTerminalPrimesAt S n a) (coarseTownMinimumTerminalPrimesAt S n b)
  rw [Finset.disjoint_left]
  intro q hqa hqb
  have ha := (mem_coarseTownMinimumTerminalPrimesAt.mp hqa).2
  have hb := (mem_coarseTownMinimumTerminalPrimesAt.mp hqb).2
  have hab' := ha.2 b hb.1
  have hba := hb.2 a ha.1
  exact hab (by omega)

theorem coarseTown_terminal_biUnion_eq_missing {S : Finset ℕ} (hS : KnownPrimeScales S) (n : ℕ) :
    (coarseTownDeletionVertices S n).biUnion (coarseTownTerminalPrimesAt S n) =
      coarseTownUnrepresentedActivePrimes S n := by
  ext q
  constructor
  · intro hq
    obtain ⟨a,ha,hqa⟩ := Finset.mem_biUnion.mp hq
    exact coarseTown_deleted_terminal_subset_missing hS ha hqa
  · intro hq
    obtain ⟨a,ha,_hu⟩ := coarseTown_missing_unique_terminal hq
    exact Finset.mem_biUnion.mpr ⟨a,ha⟩

theorem coarseTown_minimum_terminal_biUnion_eq_missing {S : Finset ℕ} (hS : KnownPrimeScales S) (n : ℕ) :
    (coarseTownRightDeletionVertices S n).biUnion (coarseTownMinimumTerminalPrimesAt S n) =
      coarseTownRightUnrepresentedActivePrimes S n := by
  ext q
  constructor
  · intro hq
    obtain ⟨a,ha,hqa⟩ := Finset.mem_biUnion.mp hq
    exact coarseTown_rightDeleted_terminal_subset_missing hS ha hqa
  · intro hq
    obtain ⟨a,ha,_hu⟩ := coarseTown_rightMissing_unique_terminal hq
    exact Finset.mem_biUnion.mpr ⟨a,ha⟩

theorem coarseTown_missing_card_eq_terminal_sum {S : Finset ℕ} (hS : KnownPrimeScales S) (n : ℕ) :
    (coarseTownUnrepresentedActivePrimes S n).card =
      ∑ a ∈ coarseTownDeletionVertices S n, (coarseTownTerminalPrimesAt S n a).card := by
  rw [← coarseTown_terminal_biUnion_eq_missing hS n,
    Finset.card_biUnion (coarseTown_terminal_fibers_pairwiseDisjoint S n)]

theorem coarseTown_rightMissing_card_eq_terminal_sum {S : Finset ℕ} (hS : KnownPrimeScales S) (n : ℕ) :
    (coarseTownRightUnrepresentedActivePrimes S n).card =
      ∑ a ∈ coarseTownRightDeletionVertices S n, (coarseTownMinimumTerminalPrimesAt S n a).card := by
  rw [← coarseTown_minimum_terminal_biUnion_eq_missing hS n,
    Finset.card_biUnion (coarseTown_minimum_terminal_fibers_pairwiseDisjoint S n)]

theorem coarseTown_missing_le_capacity_sum {S : Finset ℕ} (hS : KnownPrimeScales S)
    (n : ℕ) (capacity : ℕ → ℕ)
    (hcap : ∀ a ∈ coarseTownDeletionVertices S n, (coarseTownTerminalPrimesAt S n a).card ≤ capacity a) :
    (coarseTownUnrepresentedActivePrimes S n).card ≤ ∑ a ∈ coarseTownDeletionVertices S n, capacity a := by
  rw [coarseTown_missing_card_eq_terminal_sum hS n]
  exact Finset.sum_le_sum hcap

theorem coarseTown_rightMissing_le_capacity_sum {S : Finset ℕ} (hS : KnownPrimeScales S)
    (n : ℕ) (capacity : ℕ → ℕ)
    (hcap : ∀ a ∈ coarseTownRightDeletionVertices S n, (coarseTownMinimumTerminalPrimesAt S n a).card ≤ capacity a) :
    (coarseTownRightUnrepresentedActivePrimes S n).card ≤ ∑ a ∈ coarseTownRightDeletionVertices S n, capacity a := by
  rw [coarseTown_rightMissing_card_eq_terminal_sum hS n]
  exact Finset.sum_le_sum hcap

theorem coarseTown_missing_le_uniform_capacity {S : Finset ℕ} (hS : KnownPrimeScales S)
    (n k : ℕ) (hcap : ∀ a ∈ coarseTownDeletionVertices S n, (coarseTownTerminalPrimesAt S n a).card ≤ k) :
    (coarseTownUnrepresentedActivePrimes S n).card ≤ (coarseTownDeletionVertices S n).card * k := by
  simpa [Nat.mul_comm] using coarseTown_missing_le_capacity_sum hS n (fun _ => k) hcap

theorem coarseTown_rightMissing_le_uniform_capacity {S : Finset ℕ} (hS : KnownPrimeScales S)
    (n k : ℕ) (hcap : ∀ a ∈ coarseTownRightDeletionVertices S n, (coarseTownMinimumTerminalPrimesAt S n a).card ≤ k) :
    (coarseTownRightUnrepresentedActivePrimes S n).card ≤ (coarseTownRightDeletionVertices S n).card * k := by
  simpa [Nat.mul_comm] using coarseTown_rightMissing_le_capacity_sum hS n (fun _ => k) hcap

theorem coarseTown_loss_le_capacity_sum {S : Finset ℕ} (hS : KnownPrimeScales S)
    (n : ℕ) (capacity : ℕ → ℕ)
    (hcap : ∀ a ∈ coarseTownDeletionVertices S n, (coarseTownTerminalPrimesAt S n a).card ≤ capacity a) :
    coarseTownSupportLoss S n ≤ (∑ a ∈ coarseTownDeletionVertices S n, capacity a) +
      coarseTownRetainedSupportExcess S n := by
  rw [coarseTown_loss_decomposition hS n]
  exact Nat.add_le_add_right (coarseTown_missing_le_capacity_sum hS n capacity hcap) _

theorem coarseTown_rightLoss_le_capacity_sum {S : Finset ℕ} (hS : KnownPrimeScales S)
    (n : ℕ) (capacity : ℕ → ℕ)
    (hcap : ∀ a ∈ coarseTownRightDeletionVertices S n, (coarseTownMinimumTerminalPrimesAt S n a).card ≤ capacity a) :
    coarseTownRightSupportLoss S n ≤ (∑ a ∈ coarseTownRightDeletionVertices S n, capacity a) +
      coarseTownRightRetainedSupportExcess S n := by
  rw [coarseTownRight_loss_decomposition hS n]
  exact Nat.add_le_add_right (coarseTown_rightMissing_le_capacity_sum hS n capacity hcap) _

theorem coarseTown_betterLoss_le_capacity_sums {S : Finset ℕ} (hS : KnownPrimeScales S)
    (n : ℕ) (left right : ℕ → ℕ)
    (hl : ∀ a ∈ coarseTownDeletionVertices S n, (coarseTownTerminalPrimesAt S n a).card ≤ left a)
    (hr : ∀ a ∈ coarseTownRightDeletionVertices S n, (coarseTownMinimumTerminalPrimesAt S n a).card ≤ right a) :
    coarseTownBetterLoss S n ≤ min
      ((∑ a ∈ coarseTownDeletionVertices S n, left a) + coarseTownRetainedSupportExcess S n)
      ((∑ a ∈ coarseTownRightDeletionVertices S n, right a) + coarseTownRightRetainedSupportExcess S n) :=
  min_le_min (coarseTown_loss_le_capacity_sum hS n left hl) (coarseTown_rightLoss_le_capacity_sum hS n right hr)

theorem coarseTown_missing_le_deleted_excess {S : Finset ℕ} (hS : KnownPrimeScales S) (n : ℕ) :
    (coarseTownUnrepresentedActivePrimes S n).card ≤
      ∑ a ∈ coarseTownDeletionVertices S n, ((squareOffsetPrimeSupport n a).card - 1) :=
  coarseTown_missing_le_capacity_sum hS n _ (fun _a ha => coarseTown_deleted_terminal_le_support_excess hS ha)

theorem coarseTown_support_excess_partition (S : Finset ℕ) (n : ℕ) :
    coarseFullTownSupportExcess S n =
      (∑ a ∈ coarseTownDeletionVertices S n, ((squareOffsetPrimeSupport n a).card - 1)) +
        coarseTownRetainedSupportExcess S n := by
  unfold coarseFullTownSupportExcess coarseTownRetainedSupportExcess retainedExcess
  rw [← coarseTownRemainder_union_deletion S n,
    Finset.sum_union (disjoint_coarseTownRemainder_deletion S n)]
  omega

/-- Any capacity dominating actual support-minus-one is already at least full excess. -/
theorem coarseTown_capacity_loss_upper_ge_excess (S : Finset ℕ) (n : ℕ) (capacity : ℕ → ℕ)
    (hcap : ∀ a ∈ coarseTownDeletionVertices S n, (squareOffsetPrimeSupport n a).card - 1 ≤ capacity a) :
    coarseFullTownSupportExcess S n ≤ (∑ a ∈ coarseTownDeletionVertices S n, capacity a) +
      coarseTownRetainedSupportExcess S n := by
  rw [coarseTown_support_excess_partition]
  exact Nat.add_le_add_right (Finset.sum_le_sum hcap) _

theorem coarseTown_right_support_excess_partition (S : Finset ℕ) (n : ℕ) :
    coarseFullTownSupportExcess S n =
      (∑ a ∈ coarseTownRightDeletionVertices S n, ((squareOffsetPrimeSupport n a).card - 1)) +
        coarseTownRightRetainedSupportExcess S n := by
  classical
  have hu : coarseTownRightPackingRemainder S n ∪ coarseTownRightDeletionVertices S n =
      coarsePrimeWorldFullTown S n := Finset.sdiff_union_of_subset (coarseTownRightDeletionVertices_subset S n)
  have hd : Disjoint (coarseTownRightPackingRemainder S n) (coarseTownRightDeletionVertices S n) :=
    Finset.sdiff_disjoint
  unfold coarseFullTownSupportExcess coarseTownRightRetainedSupportExcess retainedExcess
  rw [← hu,Finset.sum_union hd]
  omega

theorem coarseTown_right_capacity_loss_upper_ge_excess (S : Finset ℕ) (n : ℕ) (capacity : ℕ → ℕ)
    (hcap : ∀ a ∈ coarseTownRightDeletionVertices S n, (squareOffsetPrimeSupport n a).card - 1 ≤ capacity a) :
    coarseFullTownSupportExcess S n ≤ (∑ a ∈ coarseTownRightDeletionVertices S n, capacity a) +
      coarseTownRightRetainedSupportExcess S n := by
  rw [coarseTown_right_support_excess_partition]
  exact Nat.add_le_add_right (Finset.sum_le_sum hcap) _

/-- A size threshold already bounds actual support; its source allowance cannot beat it. -/
theorem coarseTown_product_threshold_capacity_ge_excess {S : Finset ℕ} {n a B k : ℕ}
    (ha : a ∈ coarsePrimeWorldFullTown S n) (hB : 1 < B)
    (hbase : ∀ q ∈ squareOffsetPrimeSupport n a, B ≤ q)
    (hthreshold : (n + 1) ^ 2 ≤ B ^ (k + 1)) :
    (squareOffsetPrimeSupport n a).card - 1 ≤ k - 1 := by
  have hp := squareOffsetPrimeSupport_power_bounds
    (mem_squareOffsets.mp (coarseFullTown_subset_squareOffsets S n ha)) hbase
  have hc := support_card_le_of_power_threshold hB (hp.1.trans hp.2.1) hp.2.2 hthreshold
  omega

theorem coarseTown_missing_le_product_threshold {S : Finset ℕ} (hS : KnownPrimeScales S)
    {n B k : ℕ} (hB : 1 < B)
    (hbase : ∀ a ∈ coarsePrimeWorldFullTown S n, ∀ q ∈ squareOffsetPrimeSupport n a, B ≤ q)
    (hthreshold : (n + 1) ^ 2 ≤ B ^ (k + 1)) :
    (coarseTownUnrepresentedActivePrimes S n).card ≤ (coarseTownDeletionVertices S n).card * (k - 1) := by
  apply coarseTown_missing_le_uniform_capacity hS n (k - 1)
  intro a ha
  have ht := coarseTown_deleted_terminal_threshold hS ha hB
    (hbase a (coarseTownDeletionVertices_subset _ _ ha)) hthreshold
  omega

theorem coarseTown_rightMissing_le_product_threshold {S : Finset ℕ} (hS : KnownPrimeScales S)
    {n B k : ℕ} (hB : 1 < B)
    (hbase : ∀ a ∈ coarsePrimeWorldFullTown S n, ∀ q ∈ squareOffsetPrimeSupport n a, B ≤ q)
    (hthreshold : (n + 1) ^ 2 ≤ B ^ (k + 1)) :
    (coarseTownRightUnrepresentedActivePrimes S n).card ≤ (coarseTownRightDeletionVertices S n).card * (k - 1) := by
  apply coarseTown_rightMissing_le_uniform_capacity hS n (k - 1)
  intro a ha
  have ht := coarseTown_rightDeleted_terminal_threshold hS ha hB
    (hbase a (coarseTownRightDeletionVertices_subset _ _ ha)) hthreshold
  omega

theorem coarseTown_product_threshold_loss_upper_ge_excess {S : Finset ℕ} {n B k : ℕ}
    (hB : 1 < B)
    (hbase : ∀ a ∈ coarsePrimeWorldFullTown S n, ∀ q ∈ squareOffsetPrimeSupport n a, B ≤ q)
    (hthreshold : (n + 1) ^ 2 ≤ B ^ (k + 1)) :
    coarseFullTownSupportExcess S n ≤ (coarseTownDeletionVertices S n).card * (k - 1) +
      coarseTownRetainedSupportExcess S n := by
  simpa [Nat.mul_comm] using coarseTown_capacity_loss_upper_ge_excess S n (fun _ => k - 1)
    (fun _a ha => coarseTown_product_threshold_capacity_ge_excess
      (coarseTownDeletionVertices_subset _ _ ha) hB (hbase _ (coarseTownDeletionVertices_subset _ _ ha)) hthreshold)

theorem coarseTown_right_product_threshold_loss_upper_ge_excess {S : Finset ℕ} {n B k : ℕ}
    (hB : 1 < B)
    (hbase : ∀ a ∈ coarsePrimeWorldFullTown S n, ∀ q ∈ squareOffsetPrimeSupport n a, B ≤ q)
    (hthreshold : (n + 1) ^ 2 ≤ B ^ (k + 1)) :
    coarseFullTownSupportExcess S n ≤ (coarseTownRightDeletionVertices S n).card * (k - 1) +
      coarseTownRightRetainedSupportExcess S n := by
  simpa [Nat.mul_comm] using coarseTown_right_capacity_loss_upper_ge_excess S n (fun _ => k - 1)
    (fun _a ha => coarseTown_product_threshold_capacity_ge_excess
      (coarseTownRightDeletionVertices_subset _ _ ha) hB (hbase _ (coarseTownRightDeletionVertices_subset _ _ ha)) hthreshold)

/-- The mirrored product allowance cannot improve even the previous full-excess budget. -/
theorem coarseTown_better_product_threshold_upper_ge_excess {S : Finset ℕ} {n B k : ℕ}
    (hB : 1 < B)
    (hbase : ∀ a ∈ coarsePrimeWorldFullTown S n, ∀ q ∈ squareOffsetPrimeSupport n a, B ≤ q)
    (hthreshold : (n + 1) ^ 2 ≤ B ^ (k + 1)) :
    coarseFullTownSupportExcess S n ≤ min
      ((coarseTownDeletionVertices S n).card * (k - 1) + coarseTownRetainedSupportExcess S n)
      ((coarseTownRightDeletionVertices S n).card * (k - 1) + coarseTownRightRetainedSupportExcess S n) :=
  le_min (coarseTown_product_threshold_loss_upper_ge_excess hB hbase hthreshold)
    (coarseTown_right_product_threshold_loss_upper_ge_excess hB hbase hthreshold)

theorem coarseTown_capacity_frontier_implies_better_deficit {S : Finset ℕ} (hS : KnownPrimeScales S)
    (n : ℕ) (left right : ℕ → ℕ)
    (hl : ∀ a ∈ coarseTownDeletionVertices S n, (coarseTownTerminalPrimesAt S n a).card ≤ left a)
    (hr : ∀ a ∈ coarseTownRightDeletionVertices S n, (coarseTownMinimumTerminalPrimesAt S n a).card ≤ right a)
    (hfrontier : min
      ((∑ a ∈ coarseTownDeletionVertices S n, left a) + coarseTownRetainedSupportExcess S n)
      ((∑ a ∈ coarseTownRightDeletionVertices S n, right a) + coarseTownRightRetainedSupportExcess S n) +
        ((coarseOutsidePrimes S n).card - (coarseFullTownActivePrimes S n).card) <
          (coarseFullTownUncoveredSeats S n).card) :
    (coarseOutsidePrimes S n).card < (coarseTownBetterRemainder S n).card := by
  apply (coarseTownBetter_deficit_iff_loss_frontier hS n).mpr
  have hb := coarseTown_betterLoss_le_capacity_sums hS n left right hl hr
  omega

end DkMath.NumberTheory.Legendre
