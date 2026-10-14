/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.CoarseTownPrimeHandoff
import DkMath.NumberTheory.PrimorialUniverse.FinitePrimeSynchronization
import Mathlib.Algebra.Order.BigOperators.Group.Finset

#print "file: DkMath.NumberTheory.Legendre.CoarseTownTerminalProduct"

/-! Actual terminal-source partitions and squarefree product budgets. -/
namespace DkMath.NumberTheory.Legendre

open DkMath.NumberTheory.Primitive DkMath.NumberTheory.StructuralArithmetic
open DkMath.NumberTheory.PrimorialUniverse
open scoped BigOperators

noncomputable def coarseTownTerminalPrimesAt (S : Finset ℕ) (n a : ℕ) : Finset ℕ := by
  classical
  exact (squareOffsetPrimeSupport n a).filter (fun q => coarseTownFiberMaximumAt S n q a)

noncomputable def coarseTownMinimumTerminalPrimesAt (S : Finset ℕ) (n a : ℕ) : Finset ℕ := by
  classical
  exact (squareOffsetPrimeSupport n a).filter (fun q => coarseTownFiberMinimumAt S n q a)

@[simp] theorem mem_coarseTownTerminalPrimesAt {S : Finset ℕ} {n a q : ℕ} :
    q ∈ coarseTownTerminalPrimesAt S n a ↔
      q ∈ squareOffsetPrimeSupport n a ∧ coarseTownFiberMaximumAt S n q a := by
  classical
  exact Finset.mem_filter

@[simp] theorem mem_coarseTownMinimumTerminalPrimesAt {S : Finset ℕ} {n a q : ℕ} :
    q ∈ coarseTownMinimumTerminalPrimesAt S n a ↔
      q ∈ squareOffsetPrimeSupport n a ∧ coarseTownFiberMinimumAt S n q a := by
  classical
  exact Finset.mem_filter

theorem coarseTownTerminalPrimesAt_subset_support (S : Finset ℕ) (n a : ℕ) :
    coarseTownTerminalPrimesAt S n a ⊆ squareOffsetPrimeSupport n a := by
  classical
  exact Finset.filter_subset _ _

theorem coarseTownMinimumTerminalPrimesAt_subset_support (S : Finset ℕ) (n a : ℕ) :
    coarseTownMinimumTerminalPrimesAt S n a ⊆ squareOffsetPrimeSupport n a := by
  classical
  exact Finset.filter_subset _ _

theorem coarseTownTerminalPrimesAt_subset_active {S : Finset ℕ} (hS : KnownPrimeScales S)
    {n a : ℕ} (ha : a ∈ coarsePrimeWorldFullTown S n) :
    coarseTownTerminalPrimesAt S n a ⊆ coarseFullTownActivePrimes S n := by
  intro q hq
  have h := mem_coarseTownTerminalPrimesAt.mp hq
  exact mem_coarseFullTownActivePrimes.mpr
    ⟨coarse_survivor_support_outside (coarseFullTown_survivor hS ha) h.1, a,h.2.1⟩

theorem coarseTownTerminalPrimesAt_subset_outside {S : Finset ℕ} (hS : KnownPrimeScales S)
    {n a : ℕ} (ha : a ∈ coarsePrimeWorldFullTown S n) :
    coarseTownTerminalPrimesAt S n a ⊆ coarseOutsidePrimes S n :=
  (coarseTownTerminalPrimesAt_subset_active hS ha).trans (coarseFullTownActivePrimes_subset S n)

theorem coarseTownMinimumTerminalPrimesAt_subset_active {S : Finset ℕ} (hS : KnownPrimeScales S)
    {n a : ℕ} (ha : a ∈ coarsePrimeWorldFullTown S n) :
    coarseTownMinimumTerminalPrimesAt S n a ⊆ coarseFullTownActivePrimes S n := by
  intro q hq
  have h := mem_coarseTownMinimumTerminalPrimesAt.mp hq
  exact mem_coarseFullTownActivePrimes.mpr
    ⟨coarse_survivor_support_outside (coarseFullTown_survivor hS ha) h.1, a,h.2.1⟩

theorem coarseTown_terminal_continuing_partition {S : Finset ℕ} (hS : KnownPrimeScales S)
    {n a : ℕ} (ha : a ∈ coarsePrimeWorldFullTown S n) :
    coarseTownTerminalPrimesAt S n a ∪ coarseTownDeletionWitnessPrimes S n a =
      squareOffsetPrimeSupport n a ∧
    Disjoint (coarseTownTerminalPrimesAt S n a) (coarseTownDeletionWitnessPrimes S n a) := by
  classical
  constructor
  · ext q
    constructor
    · intro hq
      rcases Finset.mem_union.mp hq with hq | hq
      · exact (mem_coarseTownTerminalPrimesAt.mp hq).1
      · exact coarseTownDeletionWitnessPrimes_subset_support S n a hq
    · intro hq
      have hF : a ∈ coarseFullTownPrimeFiber S n q := Finset.mem_filter.mpr ⟨ha,hq⟩
      by_cases hm : ∀ b ∈ coarseFullTownPrimeFiber S n q, b ≤ a
      · exact Finset.mem_union_left _ (mem_coarseTownTerminalPrimesAt.mpr ⟨hq,hF,hm⟩)
      · push Not at hm
        exact Finset.mem_union_right _ (Finset.mem_filter.mpr
          ⟨coarse_survivor_support_outside (coarseFullTown_survivor hS ha) hq,
            mem_coarseTownNonmaximumFiberSeats.mpr ⟨hF,hm⟩⟩)
  · rw [Finset.disjoint_left]
    intro q ht hc
    have hm := (mem_coarseTownTerminalPrimesAt.mp ht).2
    obtain ⟨_,b,hb,hab⟩ := mem_coarseTownNonmaximumFiberSeats.mp (Finset.mem_filter.mp hc).2
    have hle := hm.2 b hb
    omega

theorem coarseTown_minimum_continuing_partition {S : Finset ℕ} (hS : KnownPrimeScales S)
    {n a : ℕ} (ha : a ∈ coarsePrimeWorldFullTown S n) :
    coarseTownMinimumTerminalPrimesAt S n a ∪ coarseTownRightDeletionWitnessPrimes S n a =
      squareOffsetPrimeSupport n a ∧
    Disjoint (coarseTownMinimumTerminalPrimesAt S n a) (coarseTownRightDeletionWitnessPrimes S n a) := by
  classical
  constructor
  · ext q
    constructor
    · intro hq
      rcases Finset.mem_union.mp hq with hq | hq
      · exact (mem_coarseTownMinimumTerminalPrimesAt.mp hq).1
      · exact coarseTownRightDeletionWitnessPrimes_subset_support S n a hq
    · intro hq
      have hF : a ∈ coarseFullTownPrimeFiber S n q := Finset.mem_filter.mpr ⟨ha,hq⟩
      by_cases hm : ∀ b ∈ coarseFullTownPrimeFiber S n q, a ≤ b
      · exact Finset.mem_union_left _ (mem_coarseTownMinimumTerminalPrimesAt.mpr ⟨hq,hF,hm⟩)
      · push Not at hm
        exact Finset.mem_union_right _ (Finset.mem_filter.mpr
          ⟨coarse_survivor_support_outside (coarseFullTown_survivor hS ha) hq,
            mem_coarseTownNonminimumFiberSeats.mpr ⟨hF,hm⟩⟩)
  · rw [Finset.disjoint_left]
    intro q ht hc
    have hm := (mem_coarseTownMinimumTerminalPrimesAt.mp ht).2
    obtain ⟨_,b,hb,hba⟩ := mem_coarseTownNonminimumFiberSeats.mp (Finset.mem_filter.mp hc).2
    have hle := hm.2 b hb
    omega

theorem coarseTown_terminal_continuing_cards {S : Finset ℕ} (hS : KnownPrimeScales S)
    {n a : ℕ} (ha : a ∈ coarsePrimeWorldFullTown S n) :
    (coarseTownTerminalPrimesAt S n a).card + (coarseTownDeletionWitnessPrimes S n a).card =
      (squareOffsetPrimeSupport n a).card := by
  have h := coarseTown_terminal_continuing_partition hS ha
  rw [← Finset.card_union_of_disjoint h.2,h.1]

theorem coarseTown_minimum_continuing_cards {S : Finset ℕ} (hS : KnownPrimeScales S)
    {n a : ℕ} (ha : a ∈ coarsePrimeWorldFullTown S n) :
    (coarseTownMinimumTerminalPrimesAt S n a).card + (coarseTownRightDeletionWitnessPrimes S n a).card =
      (squareOffsetPrimeSupport n a).card := by
  have h := coarseTown_minimum_continuing_partition hS ha
  rw [← Finset.card_union_of_disjoint h.2,h.1]

theorem mem_coarseTownDeletionVertices_iff_continuing_nonempty {S : Finset ℕ}
    (hS : KnownPrimeScales S) (n a : ℕ) :
    a ∈ coarseTownDeletionVertices S n ↔ (coarseTownDeletionWitnessPrimes S n a).Nonempty := by
  rw [mem_coarseTownDeletionVertices_iff_multiplicity_pos hS,coarseTownDeletionMultiplicity,
    Finset.card_pos]

theorem mem_coarseTownRightDeletionVertices_iff_continuing_nonempty {S : Finset ℕ}
    (hS : KnownPrimeScales S) (n a : ℕ) :
    a ∈ coarseTownRightDeletionVertices S n ↔ (coarseTownRightDeletionWitnessPrimes S n a).Nonempty := by
  rw [mem_coarseTownRightDeletionVertices_iff_multiplicity_pos hS,coarseTownRightDeletionMultiplicity,
    Finset.card_pos]

theorem squareOffsetPrimeSupport_isFinitePrimeBasis (n a : ℕ) :
    IsFinitePrimeBasis (squareOffsetPrimeSupport n a) := by
  intro q hq
  exact (mem_squareOffsetPrimeSupport.mp hq).1

theorem squareOffsetPrimeSupport_product_dvd (n a : ℕ) :
    (squareOffsetPrimeSupport n a).prod id ∣ n ^ 2 + a :=
  finitePrimeBasisProduct_dvd_of_commonMultiple (squareOffsetPrimeSupport_isFinitePrimeBasis n a)
    (fun _q hq => (mem_squareOffsetPrimeSupport.mp hq).2.2)

theorem squareOffset_completePoint_bounds {n a : ℕ} (ha : SquareOffset n a) :
    0 < n ^ 2 + a ∧ n ^ 2 + a < (n + 1) ^ 2 := by
  rcases ha with ⟨hapos,haend⟩
  constructor
  · omega
  · nlinarith

theorem squareOffsetPrimeSupport_product_bounds {n a : ℕ} (ha : SquareOffset n a) :
    (squareOffsetPrimeSupport n a).prod id ≤ n ^ 2 + a ∧ n ^ 2 + a < (n + 1) ^ 2 :=
  ⟨Nat.le_of_dvd (squareOffset_completePoint_bounds ha).1 (squareOffsetPrimeSupport_product_dvd n a),
    (squareOffset_completePoint_bounds ha).2⟩

theorem coarseTown_initial_support_gt_cutoff {P n a q : ℕ}
    (ha : a ∈ coarsePrimeWorldFullTown (primeScalesUpTo P) n)
    (hq : q ∈ squareOffsetPrimeSupport n a) : P < q := by
  have ho := coarse_survivor_support_outside
    (coarseFullTown_survivor (knownPrimeScales_primeScalesUpTo P) ha) hq
  have hn := (Finset.mem_sdiff.mp ho).2
  have hp := (mem_squareOffsetPrimeSupport.mp hq).1
  by_contra h
  exact hn (mem_primeScalesUpTo.mpr ⟨hp,by omega⟩)

/-- General pointwise-base form, also valid for noninitial certified worlds. -/
theorem squareOffsetPrimeSupport_power_bounds {n a B : ℕ} (ha : SquareOffset n a)
    (hB : ∀ q ∈ squareOffsetPrimeSupport n a, B ≤ q) :
    B ^ (squareOffsetPrimeSupport n a).card ≤ (squareOffsetPrimeSupport n a).prod id ∧
      (squareOffsetPrimeSupport n a).prod id ≤ n ^ 2 + a ∧ n ^ 2 + a < (n + 1) ^ 2 :=
  ⟨Finset.pow_card_le_prod _ id B hB,squareOffsetPrimeSupport_product_bounds ha⟩

theorem coarseTown_initial_support_power_bounds {P n a : ℕ}
    (ha : a ∈ coarsePrimeWorldFullTown (primeScalesUpTo P) n) :
    (P + 1) ^ (squareOffsetPrimeSupport n a).card ≤ (squareOffsetPrimeSupport n a).prod id ∧
      (squareOffsetPrimeSupport n a).prod id ≤ n ^ 2 + a ∧ n ^ 2 + a < (n + 1) ^ 2 :=
  squareOffsetPrimeSupport_power_bounds
    (mem_squareOffsets.mp (coarseFullTown_subset_squareOffsets _ _ ha))
    (fun _q hq => by have h := coarseTown_initial_support_gt_cutoff ha hq; omega)

theorem coarseTown_terminal_continuing_product_dvd {S : Finset ℕ} (hS : KnownPrimeScales S)
    {n a : ℕ} (ha : a ∈ coarsePrimeWorldFullTown S n) :
    (coarseTownTerminalPrimesAt S n a).prod id * (coarseTownDeletionWitnessPrimes S n a).prod id ∣
      n ^ 2 + a := by
  have h := coarseTown_terminal_continuing_partition hS ha
  rw [← Finset.prod_union h.2,h.1]
  exact squareOffsetPrimeSupport_product_dvd n a

theorem coarseTown_minimum_continuing_product_dvd {S : Finset ℕ} (hS : KnownPrimeScales S)
    {n a : ℕ} (ha : a ∈ coarsePrimeWorldFullTown S n) :
    (coarseTownMinimumTerminalPrimesAt S n a).prod id * (coarseTownRightDeletionWitnessPrimes S n a).prod id ∣
      n ^ 2 + a := by
  have h := coarseTown_minimum_continuing_partition hS ha
  rw [← Finset.prod_union h.2,h.1]
  exact squareOffsetPrimeSupport_product_dvd n a

theorem coarseTown_continuing_mul_terminal_product_dvd {S : Finset ℕ} (hS : KnownPrimeScales S)
    {n a p : ℕ} (ha : a ∈ coarsePrimeWorldFullTown S n)
    (hp : p ∈ coarseTownDeletionWitnessPrimes S n a) :
    p * (coarseTownTerminalPrimesAt S n a).prod id ∣ n ^ 2 + a := by
  have hd : p ∣ (coarseTownDeletionWitnessPrimes S n a).prod id := Finset.dvd_prod_of_mem id hp
  have hmul := mul_dvd_mul_left ((coarseTownTerminalPrimesAt S n a).prod id) hd
  exact dvd_trans (by simpa [Nat.mul_comm] using hmul) (coarseTown_terminal_continuing_product_dvd hS ha)

theorem coarseTown_initial_terminal_continuing_power {P n a : ℕ}
    (ha : a ∈ coarsePrimeWorldFullTown (primeScalesUpTo P) n) :
    (P + 1) ^ ((coarseTownTerminalPrimesAt (primeScalesUpTo P) n a).card +
      (coarseTownDeletionWitnessPrimes (primeScalesUpTo P) n a).card) ≤ n ^ 2 + a := by
  rw [coarseTown_terminal_continuing_cards (knownPrimeScales_primeScalesUpTo P) ha]
  exact (coarseTown_initial_support_power_bounds ha).1.trans
    (coarseTown_initial_support_power_bounds ha).2.1

theorem coarseTown_deleted_terminal_power {S : Finset ℕ} (hS : KnownPrimeScales S)
    {n a B : ℕ} (ha : a ∈ coarseTownDeletionVertices S n)
    (hBpos : 0 < B) (hB : ∀ q ∈ squareOffsetPrimeSupport n a, B ≤ q) :
    B ^ ((coarseTownTerminalPrimesAt S n a).card + 1) ≤ n ^ 2 + a := by
  have hav := coarseTownDeletionVertices_subset S n ha
  have hc := coarseTown_terminal_continuing_cards hS hav
  have hp := Finset.card_pos.mpr ((mem_coarseTownDeletionVertices_iff_continuing_nonempty hS n a).mp ha)
  have hexp : (coarseTownTerminalPrimesAt S n a).card + 1 ≤ (squareOffsetPrimeSupport n a).card := by omega
  have hb := squareOffsetPrimeSupport_power_bounds
    (mem_squareOffsets.mp (coarseFullTown_subset_squareOffsets S n hav)) hB
  exact (Nat.pow_le_pow_right hBpos hexp).trans (hb.1.trans hb.2.1)

theorem coarseTown_rightDeleted_terminal_power {S : Finset ℕ} (hS : KnownPrimeScales S)
    {n a B : ℕ} (ha : a ∈ coarseTownRightDeletionVertices S n)
    (hBpos : 0 < B) (hB : ∀ q ∈ squareOffsetPrimeSupport n a, B ≤ q) :
    B ^ ((coarseTownMinimumTerminalPrimesAt S n a).card + 1) ≤ n ^ 2 + a := by
  have hav := coarseTownRightDeletionVertices_subset S n ha
  have hc := coarseTown_minimum_continuing_cards hS hav
  have hp := Finset.card_pos.mpr ((mem_coarseTownRightDeletionVertices_iff_continuing_nonempty hS n a).mp ha)
  have hexp : (coarseTownMinimumTerminalPrimesAt S n a).card + 1 ≤ (squareOffsetPrimeSupport n a).card := by omega
  have hb := squareOffsetPrimeSupport_power_bounds
    (mem_squareOffsets.mp (coarseFullTown_subset_squareOffsets S n hav)) hB
  exact (Nat.pow_le_pow_right hBpos hexp).trans (hb.1.trans hb.2.1)

theorem coarseTown_initial_deleted_terminal_power {P n a : ℕ}
    (ha : a ∈ coarseTownDeletionVertices (primeScalesUpTo P) n) :
    (P + 1) ^ ((coarseTownTerminalPrimesAt (primeScalesUpTo P) n a).card + 1) ≤ n ^ 2 + a :=
  coarseTown_deleted_terminal_power (knownPrimeScales_primeScalesUpTo P) ha (by omega)
    (fun _q hq => by
      have h := coarseTown_initial_support_gt_cutoff (coarseTownDeletionVertices_subset _ _ ha) hq
      simpa only [id_eq] using Nat.add_one_le_iff.mpr h)

theorem coarseTown_initial_continuing_mul_terminal_power {P n a p : ℕ}
    (ha : a ∈ coarsePrimeWorldFullTown (primeScalesUpTo P) n)
    (hp : p ∈ coarseTownDeletionWitnessPrimes (primeScalesUpTo P) n a) :
    p * (P + 1) ^ (coarseTownTerminalPrimesAt (primeScalesUpTo P) n a).card ≤ n ^ 2 + a := by
  have hl := Finset.pow_card_le_prod (coarseTownTerminalPrimesAt (primeScalesUpTo P) n a) id (P + 1)
    (fun _q hq => by
      have h := coarseTown_initial_support_gt_cutoff ha (coarseTownTerminalPrimesAt_subset_support _ _ _ hq)
      simpa only [id_eq] using Nat.add_one_le_iff.mpr h)
  have hd := coarseTown_continuing_mul_terminal_product_dvd (knownPrimeScales_primeScalesUpTo P) ha hp
  exact (Nat.mul_le_mul_left p hl).trans (Nat.le_of_dvd
    (squareOffset_completePoint_bounds (mem_squareOffsets.mp (coarseFullTown_subset_squareOffsets _ _ ha))).1 hd)

/-- Exact exponent threshold; the strict shell boundary saves a further unit. -/
theorem terminal_card_lt_of_power_threshold {B t m H k : ℕ} (hB : 1 < B)
    (hpow : B ^ (t + 1) ≤ m) (hm : m < H) (hH : H ≤ B ^ (k + 1)) : t < k := by
  have hlt : B ^ (t + 1) < B ^ (k + 1) := lt_of_le_of_lt hpow (lt_of_lt_of_le hm hH)
  have hexp := (Nat.pow_lt_pow_iff_right hB).mp hlt
  omega

theorem support_card_le_of_power_threshold {B s m H k : ℕ} (hB : 1 < B)
    (hpow : B ^ s ≤ m) (hm : m < H) (hH : H ≤ B ^ (k + 1)) : s ≤ k := by
  have hlt : B ^ s < B ^ (k + 1) := lt_of_le_of_lt hpow (lt_of_lt_of_le hm hH)
  have hexp := (Nat.pow_lt_pow_iff_right hB).mp hlt
  omega

theorem coarseTown_deleted_terminal_threshold {S : Finset ℕ} (hS : KnownPrimeScales S)
    {n a B k : ℕ} (ha : a ∈ coarseTownDeletionVertices S n) (hB : 1 < B)
    (hbase : ∀ q ∈ squareOffsetPrimeSupport n a, B ≤ q)
    (hthreshold : (n + 1) ^ 2 ≤ B ^ (k + 1)) : (coarseTownTerminalPrimesAt S n a).card < k :=
  terminal_card_lt_of_power_threshold hB (coarseTown_deleted_terminal_power hS ha (by omega) hbase)
    (squareOffset_completePoint_bounds (mem_squareOffsets.mp
      (coarseFullTown_subset_squareOffsets _ _ (coarseTownDeletionVertices_subset _ _ ha)))).2 hthreshold

theorem coarseTown_rightDeleted_terminal_threshold {S : Finset ℕ} (hS : KnownPrimeScales S)
    {n a B k : ℕ} (ha : a ∈ coarseTownRightDeletionVertices S n) (hB : 1 < B)
    (hbase : ∀ q ∈ squareOffsetPrimeSupport n a, B ≤ q)
    (hthreshold : (n + 1) ^ 2 ≤ B ^ (k + 1)) : (coarseTownMinimumTerminalPrimesAt S n a).card < k :=
  terminal_card_lt_of_power_threshold hB (coarseTown_rightDeleted_terminal_power hS ha (by omega) hbase)
    (squareOffset_completePoint_bounds (mem_squareOffsets.mp
      (coarseFullTown_subset_squareOffsets _ _ (coarseTownRightDeletionVertices_subset _ _ ha)))).2 hthreshold

theorem coarseTown_deleted_terminal_le_support_excess {S : Finset ℕ} (hS : KnownPrimeScales S)
    {n a : ℕ} (ha : a ∈ coarseTownDeletionVertices S n) :
    (coarseTownTerminalPrimesAt S n a).card ≤ (squareOffsetPrimeSupport n a).card - 1 := by
  have hc := coarseTown_terminal_continuing_cards hS (coarseTownDeletionVertices_subset _ _ ha)
  have hp := Finset.card_pos.mpr ((mem_coarseTownDeletionVertices_iff_continuing_nonempty hS n a).mp ha)
  omega

end DkMath.NumberTheory.Legendre
