/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.ParitySafePersistenceParity
import DkMath.NumberTheory.Legendre.ParitySafeCollisionPairOverlapCancellation

#print "file: DkMath.NumberTheory.Legendre.ParitySafeFreshCost"

/-!
# Fresh directions in the existing support and pair ledgers

A singleton fresh support has zero excess. If persistent support is empty,
one first fresh direction is uncharged; otherwise every fresh direction adds
support excess. All counts below use the actual production support and lower
candidate sector. Pair representatives reuse `Internal.upperPairs`.
-/

namespace DkMath.NumberTheory.Legendre

open Internal
open scoped BigOperators

/-- Actual lower seats with one active direction, which is fresh. -/
noncomputable def lowerSingletonFreshSeats (n : ℕ) : Finset ℕ :=
  (lowerParitySafeCandidates n).filter (fun r =>
    (paritySafeActiveSupport (n + 1) r).card = 1 ∧
      (lowerParitySafeFreshSupport n r).Nonempty)

/-- Fresh incidences on actual seats with at least two active directions. -/
noncomputable def lowerMultiFreshCount (n : ℕ) : ℕ :=
  ∑ r ∈ (lowerParitySafeCandidates n).filter
    (fun r => 2 ≤ (paritySafeActiveSupport (n + 1) r).card),
    (lowerParitySafeFreshSupport n r).card

/-- Fresh occupied seats whose persistent support is empty. Each has one
mandatory first-support slot before excess is charged. -/
noncomputable def lowerFreshWithoutPersistentSeats (n : ℕ) : Finset ℕ :=
  (lowerParitySafeCandidates n).filter (fun r =>
    (lowerParitySafePersistentSupport n r).card = 0 ∧
      (lowerParitySafeFreshSupport n r).Nonempty)

/-- Incremental excess contributed by fresh directions after retaining the
persistent support's mandatory first direction, if there is one. -/
noncomputable def lowerFreshSupportExcessCharge (n r : ℕ) : ℕ :=
  (lowerParitySafeFreshSupport n r).card -
    (if (lowerParitySafePersistentSupport n r).card = 0 then 1 else 0)

/-- The actual lower-sector sum of incremental support-excess charges. -/
noncomputable def lowerFreshSupportExcessChargeCount (n : ℕ) : ℕ :=
  ∑ r ∈ lowerParitySafeCandidates n, lowerFreshSupportExcessCharge n r

/-- Exact local excess partition, valid also for empty support. -/
theorem lower_active_excess_eq_persistent_excess_add_fresh_charge (n r : ℕ) :
    (paritySafeActiveSupport (n + 1) r).card - 1 =
      ((lowerParitySafePersistentSupport n r).card - 1) +
        lowerFreshSupportExcessCharge n r := by
  have hs := lowerParitySafeActiveSupport_card_eq n r
  unfold lowerFreshSupportExcessCharge
  by_cases hp : (lowerParitySafePersistentSupport n r).card = 0 <;> simp only [hp, ↓reduceIte]
  all_goals omega

/-- The precise zero-excess singleton mechanism. -/
theorem lower_singleton_fresh_has_zero_excess {n r : ℕ}
    (hs : (paritySafeActiveSupport (n + 1) r).card = 1)
    (hf : (lowerParitySafeFreshSupport n r).Nonempty) :
    (lowerParitySafeFreshSupport n r).card = 1 ∧
      (lowerParitySafePersistentSupport n r).card = 0 ∧
      lowerFreshSupportExcessCharge n r = 0 ∧
      (paritySafeActiveSupport (n + 1) r).card - 1 = 0 := by
  have hp := lowerParitySafeActiveSupport_card_eq n r
  have hfpos := Finset.card_pos.mpr hf
  have hP : (lowerParitySafePersistentSupport n r).card = 0 := by omega
  simp [lowerFreshSupportExcessCharge, hP]
  omega

/-- The singleton class is exactly fresh occupancy with zero production
support excess, not an independently chosen notion of free cost. -/
theorem mem_lowerSingletonFreshSeats_iff_zero_excess {n r : ℕ} :
    r ∈ lowerSingletonFreshSeats n ↔ r ∈ lowerParitySafeCandidates n ∧
      (lowerParitySafeFreshSupport n r).Nonempty ∧
      (paritySafeActiveSupport (n + 1) r).card - 1 = 0 := by
  classical
  constructor
  · intro hr
    have h := Finset.mem_filter.mp hr
    exact ⟨h.1, h.2.2, by omega⟩
  · rintro ⟨hr, hf, he⟩
    have hpos := Finset.card_pos.mpr hf
    have hs := lowerParitySafeActiveSupport_card_eq n r
    exact Finset.mem_filter.mpr ⟨hr, by omega, hf⟩

/-- A fresh occupied multiple-support seat has positive incremental cost. -/
theorem lowerFreshSupportExcessCharge_pos_of_multi {n r : ℕ}
    (hk : 2 ≤ (paritySafeActiveSupport (n + 1) r).card)
    (hf : (lowerParitySafeFreshSupport n r).Nonempty) :
    0 < lowerFreshSupportExcessCharge n r := by
  have hs := lowerParitySafeActiveSupport_card_eq n r
  have hfpos := Finset.card_pos.mpr hf
  unfold lowerFreshSupportExcessCharge
  by_cases hp : (lowerParitySafePersistentSupport n r).card = 0 <;>
    simp only [hp, ↓reduceIte] <;> omega

/-- Fresh support of size at least two is exactly the non-singleton branch.
The singleton branch contributes one incidence and no support excess. -/
theorem lowerParitySafeFreshCount_eq_singleton_add_multi (n : ℕ) :
    lowerParitySafeFreshCount n = (lowerSingletonFreshSeats n).card + lowerMultiFreshCount n := by
  classical
  unfold lowerParitySafeFreshCount lowerSingletonFreshSeats lowerMultiFreshCount
  rw [Finset.card_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  have hs := lowerParitySafeActiveSupport_card_eq n r
  by_cases hf : (lowerParitySafeFreshSupport n r).Nonempty
  · have hfpos := Finset.card_pos.mpr hf
    by_cases hk : (paritySafeActiveSupport (n + 1) r).card = 1
    · have hnot : ¬2 ≤ (paritySafeActiveSupport (n + 1) r).card := by omega
      simp [hf, hk]
      omega
    · have hlarge : 2 ≤ (paritySafeActiveSupport (n + 1) r).card := by omega
      simp [hf, hk, hlarge]
  · have hz : (lowerParitySafeFreshSupport n r).card = 0 :=
      Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hf)
    simp [hf, hz]

/-- Multiple-support fresh incidences pay existing support excess, with at
most a factor of two for an entirely fresh support of size two. -/
theorem lowerMultiFreshCount_le_two_supportExcess (n : ℕ) :
    lowerMultiFreshCount n ≤ 2 * paritySafeSupportExcess (n + 1) := by
  classical
  unfold lowerMultiFreshCount paritySafeSupportExcess
  rw [Finset.mul_sum]
  calc
    (∑ r ∈ (lowerParitySafeCandidates n).filter
        (fun r => 2 ≤ (paritySafeActiveSupport (n + 1) r).card),
        (lowerParitySafeFreshSupport n r).card) ≤
        ∑ r ∈ (lowerParitySafeCandidates n).filter
          (fun r => 2 ≤ (paritySafeActiveSupport (n + 1) r).card),
          2 * ((paritySafeActiveSupport (n + 1) r).card - 1) := by
      apply Finset.sum_le_sum
      intro r hr
      have hk := (Finset.mem_filter.mp hr).2
      have hs := lowerParitySafeActiveSupport_card_eq n r
      omega
    _ ≤ ∑ r ∈ squareAnchorOddPointCoprimeOffsets (n + 1),
        2 * ((paritySafeActiveSupport (n + 1) r).card - 1) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
      · intros; omega

/-- Exact first-slot / incremental-excess partition of fresh incidences. -/
theorem lowerParitySafeFreshCount_eq_firstSlots_add_excessCharge (n : ℕ) :
    lowerParitySafeFreshCount n = (lowerFreshWithoutPersistentSeats n).card +
      lowerFreshSupportExcessChargeCount n := by
  classical
  unfold lowerParitySafeFreshCount lowerFreshWithoutPersistentSeats lowerFreshSupportExcessChargeCount
  rw [Finset.card_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  unfold lowerFreshSupportExcessCharge
  by_cases hp : (lowerParitySafePersistentSupport n r).card = 0
  · by_cases hf : (lowerParitySafeFreshSupport n r).Nonempty
    · have hpos := Finset.card_pos.mpr hf
      simp only [hp, hf, and_self, ite_true]
      omega
    · have hz : (lowerParitySafeFreshSupport n r).card = 0 :=
        Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hf)
      simp [hp, hf, hz]
  · simp [hp]

/-- The incremental charge belongs to the production support-excess ledger. -/
theorem lowerFreshSupportExcessChargeCount_le_supportExcess (n : ℕ) :
    lowerFreshSupportExcessChargeCount n ≤ paritySafeSupportExcess (n + 1) := by
  classical
  calc
    lowerFreshSupportExcessChargeCount n ≤ ∑ r ∈ lowerParitySafeCandidates n,
        ((paritySafeActiveSupport (n + 1) r).card - 1) := by
      apply Finset.sum_le_sum
      intro r hr
      have h := lower_active_excess_eq_persistent_excess_add_fresh_charge n r
      omega
    _ ≤ paritySafeSupportExcess (n + 1) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by intros; omega)

/-- On collided seats, the charge is paid by the existing named collision
support cost; no residual-pair injection is asserted. -/
theorem lowerFreshCharge_onCollision_le_collisionSupportCost (n : ℕ) :
    (∑ r ∈ lowerParitySafeCandidates n ∩ paritySafeRechargeExactDepthFiberCollisionSeats (n + 1),
      lowerFreshSupportExcessCharge n r) ≤ paritySafeDepthCollisionLocalSupportCost (n + 1) := by
  classical
  calc
    _ ≤ ∑ r ∈ lowerParitySafeCandidates n ∩ paritySafeRechargeExactDepthFiberCollisionSeats (n + 1),
        ((paritySafeActiveSupport (n + 1) r).card - 1) := by
      apply Finset.sum_le_sum
      intro r hr
      have h := lower_active_excess_eq_persistent_excess_add_fresh_charge n r
      omega
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right (by intros; omega)

/-- Singleton fresh seats are a genuine zero-cost class; the first-slot class
also contains one slot from entirely fresh multiple supports. -/
theorem lowerSingletonFreshSeats_subset_firstSlots (n : ℕ) :
    lowerSingletonFreshSeats n ⊆ lowerFreshWithoutPersistentSeats n := by
  classical
  intro r hr
  obtain ⟨hseat, hs, hf⟩ := Finset.mem_filter.mp hr
  exact Finset.mem_filter.mpr
    ⟨hseat, (lower_singleton_fresh_has_zero_excess hs hf).2.1, hf⟩

/-- Actual fresh incidences are bounded by singleton capacity plus paid mass. -/
theorem lowerFreshCount_le_singleton_add_two_supportExcess (n : ℕ) :
    lowerParitySafeFreshCount n ≤
      (lowerSingletonFreshSeats n).card + 2 * paritySafeSupportExcess (n + 1) := by
  rw [lowerParitySafeFreshCount_eq_singleton_add_multi]
  exact Nat.add_le_add_left (lowerMultiFreshCount_le_two_supportExcess n) _

/-- The sharper incremental accounting has coefficient one, with a larger
first-slot capacity instead of the zero-cost singleton class. -/
theorem lowerFreshCount_le_firstSlots_add_supportExcess (n : ℕ) :
    lowerParitySafeFreshCount n ≤
      (lowerFreshWithoutPersistentSeats n).card + paritySafeSupportExcess (n + 1) := by
  rw [lowerParitySafeFreshCount_eq_firstSlots_add_excessCharge]
  exact Nat.add_le_add_left (lowerFreshSupportExcessChargeCount_le_supportExcess n) _

private theorem choose_add_two (P F : ℕ) :
    Nat.choose (P + F) 2 = Nat.choose P 2 + P * F + Nat.choose F 2 := by
  induction F with
  | zero => simp
  | succ F ih =>
    rw [Nat.add_succ, Nat.choose_succ_succ, Nat.choose_one_right, ih,
      Nat.choose_succ_succ, Nat.choose_one_right]
    ring

/-- Canonical unordered active pairs with at least one fresh endpoint. -/
noncomputable def lowerParitySafeFreshPairs (n r : ℕ) : Finset (ℕ × ℕ) :=
  upperPairs (paritySafeActiveSupport (n + 1) r) \
    upperPairs (lowerParitySafePersistentSupport n r)

/-- The representatives really contain a fresh endpoint, rather than merely
being a subtraction of two unrelated pair counts. -/
theorem mem_lowerParitySafeFreshPairs_iff {n r q s : ℕ} :
    (q, s) ∈ lowerParitySafeFreshPairs n r ↔
      q ∈ paritySafeActiveSupport (n + 1) r ∧
      s ∈ paritySafeActiveSupport (n + 1) r ∧ q < s ∧
      (q ∈ lowerParitySafeFreshSupport n r ∨ s ∈ lowerParitySafeFreshSupport n r) := by
  classical
  constructor
  · intro hp
    have hh := Finset.mem_sdiff.mp hp
    have ha := Finset.mem_filter.mp hh.1
    have hd := Finset.mem_offDiag.mp ha.1
    refine ⟨hd.1, hd.2.1, ha.2, ?_⟩
    by_cases hq : q ∈ squareOffsetPrimeSupport n r
    · right
      apply Finset.mem_sdiff.mpr
      refine ⟨hd.2.1, ?_⟩
      intro hs
      exact hh.2 (Finset.mem_filter.mpr ⟨Finset.mem_offDiag.mpr
        ⟨Finset.mem_inter.mpr ⟨hd.1, hq⟩,
          Finset.mem_inter.mpr ⟨hd.2.1, hs⟩, hd.2.2⟩, ha.2⟩)
    · exact Or.inl (Finset.mem_sdiff.mpr ⟨hd.1, hq⟩)
  · rintro ⟨hq, hs, hlt, hf⟩
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_offDiag.mpr ⟨hq, hs, ne_of_lt hlt⟩, hlt⟩, ?_⟩
    intro hp
    have hd := Finset.mem_offDiag.mp (Finset.mem_filter.mp hp).1
    rcases hf with hf | hf
    · exact (Finset.mem_sdiff.mp hf).2 (Finset.mem_inter.mp hd.1).2
    · exact (Finset.mem_sdiff.mp hf).2 (Finset.mem_inter.mp hd.2.1).2

/-- Persistent-only pair representatives form a subset of the actual active pairs. -/
theorem lower_persistent_upperPairs_subset (n r : ℕ) :
    upperPairs (lowerParitySafePersistentSupport n r) ⊆
      upperPairs (paritySafeActiveSupport (n + 1) r) := by
  classical
  intro pair hp
  have h := Finset.mem_filter.mp hp
  have hd := Finset.mem_offDiag.mp h.1
  exact Finset.mem_filter.mpr ⟨Finset.mem_offDiag.mpr
    ⟨(Finset.mem_inter.mp hd.1).1, (Finset.mem_inter.mp hd.2.1).1, hd.2.2⟩, h.2⟩

/-- Exact pair partition in the existing choose-cardinality notation. -/
theorem lower_active_pair_eq_persistent_pair_add_fresh_pairs (n r : ℕ) :
    Nat.choose (paritySafeActiveSupport (n + 1) r).card 2 =
      Nat.choose (lowerParitySafePersistentSupport n r).card 2 +
        (lowerParitySafeFreshPairs n r).card := by
  classical
  have h := Finset.card_sdiff_add_card_eq_card (lower_persistent_upperPairs_subset n r)
  rw [card_upperPairs_eq_choose, card_upperPairs_eq_choose] at h
  dsimp only [lowerParitySafeFreshPairs]
  omega

/-- Mixed persistent/fresh pairs and fresh/fresh pairs account for every
fresh-involving pair, with no double counting. -/
theorem lowerFreshPairs_card_eq_mixed_add_choose_fresh (n r : ℕ) :
    (lowerParitySafeFreshPairs n r).card =
      (lowerParitySafePersistentSupport n r).card * (lowerParitySafeFreshSupport n r).card +
        Nat.choose (lowerParitySafeFreshSupport n r).card 2 := by
  have hsplit := lower_active_pair_eq_persistent_pair_add_fresh_pairs n r
  rw [lowerParitySafeActiveSupport_card_eq, choose_add_two] at hsplit
  omega

/-- Every fresh occupied seat with multiple active directions has a real
fresh-involving pair. This need not be a residual or collided pair. -/
theorem lowerFreshPairs_card_pos_of_multi {n r : ℕ}
    (hk : 2 ≤ (paritySafeActiveSupport (n + 1) r).card)
    (hf : (lowerParitySafeFreshSupport n r).Nonempty) :
    0 < (lowerParitySafeFreshPairs n r).card := by
  have hsplit := lowerParitySafeActiveSupport_card_eq n r
  have hfpos := Finset.card_pos.mpr hf
  rw [lowerFreshPairs_card_eq_mixed_add_choose_fresh]
  by_cases hp : (lowerParitySafePersistentSupport n r).card = 0
  · have hh : 2 ≤ (lowerParitySafeFreshSupport n r).card := by omega
    have hchoose := Nat.choose_pos hh
    omega
  · have hprod := Nat.mul_pos (by omega : 0 < (lowerParitySafePersistentSupport n r).card) hfpos
    omega

/-- Lower-sector fresh-involving pair mass is a restriction of existing pair overlap. -/
noncomputable def lowerFreshPairOverlapCount (n : ℕ) : ℕ :=
  ∑ r ∈ lowerParitySafeCandidates n, (lowerParitySafeFreshPairs n r).card

theorem lowerFreshPairOverlapCount_le_pairOverlap (n : ℕ) :
    lowerFreshPairOverlapCount n ≤ paritySafePrimePairOverlapCount (n + 1) := by
  classical
  calc
    lowerFreshPairOverlapCount n ≤ ∑ r ∈ lowerParitySafeCandidates n,
        Nat.choose (paritySafeActiveSupport (n + 1) r).card 2 := by
      apply Finset.sum_le_sum
      intro r hr
      have h := lower_active_pair_eq_persistent_pair_add_fresh_pairs n r
      omega
    _ ≤ paritySafePrimePairOverlapCount (n + 1) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by intros; omega)

/-- Fresh pair mass outside collisions is charged to the corresponding
production outside-collision ledger, not to collision residual capacity. -/
theorem lowerFreshPairs_outsideCollision_le_outsidePairOverlap (n : ℕ) :
    (∑ r ∈ lowerParitySafeCandidates n \ paritySafeRechargeExactDepthFiberCollisionSeats (n + 1),
      (lowerParitySafeFreshPairs n r).card) ≤ paritySafePairOverlapOutsideDepthCollision (n + 1) := by
  classical
  calc
    _ ≤ ∑ r ∈ lowerParitySafeCandidates n \ paritySafeRechargeExactDepthFiberCollisionSeats (n + 1),
        Nat.choose (paritySafeActiveSupport (n + 1) r).card 2 := by
      apply Finset.sum_le_sum
      intro r hr
      have h := lower_active_pair_eq_persistent_pair_add_fresh_pairs n r
      omega
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro r hr
        have hh := Finset.mem_sdiff.mp hr
        exact Finset.mem_sdiff.mpr ⟨(Finset.mem_filter.mp hh.1).1, hh.2⟩
      · intros; omega

/-- A collided singleton is impossible, independently of freshness. -/
theorem lower_singleton_not_collision {n r : ℕ}
    (hs : (paritySafeActiveSupport (n + 1) r).card = 1) :
    r ∉ paritySafeRechargeExactDepthFiberCollisionSeats (n + 1) := by
  intro hr
  have h := paritySafeRechargeExactDepthFiberCollision_support_card_ge_four hr
  omega

/-- Temporal fresh demand minus actual singleton capacity pays real support excess. -/
theorem sum_lowerCandidates_sub_persistenceCap_sub_singletons_le_two_excess
    (N T : ℕ) (hfull : ∀ i ∈ Finset.range T, SquareOffsetsFullyCovered (N + i + 1)) :
    (∑ i ∈ Finset.range T, (lowerParitySafeCandidates (N + i)).card) -
        lowerParitySafePersistenceCap N T -
        (∑ i ∈ Finset.range T, (lowerSingletonFreshSeats (N + i)).card) ≤
      2 * ∑ i ∈ Finset.range T, paritySafeSupportExcess (N + i + 1) := by
  have hf := sum_lowerParitySafeCandidates_sub_cap_le_fresh_of_fullyCovered N T hfull
  have hu : (∑ i ∈ Finset.range T, lowerParitySafeFreshCount (N + i)) ≤
      (∑ i ∈ Finset.range T, (lowerSingletonFreshSeats (N + i)).card) +
        2 * ∑ i ∈ Finset.range T, paritySafeSupportExcess (N + i + 1) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun i _ => lowerFreshCount_le_singleton_add_two_supportExcess (N + i))
  omega

/-- Coefficient-one temporal charge using the larger mandatory-first-slot class. -/
theorem sum_lowerCandidates_sub_persistenceCap_sub_firstSlots_le_excess
    (N T : ℕ) (hfull : ∀ i ∈ Finset.range T, SquareOffsetsFullyCovered (N + i + 1)) :
    (∑ i ∈ Finset.range T, (lowerParitySafeCandidates (N + i)).card) -
        lowerParitySafePersistenceCap N T -
        (∑ i ∈ Finset.range T, (lowerFreshWithoutPersistentSeats (N + i)).card) ≤
      ∑ i ∈ Finset.range T, paritySafeSupportExcess (N + i + 1) := by
  have hf := sum_lowerParitySafeCandidates_sub_cap_le_fresh_of_fullyCovered N T hfull
  have hu : (∑ i ∈ Finset.range T, lowerParitySafeFreshCount (N + i)) ≤
      (∑ i ∈ Finset.range T, (lowerFreshWithoutPersistentSeats (N + i)).card) +
        ∑ i ∈ Finset.range T, paritySafeSupportExcess (N + i + 1) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun i _ => lowerFreshCount_le_firstSlots_add_supportExcess (N + i))
  omega

/-- Parity-refined temporal demand pays coefficient-one incremental excess
beyond the actual first-slot capacity. -/
theorem sum_lowerCandidates_sub_parityCap_sub_firstSlots_le_excess
    (N T : ℕ) (hfull : ∀ i ∈ Finset.range T, SquareOffsetsFullyCovered (N + i + 1)) :
    (∑ i ∈ Finset.range T, (lowerParitySafeCandidates (N + i)).card) -
        lowerParitySafeParityPersistenceCap N T -
        (∑ i ∈ Finset.range T, (lowerFreshWithoutPersistentSeats (N + i)).card) ≤
      ∑ i ∈ Finset.range T, paritySafeSupportExcess (N + i + 1) := by
  have hf := sum_lowerCandidates_sub_parityCap_le_fresh_of_fullyCovered N T hfull
  have hu : (∑ i ∈ Finset.range T, lowerParitySafeFreshCount (N + i)) ≤
      (∑ i ∈ Finset.range T, (lowerFreshWithoutPersistentSeats (N + i)).card) +
        ∑ i ∈ Finset.range T, paritySafeSupportExcess (N + i + 1) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun i _ => lowerFreshCount_le_firstSlots_add_supportExcess (N + i))
  omega

/-- The new excess lower bound is an additional left-side charge in the
existing full-cover candidate/incidence balance, summed over a finite run. -/
theorem sum_fullCandidate_add_freshChargeBound_le_incidence
    (N T : ℕ) (hfull : ∀ i ∈ Finset.range T, SquareOffsetsFullyCovered (N + i + 1)) :
    (∑ i ∈ Finset.range T, (squareAnchorOddPointCoprimeOffsets (N + i + 1)).card) +
        ((∑ i ∈ Finset.range T, (lowerParitySafeCandidates (N + i)).card) -
          lowerParitySafeParityPersistenceCap N T -
          (∑ i ∈ Finset.range T, (lowerFreshWithoutPersistentSeats (N + i)).card)) ≤
      ∑ i ∈ Finset.range T, paritySafeIncidenceCount (N + i + 1) := by
  have hcharge := sum_lowerCandidates_sub_parityCap_sub_firstSlots_le_excess N T hfull
  have hbalance : (∑ i ∈ Finset.range T,
      (squareAnchorOddPointCoprimeOffsets (N + i + 1)).card) +
      (∑ i ∈ Finset.range T, paritySafeSupportExcess (N + i + 1)) =
      ∑ i ∈ Finset.range T, paritySafeIncidenceCount (N + i + 1) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    exact paritySafeCandidate_card_add_supportExcess_eq_incidence_of_fullyCovered
      (by omega) (hfull i hi)
  omega

end DkMath.NumberTheory.Legendre
