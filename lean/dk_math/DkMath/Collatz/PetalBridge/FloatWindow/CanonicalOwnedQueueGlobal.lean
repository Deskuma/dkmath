/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalOwnedQueue

#print "file: DkMath.Collatz.PetalBridge.FloatWindow.CanonicalOwnedQueueGlobal"

namespace DkMath.Collatz

/-!
# Global normal form of the canonical source-owned queue

The local recursion preserves source identity block by block.  This module
proves that the same queue is globally the newest upper tail of every
historical carry-two source, after removing the cumulative *actual* consumed
count.  Unused service is deliberately absent from this normal form.
-/

/-- Every carry-two claim source born before canonical block `m`. -/
noncomputable def canonicalHistoricalClaimSourceCarrier
    (n : OddNat) (m : ℕ) : Finset ℕ :=
  carryTwoPositions n (Finset.Ico 0 (canonicalBlockStartTime n m))

/-- Source identities consumed in the strict block prefix `[0,m)`. -/
noncomputable def canonicalOwnedCumulativeConsumedClaimsBeforeBlock
    (n : OddNat) : ℕ → Finset ℕ
  | 0 => ∅
  | m + 1 =>
      canonicalOwnedCumulativeConsumedClaimsBeforeBlock n m ∪
        canonicalOwnedConsumedClaimsAtBlock n m

/-- Scalar actual consumption in the strict block prefix `[0,m)`. -/
noncomputable def canonicalCumulativeConsumedCountBeforeBlock
    (n : OddNat) (m : ℕ) : ℕ :=
  ∑ k ∈ Finset.range m, canonicalQueueConsumed n k

@[simp] theorem canonicalOwnedCumulativeConsumedClaimsBeforeBlock_zero
    (n : OddNat) :
    canonicalOwnedCumulativeConsumedClaimsBeforeBlock n 0 = ∅ := rfl

@[simp] theorem canonicalOwnedCumulativeConsumedClaimsBeforeBlock_succ
    (n : OddNat) (m : ℕ) :
    canonicalOwnedCumulativeConsumedClaimsBeforeBlock n (m + 1) =
      canonicalOwnedCumulativeConsumedClaimsBeforeBlock n m ∪
        canonicalOwnedConsumedClaimsAtBlock n m := rfl

/-- Membership in the cumulative carrier retains the exact consuming block. -/
theorem mem_canonicalOwnedCumulativeConsumedClaimsBeforeBlock_iff
    {n : OddNat} {m i : ℕ} :
    i ∈ canonicalOwnedCumulativeConsumedClaimsBeforeBlock n m ↔
      ∃ k < m, i ∈ canonicalOwnedConsumedClaimsAtBlock n k := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [canonicalOwnedCumulativeConsumedClaimsBeforeBlock_succ,
        Finset.mem_union, ih]
      constructor
      · rintro (⟨k, hkm, hi⟩ | hi)
        · exact ⟨k, by omega, hi⟩
        · exact ⟨m, by omega, hi⟩
      · rintro ⟨k, hkm, hi⟩
        by_cases hkmEq : k = m
        · exact Or.inr (hkmEq ▸ hi)
        · exact Or.inl ⟨k, by omega, hi⟩

/-- A consumed source is a member of the claims available at that block. -/
theorem mem_canonicalOwnedAvailableClaimsAtBlock_of_consumed
    {n : OddNat} {k i : ℕ}
    (hi : i ∈ canonicalOwnedConsumedClaimsAtBlock n k) :
    i ∈ canonicalOwnedAvailableClaimsAtBlock n k :=
  (Finset.mem_sdiff.mp hi).1

/-- A consumed identity cannot occur in any later available carrier. -/
theorem not_mem_canonicalOwnedAvailableClaimsAtBlock_of_consumed
    {n : OddNat} {k m i : ℕ}
    (hi : i ∈ canonicalOwnedConsumedClaimsAtBlock n k)
    (hkm : k < m) :
    i ∉ canonicalOwnedAvailableClaimsAtBlock n m := by
  intro hiLater
  rcases Finset.mem_union.mp hiLater with hiOld | hiNew
  · exact not_mem_canonicalOwnedOutstandingClaimsBeforeBlock_of_consumed
      hi hkm hiOld
  · have hiLt := mem_canonicalOwnedConsumedClaimsAtBlock_lt_next_start hi
    have hstart := canonicalBlockStartTime_mono n
      (show k + 1 ≤ m by omega)
    have hiGe := (Finset.mem_Ico.mp
      (mem_canonicalBlockClaimSourceCarrier_interval hiNew)).1
    omega

/-- Consumed carriers belonging to different blocks are disjoint. -/
theorem disjoint_canonicalOwnedConsumedClaimsAtBlock
    {n : OddNat} {j k : ℕ} (hjk : j ≠ k) :
    Disjoint (canonicalOwnedConsumedClaimsAtBlock n j)
      (canonicalOwnedConsumedClaimsAtBlock n k) := by
  wlog hjkOrder : j < k generalizing j k
  · exact (this (Ne.symm hjk) (by omega)).symm
  apply Finset.disjoint_left.mpr
  intro i hij hik
  exact not_mem_canonicalOwnedAvailableClaimsAtBlock_of_consumed
    hij hjkOrder (mem_canonicalOwnedAvailableClaimsAtBlock_of_consumed hik)

/-- A consumed source cannot be consumed again at a later block. -/
theorem not_mem_canonicalOwnedConsumedClaimsAtBlock_of_consumed
    {n : OddNat} {j k i : ℕ}
    (hi : i ∈ canonicalOwnedConsumedClaimsAtBlock n j)
    (hjk : j < k) :
    i ∉ canonicalOwnedConsumedClaimsAtBlock n k := by
  exact fun hik => (Finset.disjoint_left.mp
    (disjoint_canonicalOwnedConsumedClaimsAtBlock (by omega))) hi hik

/-- The previous cumulative consumed carrier is disjoint from the next block's
consumed carrier. -/
theorem disjoint_canonicalOwnedCumulativeConsumedClaimsBeforeBlock_consumed
    (n : OddNat) (m : ℕ) :
    Disjoint (canonicalOwnedCumulativeConsumedClaimsBeforeBlock n m)
      (canonicalOwnedConsumedClaimsAtBlock n m) := by
  apply Finset.disjoint_left.mpr
  intro i hiCum hiNow
  rcases mem_canonicalOwnedCumulativeConsumedClaimsBeforeBlock_iff.mp hiCum with
    ⟨k, hkm, hiK⟩
  exact not_mem_canonicalOwnedConsumedClaimsAtBlock_of_consumed hiK hkm hiNow

/-- The cumulative source carrier realizes the cumulative scalar consumption. -/
theorem card_canonicalOwnedCumulativeConsumedClaimsBeforeBlock
    (n : OddNat) (m : ℕ) :
    (canonicalOwnedCumulativeConsumedClaimsBeforeBlock n m).card =
      canonicalCumulativeConsumedCountBeforeBlock n m := by
  induction m with
  | zero => simp [canonicalCumulativeConsumedCountBeforeBlock]
  | succ m ih =>
      rw [canonicalOwnedCumulativeConsumedClaimsBeforeBlock_succ,
        Finset.card_union_of_disjoint
          (disjoint_canonicalOwnedCumulativeConsumedClaimsBeforeBlock_consumed n m),
        ih, card_canonicalOwnedConsumedClaimsAtBlock]
      change (∑ k ∈ Finset.range m, canonicalQueueConsumed n k) +
          canonicalQueueConsumed n m =
        ∑ k ∈ Finset.range (m + 1), canonicalQueueConsumed n k
      rw [Finset.sum_range_succ]

/-- Historical claims split when one complete canonical block is appended. -/
theorem canonicalHistoricalClaimSourceCarrier_succ
    (n : OddNat) (m : ℕ) :
    canonicalHistoricalClaimSourceCarrier n (m + 1) =
      canonicalHistoricalClaimSourceCarrier n m ∪
        canonicalBlockClaimSourceCarrier n m := by
  ext i
  simp only [canonicalHistoricalClaimSourceCarrier,
    canonicalBlockClaimSourceCarrier, mem_carryTwoPositions_iff,
    Finset.mem_union, Finset.mem_Ico]
  constructor
  · rintro ⟨⟨_, hiTop⟩, hiCarry⟩
    by_cases hiOld : i < canonicalBlockStartTime n m
    · exact Or.inl ⟨⟨by omega, hiOld⟩, hiCarry⟩
    · exact Or.inr ⟨⟨by omega, hiTop⟩, hiCarry⟩
  · rintro (⟨⟨_, hiTop⟩, hiCarry⟩ | ⟨⟨_, hiTop⟩, hiCarry⟩)
    · have hmono : canonicalBlockStartTime n m ≤
          canonicalBlockStartTime n (m + 1) :=
        canonicalBlockStartTime_mono n (by omega)
      exact ⟨⟨by omega, by omega⟩, hiCarry⟩
    · exact ⟨⟨by omega, hiTop⟩, hiCarry⟩

/-- Exact source-identity partition of historical claims into consumed and
currently outstanding claims. -/
theorem canonicalHistoricalClaimSourceCarrier_eq_consumed_union_outstanding
    (n : OddNat) (m : ℕ) :
    canonicalHistoricalClaimSourceCarrier n m =
      canonicalOwnedCumulativeConsumedClaimsBeforeBlock n m ∪
        canonicalOwnedOutstandingClaimsBeforeBlock n m := by
  induction m with
  | zero =>
      simp [canonicalHistoricalClaimSourceCarrier, canonicalBlockStartTime,
        canonicalEndpointBlockStart, carryTwoPositions]
  | succ m ih =>
      rw [canonicalHistoricalClaimSourceCarrier_succ, ih,
        Finset.union_assoc,
        ← canonicalOwnedAvailableClaimsAtBlock,
        ← canonicalOwnedConsumed_union_nextOutstanding,
        ← Finset.union_assoc]
      rfl

/-- Cumulative consumed and outstanding identities are disjoint. -/
theorem disjoint_canonicalOwnedCumulativeConsumedClaimsBeforeBlock_outstanding
    (n : OddNat) (m : ℕ) :
    Disjoint (canonicalOwnedCumulativeConsumedClaimsBeforeBlock n m)
      (canonicalOwnedOutstandingClaimsBeforeBlock n m) := by
  apply Finset.disjoint_left.mpr
  intro i hiCum hiOut
  rcases mem_canonicalOwnedCumulativeConsumedClaimsBeforeBlock_iff.mp hiCum with
    ⟨k, hkm, hiConsumed⟩
  exact not_mem_canonicalOwnedOutstandingClaimsBeforeBlock_of_consumed
    hiConsumed hkm hiOut

/-- Exact cardinal form of the historical source partition. -/
theorem card_canonicalHistoricalClaimSourceCarrier
    (n : OddNat) (m : ℕ) :
    (canonicalHistoricalClaimSourceCarrier n m).card =
      canonicalCumulativeConsumedCountBeforeBlock n m +
        canonicalOutstandingClaimQueueBeforeBlock n m := by
  rw [canonicalHistoricalClaimSourceCarrier_eq_consumed_union_outstanding,
    Finset.card_union_of_disjoint
      (disjoint_canonicalOwnedCumulativeConsumedClaimsBeforeBlock_outstanding n m),
    card_canonicalOwnedCumulativeConsumedClaimsBeforeBlock,
    card_canonicalOwnedOutstandingClaimsBeforeBlock]

/-- The carrier partition is the source-bearing form of the existing scalar
prefix balance. -/
theorem card_canonicalHistoricalClaimSourceCarrier_eq_sum_demand
    (n : OddNat) (m : ℕ) :
    (canonicalHistoricalClaimSourceCarrier n m).card =
      ∑ k ∈ Finset.range m, canonicalQueueDemand n k := by
  exact (sum_canonicalQueueDemand_range_eq_sourceClaims_card n m).symm

/-- Every historical source lies before the observation block. -/
theorem mem_canonicalHistoricalClaimSourceCarrier_lt_start
    {n : OddNat} {m i : ℕ}
    (hi : i ∈ canonicalHistoricalClaimSourceCarrier n m) :
    i < canonicalBlockStartTime n m :=
  (Finset.mem_Ico.mp (mem_carryTwoPositions_iff.mp hi).1).2

/-- Global FIFO ordering: every consumed historical source is no later than
every source still outstanding. -/
theorem canonicalOwnedCumulativeConsumed_le_outstanding
    (n : OddNat) (m : ℕ) :
    ∀ x ∈ canonicalOwnedCumulativeConsumedClaimsBeforeBlock n m,
      ∀ y ∈ canonicalOwnedOutstandingClaimsBeforeBlock n m, x ≤ y := by
  induction m with
  | zero => simp
  | succ m ih =>
      intro x hx y hy
      rcases Finset.mem_union.mp hx with hxOld | hxNow
      · have hyAvail := mem_of_mem_eraseOldestN hy
        rcases Finset.mem_union.mp hyAvail with hyOld | hyNew
        · exact ih x hxOld y hyOld
        · have hxHist : x ∈ canonicalHistoricalClaimSourceCarrier n m := by
            rw [canonicalHistoricalClaimSourceCarrier_eq_consumed_union_outstanding]
            exact Finset.mem_union_left _ hxOld
          have hxLt := mem_canonicalHistoricalClaimSourceCarrier_lt_start hxHist
          have hyGe := (Finset.mem_Ico.mp
            (mem_canonicalBlockClaimSourceCarrier_interval hyNew)).1
          omega
      · exact consumedOldestN_le_eraseOldestN
          (canonicalQueueService n m)
          (canonicalOwnedAvailableClaimsAtBlock n m) x hxNow y hy

/-- The recursive owned queue is globally the newest upper tail of all
historical source identities after cumulative *actual* consumption. -/
theorem canonicalOwnedOutstandingClaimsBeforeBlock_eq_eraseOldestN_historical
    (n : OddNat) (m : ℕ) :
    canonicalOwnedOutstandingClaimsBeforeBlock n m =
      eraseOldestN (canonicalCumulativeConsumedCountBeforeBlock n m)
        (canonicalHistoricalClaimSourceCarrier n m) := by
  symm
  apply eraseOldestN_eq_of_subset_card_and_complement_le
  · intro i hi
    rw [canonicalHistoricalClaimSourceCarrier_eq_consumed_union_outstanding]
    exact Finset.mem_union_right _ hi
  · rw [card_eraseOldestN,
      card_canonicalOwnedOutstandingClaimsBeforeBlock,
      card_canonicalHistoricalClaimSourceCarrier]
    omega
  · intro x hx y hy
    have hxHist := (Finset.mem_sdiff.mp hx).1
    have hxNot := (Finset.mem_sdiff.mp hx).2
    rw [canonicalHistoricalClaimSourceCarrier_eq_consumed_union_outstanding] at hxHist
    rcases Finset.mem_union.mp hxHist with hxConsumed | hxOutstanding
    · exact canonicalOwnedCumulativeConsumed_le_outstanding n m x hxConsumed y hy
    · exact False.elim (hxNot hxOutstanding)

/-! ## Exact age and cardinality normal forms -/

/-- Recent claims are exactly the cutoff-filtered part of the historical
carrier. -/
theorem canonicalRecentSourceClaimCarrier_eq_historical_filter
    (n : OddNat) (H m : ℕ) :
    canonicalRecentSourceClaimCarrier n H m =
      (canonicalHistoricalClaimSourceCarrier n m).filter
        (fun i => canonicalBlockStartTime n m - H ≤ i) := by
  ext i
  simp only [canonicalRecentSourceClaimCarrier,
    canonicalHistoricalClaimSourceCarrier, mem_carryTwoPositions_iff,
    Finset.mem_Ico, Finset.mem_filter]
  constructor
  · rintro ⟨⟨hiLow, hiTop⟩, hiCarry⟩
    exact ⟨⟨⟨by omega, hiTop⟩, hiCarry⟩, hiLow⟩
  · rintro ⟨⟨⟨_, hiTop⟩, hiCarry⟩, hiLow⟩
    exact ⟨⟨hiLow, hiTop⟩, hiCarry⟩

/-- At one block, a FIFO age bound is equivalent to inclusion in the recent
source carrier. -/
theorem owned_sourceAgeAtMost_iff_subset_recentCarrier
    (n : OddNat) (H m : ℕ) :
    (∀ i, i ∈ canonicalOwnedOutstandingClaimsBeforeBlock n m →
        canonicalBlockStartTime n m - i ≤ H) ↔
      canonicalOwnedOutstandingClaimsBeforeBlock n m ⊆
        canonicalRecentSourceClaimCarrier n H m := by
  constructor
  · intro h i hi
    rw [canonicalRecentSourceClaimCarrier, mem_carryTwoPositions_iff]
    have hiTop := mem_canonicalOwnedOutstandingClaimsBeforeBlock_lt_start hi
    have hiAge := h i hi
    have hiCarry :=
      carryTwoDebtAt_of_mem_canonicalOwnedOutstandingClaimsBeforeBlock hi
    exact ⟨Finset.mem_Ico.mpr ⟨by omega, hiTop⟩, hiCarry⟩
  · intro h i hi
    have hiRecent := mem_carryTwoPositions_iff.mp (h hi)
    have hiLow := (Finset.mem_Ico.mp hiRecent.1).1
    omega

/-- For the actual FIFO queue, scalar recent-source cardinal coverage is
equivalent to genuine uniform source age. -/
theorem canonicalOwnedOutstandingClaimsHaveSourceAgeAtMost_iff_cardCovered
    (n : OddNat) (H : ℕ) :
    CanonicalOwnedOutstandingClaimsHaveSourceAgeAtMost n H ↔
      CanonicalOutstandingQueueCardCoveredByRecentSourceClaims n H := by
  constructor
  · exact
      CanonicalOwnedOutstandingClaimsHaveSourceAgeAtMost.to_cardCovered
  · intro h m
    rw [owned_sourceAgeAtMost_iff_subset_recentCarrier]
    rw [canonicalOwnedOutstandingClaimsBeforeBlock_eq_eraseOldestN_historical,
      canonicalRecentSourceClaimCarrier_eq_historical_filter]
    apply (eraseOldestN_subset_filter_iff_card_le _ _ _).2
    rw [← canonicalRecentSourceClaimCarrier_eq_historical_filter,
      ← canonicalOwnedOutstandingClaimsBeforeBlock_eq_eraseOldestN_historical,
      card_canonicalOwnedOutstandingClaimsBeforeBlock]
    exact h m

/-- Carry-two sources older than the horizon cutoff at block `m`. -/
noncomputable def canonicalOldSourceClaimCarrier
    (n : OddNat) (H m : ℕ) : Finset ℕ :=
  carryTwoPositions n
    (Finset.Ico 0 (canonicalBlockStartTime n m - H))

/-- Old and recent carriers partition the complete historical carrier. -/
theorem canonicalHistoricalClaimSourceCarrier_eq_old_union_recent
    (n : OddNat) (H m : ℕ) :
    canonicalHistoricalClaimSourceCarrier n m =
      canonicalOldSourceClaimCarrier n H m ∪
        canonicalRecentSourceClaimCarrier n H m := by
  ext i
  simp only [canonicalHistoricalClaimSourceCarrier,
    canonicalOldSourceClaimCarrier, canonicalRecentSourceClaimCarrier,
    mem_carryTwoPositions_iff, Finset.mem_Ico, Finset.mem_union]
  constructor
  · rintro ⟨⟨_, hiTop⟩, hiCarry⟩
    by_cases hiOld : i < canonicalBlockStartTime n m - H
    · exact Or.inl ⟨⟨by omega, hiOld⟩, hiCarry⟩
    · exact Or.inr ⟨⟨by omega, hiTop⟩, hiCarry⟩
  · rintro (⟨⟨_, hiTop⟩, hiCarry⟩ | ⟨⟨_, hiTop⟩, hiCarry⟩)
    · exact ⟨⟨by omega, by omega⟩, hiCarry⟩
    · exact ⟨⟨by omega, hiTop⟩, hiCarry⟩

/-- The old and recent source intervals are disjoint. -/
theorem disjoint_canonicalOldSourceClaimCarrier_recent
    (n : OddNat) (H m : ℕ) :
    Disjoint (canonicalOldSourceClaimCarrier n H m)
      (canonicalRecentSourceClaimCarrier n H m) := by
  apply Finset.disjoint_left.mpr
  intro i hiOld hiRecent
  have hOld := Finset.mem_Ico.mp (mem_carryTwoPositions_iff.mp hiOld).1
  have hRecent := Finset.mem_Ico.mp (mem_carryTwoPositions_iff.mp hiRecent).1
  omega

/-- Exact signed deficit identity comparing old source mass with cumulative
consumption, and outstanding mass with recent sources. -/
theorem canonicalOldSourceClaim_card_sub_cumulativeConsumed_eq_queue_sub_recent
    (n : OddNat) (H m : ℕ) :
    ((canonicalOldSourceClaimCarrier n H m).card : ℤ) -
        canonicalCumulativeConsumedCountBeforeBlock n m =
      canonicalOutstandingClaimQueueBeforeBlock n m -
        (canonicalRecentSourceClaimCarrier n H m).card := by
  have hOldRecent :
      (canonicalHistoricalClaimSourceCarrier n m).card =
        (canonicalOldSourceClaimCarrier n H m).card +
          (canonicalRecentSourceClaimCarrier n H m).card := by
    rw [canonicalHistoricalClaimSourceCarrier_eq_old_union_recent,
      Finset.card_union_of_disjoint
        (disjoint_canonicalOldSourceClaimCarrier_recent n H m)]
  have hConsumed := card_canonicalHistoricalClaimSourceCarrier n m
  have hEq :
      ((canonicalOldSourceClaimCarrier n H m).card : ℤ) +
          (canonicalRecentSourceClaimCarrier n H m).card =
        canonicalCumulativeConsumedCountBeforeBlock n m +
          canonicalOutstandingClaimQueueBeforeBlock n m := by
    exact_mod_cast (show
      (canonicalOldSourceClaimCarrier n H m).card +
          (canonicalRecentSourceClaimCarrier n H m).card =
        canonicalCumulativeConsumedCountBeforeBlock n m +
          canonicalOutstandingClaimQueueBeforeBlock n m by omega)
  omega

/-- The signed source-age deficit at block `m`. -/
noncomputable def canonicalSourceAgeDeficit
    (n : OddNat) (H m : ℕ) : ℤ :=
  ((canonicalOldSourceClaimCarrier n H m).card : ℤ) -
    canonicalCumulativeConsumedCountBeforeBlock n m

/-- At one block, actual FIFO age is bounded exactly when the old-source
deficit is nonpositive. -/
theorem owned_sourceAgeAtMost_iff_sourceAgeDeficit_nonpos
    (n : OddNat) (H m : ℕ) :
    (∀ i, i ∈ canonicalOwnedOutstandingClaimsBeforeBlock n m →
        canonicalBlockStartTime n m - i ≤ H) ↔
      canonicalSourceAgeDeficit n H m ≤ 0 := by
  rw [owned_sourceAgeAtMost_iff_subset_recentCarrier]
  constructor
  · intro hsub
    have hcard := Finset.card_le_card hsub
    unfold canonicalSourceAgeDeficit
    rw [canonicalOldSourceClaim_card_sub_cumulativeConsumed_eq_queue_sub_recent]
    rw [card_canonicalOwnedOutstandingClaimsBeforeBlock] at hcard
    omega
  · intro hdef
    rw [canonicalOwnedOutstandingClaimsBeforeBlock_eq_eraseOldestN_historical,
      canonicalRecentSourceClaimCarrier_eq_historical_filter]
    apply (eraseOldestN_subset_filter_iff_card_le _ _ _).2
    rw [← canonicalRecentSourceClaimCarrier_eq_historical_filter,
      ← canonicalOwnedOutstandingClaimsBeforeBlock_eq_eraseOldestN_historical,
      card_canonicalOwnedOutstandingClaimsBeforeBlock]
    unfold canonicalSourceAgeDeficit at hdef
    rw [canonicalOldSourceClaim_card_sub_cumulativeConsumed_eq_queue_sub_recent]
      at hdef
    omega

/-- Uniform source age is exactly uniform nonpositivity of the scalar deficit. -/
theorem canonicalOwnedOutstandingClaimsHaveSourceAgeAtMost_iff_deficit_nonpos
    (n : OddNat) (H : ℕ) :
    CanonicalOwnedOutstandingClaimsHaveSourceAgeAtMost n H ↔
      ∀ m, canonicalSourceAgeDeficit n H m ≤ 0 := by
  constructor
  · intro h m
    exact (owned_sourceAgeAtMost_iff_sourceAgeDeficit_nonpos n H m).mp (h m)
  · intro h m
    exact (owned_sourceAgeAtMost_iff_sourceAgeDeficit_nonpos n H m).mpr (h m)

/-! ## Oldest source, maximum age, and policy optimality -/

/-- Oldest retained source, with explicit value zero for an empty queue. -/
noncomputable def canonicalOldestOutstandingSource
    (n : OddNat) (m : ℕ) : ℕ :=
  if h : (canonicalOwnedOutstandingClaimsBeforeBlock n m).Nonempty then
    (canonicalOwnedOutstandingClaimsBeforeBlock n m).min' h
  else
    0

/-- Maximum retained source age, explicitly zero for an empty queue. -/
noncomputable def canonicalOwnedMaximumSourceAge
    (n : OddNat) (m : ℕ) : ℕ :=
  if h : (canonicalOwnedOutstandingClaimsBeforeBlock n m).Nonempty then
    canonicalBlockStartTime n m -
      (canonicalOwnedOutstandingClaimsBeforeBlock n m).min' h
  else
    0

@[simp] theorem canonicalOwnedMaximumSourceAge_eq_zero_of_empty
    {n : OddNat} {m : ℕ}
    (h : canonicalOwnedOutstandingClaimsBeforeBlock n m = ∅) :
    canonicalOwnedMaximumSourceAge n m = 0 := by
  simp [canonicalOwnedMaximumSourceAge, h]

/-- The maximum-age scalar exactly characterizes uniform actual source age. -/
theorem canonicalOwnedOutstandingClaimsHaveSourceAgeAtMost_iff_maximumAge_le
    (n : OddNat) (H : ℕ) :
    CanonicalOwnedOutstandingClaimsHaveSourceAgeAtMost n H ↔
      ∀ m, canonicalOwnedMaximumSourceAge n m ≤ H := by
  constructor
  · intro h m
    by_cases hne :
        (canonicalOwnedOutstandingClaimsBeforeBlock n m).Nonempty
    · rw [canonicalOwnedMaximumSourceAge, dif_pos hne]
      exact h m _ (Finset.min'_mem _ hne)
    · simp [canonicalOwnedMaximumSourceAge, hne]
  · intro h m i hi
    have hne : (canonicalOwnedOutstandingClaimsBeforeBlock n m).Nonempty :=
      ⟨i, hi⟩
    have hmax := h m
    rw [canonicalOwnedMaximumSourceAge, dif_pos hne] at hmax
    have hmin := Finset.min'_le
      (canonicalOwnedOutstandingClaimsBeforeBlock n m) i hi
    exact (Nat.sub_le_sub_left hmin _).trans hmax

/-- Any source assignment realizing the same scalar queue at block `m`. -/
def CanonicalAdmissibleOwnedRemainder
    (n : OddNat) (m : ℕ) (u : Finset ℕ) : Prop :=
  u ⊆ canonicalHistoricalClaimSourceCarrier n m ∧
    u.card = canonicalOutstandingClaimQueueBeforeBlock n m

/-- FIFO maximizes the oldest retained source among every assignment realizing
the same scalar queue. -/
theorem canonicalOldestOutstandingSource_maximal
    {n : OddNat} {m : ℕ} {u : Finset ℕ}
    (hu : CanonicalAdmissibleOwnedRemainder n m u)
    (huNonempty : u.Nonempty)
    (hfifoNonempty :
      (canonicalOwnedOutstandingClaimsBeforeBlock n m).Nonempty) :
    u.min' huNonempty ≤
      (canonicalOwnedOutstandingClaimsBeforeBlock n m).min' hfifoNonempty := by
  let y := (canonicalOwnedOutstandingClaimsBeforeBlock n m).min' hfifoNonempty
  have hy : y ∈ canonicalOwnedOutstandingClaimsBeforeBlock n m :=
    Finset.min'_mem _ hfifoNonempty
  change u.min' huNonempty ≤ y
  rw [canonicalOwnedOutstandingClaimsBeforeBlock_eq_eraseOldestN_historical]
    at hy
  have hcard : u.card =
      (eraseOldestN (canonicalCumulativeConsumedCountBeforeBlock n m)
        (canonicalHistoricalClaimSourceCarrier n m)).card := by
    rw [hu.2, ← card_canonicalOwnedOutstandingClaimsBeforeBlock,
      canonicalOwnedOutstandingClaimsBeforeBlock_eq_eraseOldestN_historical]
  rcases exists_le_of_card_eq_card_eraseOldestN hu.1 hcard hy with
    ⟨x, hxU, hxy⟩
  exact (Finset.min'_le u x hxU).trans hxy

/-! ## Eventual consumption under a uniform age hypothesis -/

/-- Once the observation time exceeds `i + H`, an age-`H` source cannot remain
outstanding. -/
theorem not_mem_ownedQueue_of_sourceAgeAtMost_of_time_gt
    {n : OddNat} {H m i : ℕ}
    (h : CanonicalOwnedOutstandingClaimsHaveSourceAgeAtMost n H)
    (htime : i + H < canonicalBlockStartTime n m) :
    i ∉ canonicalOwnedOutstandingClaimsBeforeBlock n m := by
  intro hi
  have hage := h m i hi
  have hiTop := mem_canonicalOwnedOutstandingClaimsBeforeBlock_lt_start hi
  omega

/-- Advancing `L` canonical blocks advances source time by at least `L`. -/
theorem canonicalBlockStartTime_add_le_startTime_add
    (n : OddNat) (k L : ℕ) :
    canonicalBlockStartTime n k + L ≤
      canonicalBlockStartTime n (k + L) := by
  induction L with
  | zero => simp
  | succ L ih =>
      rw [show k + (L + 1) = (k + L) + 1 by omega,
        canonicalBlockStartTime_succ]
      have hlen := one_le_canonicalBlockLength n (k + L)
      omega

/-- Every source born in block `k` is consumed by some block strictly before
`k + H + 2`, assuming the uniform actual source-age bound `H`. -/
theorem exists_consumptionBlock_before_add_of_sourceAgeAtMost
    {n : OddNat} {H k i : ℕ}
    (h : CanonicalOwnedOutstandingClaimsHaveSourceAgeAtMost n H)
    (hi : i ∈ canonicalBlockClaimSourceCarrier n k) :
    ∃ j < k + H + 2, i ∈ canonicalOwnedConsumedClaimsAtBlock n j := by
  let m := k + H + 2
  have hiInterval := Finset.mem_Ico.mp
    (mem_canonicalBlockClaimSourceCarrier_interval hi)
  have hiCarry := carryTwoDebtAt_of_mem_canonicalBlockClaimSourceCarrier hi
  have hadvance := canonicalBlockStartTime_add_le_startTime_add n (k + 1) (H + 1)
  have hmEq : (k + 1) + (H + 1) = m := by simp [m]; omega
  rw [hmEq] at hadvance
  have htime : i + H < canonicalBlockStartTime n m := by omega
  have hiHist : i ∈ canonicalHistoricalClaimSourceCarrier n m := by
    rw [canonicalHistoricalClaimSourceCarrier, mem_carryTwoPositions_iff]
    exact ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, hiCarry⟩
  have hiNot := not_mem_ownedQueue_of_sourceAgeAtMost_of_time_gt h htime
  rw [canonicalHistoricalClaimSourceCarrier_eq_consumed_union_outstanding]
    at hiHist
  rcases Finset.mem_union.mp hiHist with hiConsumed | hiOutstanding
  · rcases mem_canonicalOwnedCumulativeConsumedClaimsBeforeBlock_iff.mp
      hiConsumed with ⟨j, hjm, hij⟩
    exact ⟨j, by simpa [m] using hjm, hij⟩
  · exact False.elim (hiNot hiOutstanding)

end DkMath.Collatz
