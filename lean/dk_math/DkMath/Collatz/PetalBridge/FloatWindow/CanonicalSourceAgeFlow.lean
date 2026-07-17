/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalOwnedQueueGlobal
import DkMath.Collatz.PetalBridge.FloatWindow.FiniteSignedTransition
import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentSaturatedSuccessor

#print "file: DkMath.Collatz.PetalBridge.FloatWindow.CanonicalSourceAgeFlow"

namespace DkMath.Collatz

/-!
# Canonical source-age signed flow

The global FIFO normal form identifies the outstanding queue as a newest
historical upper tail.  This module moves the age cutoff one canonical block at
a time.  Claims crossing that cutoff are signed arrivals at the age frontier;
actual FIFO consumption is signed service.  Negative credit is retained in
`Int` and is never truncated by a reflected recurrence.
-/

/-! ## Expired outstanding claims -/

/-- Actual outstanding identities lying strictly below the age-`H` cutoff. -/
noncomputable def canonicalExpiredOutstandingClaims
    (n : OddNat) (H m : ℕ) : Finset ℕ :=
  canonicalOwnedOutstandingClaimsBeforeBlock n m ∩
    canonicalOldSourceClaimCarrier n H m

/-- An expired identity is an actual outstanding carry-two source. -/
theorem canonicalExpiredOutstandingClaims_subset_outstanding
    (n : OddNat) (H m : ℕ) :
    canonicalExpiredOutstandingClaims n H m ⊆
      canonicalOwnedOutstandingClaimsBeforeBlock n m := by
  exact Finset.inter_subset_left

theorem carryTwoDebtAt_of_mem_canonicalExpiredOutstandingClaims
    {n : OddNat} {H m i : ℕ}
    (hi : i ∈ canonicalExpiredOutstandingClaims n H m) :
    CarryTwoDebtAt n i :=
  carryTwoDebtAt_of_mem_canonicalOwnedOutstandingClaimsBeforeBlock
    (canonicalExpiredOutstandingClaims_subset_outstanding n H m hi)

/-- Expiration is exactly outstanding membership with actual source age
strictly greater than the horizon. -/
theorem mem_canonicalExpiredOutstandingClaims_iff
    {n : OddNat} {H m i : ℕ} :
    i ∈ canonicalExpiredOutstandingClaims n H m ↔
      i ∈ canonicalOwnedOutstandingClaimsBeforeBlock n m ∧
        H < canonicalBlockStartTime n m - i := by
  constructor
  · intro hi
    rcases Finset.mem_inter.mp hi with ⟨hiOut, hiOld⟩
    have hiCutoff := (Finset.mem_Ico.mp
      (mem_carryTwoPositions_iff.mp hiOld).1).2
    have hiTop := mem_canonicalOwnedOutstandingClaimsBeforeBlock_lt_start hiOut
    exact ⟨hiOut, by omega⟩
  · rintro ⟨hiOut, hiAge⟩
    apply Finset.mem_inter.mpr
    refine ⟨hiOut, ?_⟩
    rw [canonicalOldSourceClaimCarrier, mem_carryTwoPositions_iff]
    have hiTop := mem_canonicalOwnedOutstandingClaimsBeforeBlock_lt_start hiOut
    exact ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩,
      carryTwoDebtAt_of_mem_canonicalOwnedOutstandingClaimsBeforeBlock hiOut⟩

/-- The expired carrier is empty exactly when the block-local actual age bound
holds for every retained source. -/
theorem canonicalExpiredOutstandingClaims_eq_empty_iff
    (n : OddNat) (H m : ℕ) :
    canonicalExpiredOutstandingClaims n H m = ∅ ↔
      ∀ i, i ∈ canonicalOwnedOutstandingClaimsBeforeBlock n m →
        canonicalBlockStartTime n m - i ≤ H := by
  constructor
  · intro hempty i hi
    by_contra hage
    have hiExpired : i ∈ canonicalExpiredOutstandingClaims n H m :=
      mem_canonicalExpiredOutstandingClaims_iff.mpr ⟨hi, by omega⟩
    rw [hempty] at hiExpired
    simp at hiExpired
  · intro h
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨i, hi⟩
    have hiData := mem_canonicalExpiredOutstandingClaims_iff.mp hi
    exact (Nat.not_lt_of_ge (h i hiData.1)) hiData.2

/-! ## Moving age horizon -/

/-- Carry-two claims crossing the moving source-age cutoff during block `m`. -/
noncomputable def canonicalSourceAgeHorizonCrossingClaims
    (n : OddNat) (H m : ℕ) : Finset ℕ :=
  carryTwoPositions n
    (Finset.Ico
      (canonicalBlockStartTime n m - H)
      (canonicalBlockStartTime n (m + 1) - H))

/-- Moving the cutoff by one canonical block appends exactly the horizon
crossing carrier, including the Nat-subtraction early regime. -/
theorem canonicalOldSourceClaimCarrier_succ
    (n : OddNat) (H m : ℕ) :
    canonicalOldSourceClaimCarrier n H (m + 1) =
      canonicalOldSourceClaimCarrier n H m ∪
        canonicalSourceAgeHorizonCrossingClaims n H m := by
  ext i
  simp only [canonicalOldSourceClaimCarrier,
    canonicalSourceAgeHorizonCrossingClaims, mem_carryTwoPositions_iff,
    Finset.mem_Ico, Finset.mem_union]
  constructor
  · rintro ⟨⟨_, hiTop⟩, hiCarry⟩
    by_cases hiOld : i < canonicalBlockStartTime n m - H
    · exact Or.inl ⟨⟨by omega, hiOld⟩, hiCarry⟩
    · exact Or.inr ⟨⟨by omega, hiTop⟩, hiCarry⟩
  · rintro (⟨⟨_, hiTop⟩, hiCarry⟩ | ⟨⟨_, hiTop⟩, hiCarry⟩)
    · have hmono := canonicalBlockStartTime_mono n
        (show m ≤ m + 1 by omega)
      exact ⟨⟨by omega, by omega⟩, hiCarry⟩
    · exact ⟨⟨by omega, hiTop⟩, hiCarry⟩

/-- The previous old carrier and the newly crossing interval are disjoint. -/
theorem disjoint_canonicalOldSourceClaimCarrier_horizonCrossing
    (n : OddNat) (H m : ℕ) :
    Disjoint (canonicalOldSourceClaimCarrier n H m)
      (canonicalSourceAgeHorizonCrossingClaims n H m) := by
  apply Finset.disjoint_left.mpr
  intro i hiOld hiCross
  have hiOldTop := (Finset.mem_Ico.mp
    (mem_carryTwoPositions_iff.mp hiOld).1).2
  have hiCrossLow := (Finset.mem_Ico.mp
    (mem_carryTwoPositions_iff.mp hiCross).1).1
  omega

/-- Exact cardinal growth of the moving old-source carrier. -/
theorem card_canonicalOldSourceClaimCarrier_succ
    (n : OddNat) (H m : ℕ) :
    (canonicalOldSourceClaimCarrier n H (m + 1)).card =
      (canonicalOldSourceClaimCarrier n H m).card +
        (canonicalSourceAgeHorizonCrossingClaims n H m).card := by
  rw [canonicalOldSourceClaimCarrier_succ,
    Finset.card_union_of_disjoint
      (disjoint_canonicalOldSourceClaimCarrier_horizonCrossing n H m)]

/-! ## Exact signed recurrence -/

/-- Signed one-block age-frontier flow: newly expired source mass minus actual
FIFO consumption. -/
noncomputable def canonicalSourceAgeFrontierIncrement
    (n : OddNat) (H m : ℕ) : ℤ :=
  (canonicalSourceAgeHorizonCrossingClaims n H m).card -
    canonicalQueueConsumed n m

@[simp] theorem canonicalSourceAgeDeficit_zero
    (n : OddNat) (H : ℕ) :
    canonicalSourceAgeDeficit n H 0 = 0 := by
  simp [canonicalSourceAgeDeficit, canonicalOldSourceClaimCarrier,
    canonicalCumulativeConsumedCountBeforeBlock, canonicalBlockStartTime,
    canonicalEndpointBlockStart, carryTwoPositions]

/-- The static deficit evolves by exact signed frontier flow. -/
theorem canonicalSourceAgeDeficit_succ
    (n : OddNat) (H m : ℕ) :
    canonicalSourceAgeDeficit n H (m + 1) =
      canonicalSourceAgeDeficit n H m +
        canonicalSourceAgeFrontierIncrement n H m := by
  unfold canonicalSourceAgeDeficit canonicalSourceAgeFrontierIncrement
  rw [card_canonicalOldSourceClaimCarrier_succ]
  unfold canonicalCumulativeConsumedCountBeforeBlock
  rw [Finset.sum_range_succ]
  push_cast
  ring

/-- Prefix normal form.  Negative age credit is retained in `Int`. -/
theorem canonicalSourceAgeDeficit_eq_sum_frontierIncrement
    (n : OddNat) (H m : ℕ) :
    canonicalSourceAgeDeficit n H m =
      ∑ k ∈ Finset.range m, canonicalSourceAgeFrontierIncrement n H k := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [canonicalSourceAgeDeficit_succ, ih, Finset.sum_range_succ]

/-! ## Exact uniform-age surfaces -/

/-- Uniform actual source age is the nonpositivity of every signed frontier
prefix. -/
theorem canonicalOwnedOutstandingClaimsHaveSourceAgeAtMost_iff_frontierPrefix_nonpos
    (n : OddNat) (H : ℕ) :
    CanonicalOwnedOutstandingClaimsHaveSourceAgeAtMost n H ↔
      ∀ m, (∑ k ∈ Finset.range m,
        canonicalSourceAgeFrontierIncrement n H k) ≤ 0 := by
  rw [canonicalOwnedOutstandingClaimsHaveSourceAgeAtMost_iff_deficit_nonpos]
  constructor <;> intro h m
  · rw [← canonicalSourceAgeDeficit_eq_sum_frontierIncrement]
    exact h m
  · rw [canonicalSourceAgeDeficit_eq_sum_frontierIncrement]
    exact h m

/-- Carrier form of the same uniform age theorem. -/
theorem canonicalOwnedOutstandingClaimsHaveSourceAgeAtMost_iff_expired_empty
    (n : OddNat) (H : ℕ) :
    CanonicalOwnedOutstandingClaimsHaveSourceAgeAtMost n H ↔
      ∀ m, canonicalExpiredOutstandingClaims n H m = ∅ := by
  constructor
  · intro h m
    exact (canonicalExpiredOutstandingClaims_eq_empty_iff n H m).2 (h m)
  · intro h m
    exact (canonicalExpiredOutstandingClaims_eq_empty_iff n H m).1 (h m)

/-! ## Boundary values and horizon monotonicity -/

/-- At horizon zero the old carrier is the complete historical carrier. -/
theorem canonicalOldSourceClaimCarrier_zero_horizon
    (n : OddNat) (m : ℕ) :
    canonicalOldSourceClaimCarrier n 0 m =
      canonicalHistoricalClaimSourceCarrier n m := by
  ext i
  simp [canonicalOldSourceClaimCarrier, canonicalHistoricalClaimSourceCarrier]

/-- At horizon zero the signed source-age deficit is exactly the scalar queue. -/
theorem canonicalSourceAgeDeficit_zero_horizon
    (n : OddNat) (m : ℕ) :
    canonicalSourceAgeDeficit n 0 m =
      canonicalOutstandingClaimQueueBeforeBlock n m := by
  unfold canonicalSourceAgeDeficit
  rw [canonicalOldSourceClaimCarrier_zero_horizon,
    card_canonicalHistoricalClaimSourceCarrier]
  push_cast
  ring

/-- At horizon zero, frontier arrivals are exactly the current block claims. -/
theorem canonicalSourceAgeHorizonCrossingClaims_zero_horizon
    (n : OddNat) (m : ℕ) :
    canonicalSourceAgeHorizonCrossingClaims n 0 m =
      canonicalBlockClaimSourceCarrier n m := by
  ext i
  simp [canonicalSourceAgeHorizonCrossingClaims,
    canonicalBlockClaimSourceCarrier]

/-- Before the horizon reaches block time there are no old source claims. -/
theorem canonicalOldSourceClaimCarrier_eq_empty_of_start_le
    {n : OddNat} {H m : ℕ}
    (hstart : canonicalBlockStartTime n m ≤ H) :
    canonicalOldSourceClaimCarrier n H m = ∅ := by
  rw [canonicalOldSourceClaimCarrier]
  have hcutoff : canonicalBlockStartTime n m - H = 0 :=
    Nat.sub_eq_zero_of_le hstart
  rw [hcutoff]
  ext i
  simp [mem_carryTwoPositions_iff]

theorem canonicalSourceAgeDeficit_nonpos_of_start_le
    {n : OddNat} {H m : ℕ}
    (hstart : canonicalBlockStartTime n m ≤ H) :
    canonicalSourceAgeDeficit n H m ≤ 0 := by
  rw [canonicalSourceAgeDeficit,
    canonicalOldSourceClaimCarrier_eq_empty_of_start_le hstart]
  simp

/-- Enlarging the horizon can only decrease the signed deficit. -/
theorem canonicalSourceAgeDeficit_anti
    (n : OddNat) {H1 H2 m : ℕ} (hH : H1 ≤ H2) :
    canonicalSourceAgeDeficit n H2 m ≤
      canonicalSourceAgeDeficit n H1 m := by
  unfold canonicalSourceAgeDeficit
  have hsub : canonicalOldSourceClaimCarrier n H2 m ⊆
      canonicalOldSourceClaimCarrier n H1 m := by
    intro i hi
    rw [canonicalOldSourceClaimCarrier, mem_carryTwoPositions_iff] at hi ⊢
    exact ⟨Finset.mem_Ico.mpr ⟨by omega,
      by
        have hiTop := (Finset.mem_Ico.mp hi.1).2
        omega⟩, hi.2⟩
  have hcard := Finset.card_le_card hsub
  omega

/-- Enlarging the horizon can only remove expired outstanding identities. -/
theorem canonicalExpiredOutstandingClaims_anti
    (n : OddNat) {H1 H2 m : ℕ} (hH : H1 ≤ H2) :
    canonicalExpiredOutstandingClaims n H2 m ⊆
      canonicalExpiredOutstandingClaims n H1 m := by
  intro i hi
  rw [mem_canonicalExpiredOutstandingClaims_iff] at hi ⊢
  exact ⟨hi.1, by omega⟩

theorem card_canonicalExpiredOutstandingClaims_anti
    (n : OddNat) {H1 H2 m : ℕ} (hH : H1 ≤ H2) :
    (canonicalExpiredOutstandingClaims n H2 m).card ≤
      (canonicalExpiredOutstandingClaims n H1 m).card :=
  Finset.card_le_card (canonicalExpiredOutstandingClaims_anti n hH)

/-! ## Exact residual cases -/

/-- Positive deficit means every cumulatively consumed source still lies below
the current age cutoff. -/
theorem cumulativeConsumed_subset_old_of_sourceAgeDeficit_pos
    {n : OddNat} {H m : ℕ}
    (hpos : 0 < canonicalSourceAgeDeficit n H m) :
    canonicalOwnedCumulativeConsumedClaimsBeforeBlock n m ⊆
      canonicalOldSourceClaimCarrier n H m := by
  have hcard :
      (canonicalOwnedCumulativeConsumedClaimsBeforeBlock n m).card <
        (canonicalOldSourceClaimCarrier n H m).card := by
    rw [card_canonicalOwnedCumulativeConsumedClaimsBeforeBlock]
    unfold canonicalSourceAgeDeficit at hpos
    omega
  have hex : ∃ y, y ∈ canonicalOldSourceClaimCarrier n H m ∧
      y ∉ canonicalOwnedCumulativeConsumedClaimsBeforeBlock n m := by
    by_contra h
    push Not at h
    have hsub : canonicalOldSourceClaimCarrier n H m ⊆
        canonicalOwnedCumulativeConsumedClaimsBeforeBlock n m := by
      intro y hy
      exact h y hy
    have := Finset.card_le_card hsub
    omega
  rcases hex with ⟨y, hyOld, hyNotConsumed⟩
  have hyHist : y ∈ canonicalHistoricalClaimSourceCarrier n m := by
    rw [canonicalHistoricalClaimSourceCarrier_eq_old_union_recent]
    exact Finset.mem_union_left _ hyOld
  rw [canonicalHistoricalClaimSourceCarrier_eq_consumed_union_outstanding]
    at hyHist
  have hyOut : y ∈ canonicalOwnedOutstandingClaimsBeforeBlock n m :=
    (Finset.mem_union.mp hyHist).resolve_left hyNotConsumed
  intro x hx
  have hxy := canonicalOwnedCumulativeConsumed_le_outstanding n m x hx y hyOut
  have hxHist : x ∈ canonicalHistoricalClaimSourceCarrier n m := by
    rw [canonicalHistoricalClaimSourceCarrier_eq_consumed_union_outstanding]
    exact Finset.mem_union_left _ hx
  rw [canonicalOldSourceClaimCarrier, mem_carryTwoPositions_iff] at hyOld ⊢
  exact ⟨Finset.mem_Ico.mpr ⟨by omega,
    by
      have hyTop := (Finset.mem_Ico.mp hyOld.1).2
      omega⟩,
    (mem_carryTwoPositions_iff.mp hxHist).2⟩

/-- Nonpositive deficit means every old source has already been consumed. -/
theorem old_subset_cumulativeConsumed_of_sourceAgeDeficit_nonpos
    {n : OddNat} {H m : ℕ}
    (hnonpos : canonicalSourceAgeDeficit n H m ≤ 0) :
    canonicalOldSourceClaimCarrier n H m ⊆
      canonicalOwnedCumulativeConsumedClaimsBeforeBlock n m := by
  intro y hyOld
  have hyHist : y ∈ canonicalHistoricalClaimSourceCarrier n m := by
    rw [canonicalHistoricalClaimSourceCarrier_eq_old_union_recent]
    exact Finset.mem_union_left _ hyOld
  rw [canonicalHistoricalClaimSourceCarrier_eq_consumed_union_outstanding]
    at hyHist
  rcases Finset.mem_union.mp hyHist with hyConsumed | hyOut
  · exact hyConsumed
  · exfalso
    have hsub : canonicalOwnedCumulativeConsumedClaimsBeforeBlock n m ⊆
        canonicalOldSourceClaimCarrier n H m := by
      intro x hx
      have hxy := canonicalOwnedCumulativeConsumed_le_outstanding
        n m x hx y hyOut
      have hxHist : x ∈ canonicalHistoricalClaimSourceCarrier n m := by
        rw [canonicalHistoricalClaimSourceCarrier_eq_consumed_union_outstanding]
        exact Finset.mem_union_left _ hx
      rw [canonicalOldSourceClaimCarrier, mem_carryTwoPositions_iff] at hyOld ⊢
      exact ⟨Finset.mem_Ico.mpr ⟨by omega,
        by
          have hyTop := (Finset.mem_Ico.mp hyOld.1).2
          omega⟩,
        (mem_carryTwoPositions_iff.mp hxHist).2⟩
    have hyNotConsumed :
        y ∉ canonicalOwnedCumulativeConsumedClaimsBeforeBlock n m :=
      fun hyConsumed =>
        (Finset.disjoint_left.mp
          (disjoint_canonicalOwnedCumulativeConsumedClaimsBeforeBlock_outstanding
            n m) hyConsumed hyOut)
    have hne : canonicalOwnedCumulativeConsumedClaimsBeforeBlock n m ≠
        canonicalOldSourceClaimCarrier n H m := by
      intro heq
      exact hyNotConsumed (by simpa [heq] using hyOld)
    have hstrict : canonicalOwnedCumulativeConsumedClaimsBeforeBlock n m ⊂
        canonicalOldSourceClaimCarrier n H m :=
      (Finset.ssubset_iff_subset_ne).2 ⟨hsub, hne⟩
    have hcard := Finset.card_lt_card hstrict
    rw [card_canonicalOwnedCumulativeConsumedClaimsBeforeBlock] at hcard
    unfold canonicalSourceAgeDeficit at hnonpos
    omega

/-- The positive part of the signed deficit is exactly the number of actual
expired outstanding identities. -/
theorem card_canonicalExpiredOutstandingClaims
    (n : OddNat) (H m : ℕ) :
    (canonicalExpiredOutstandingClaims n H m).card =
      Int.toNat (canonicalSourceAgeDeficit n H m) := by
  by_cases hpos : 0 < canonicalSourceAgeDeficit n H m
  · have hsub := cumulativeConsumed_subset_old_of_sourceAgeDeficit_pos hpos
    have hsplit : canonicalOldSourceClaimCarrier n H m =
        canonicalOwnedCumulativeConsumedClaimsBeforeBlock n m ∪
          canonicalExpiredOutstandingClaims n H m := by
      ext i
      constructor
      · intro hiOld
        have hiHist : i ∈ canonicalHistoricalClaimSourceCarrier n m := by
          rw [canonicalHistoricalClaimSourceCarrier_eq_old_union_recent]
          exact Finset.mem_union_left _ hiOld
        rw [canonicalHistoricalClaimSourceCarrier_eq_consumed_union_outstanding]
          at hiHist
        rcases Finset.mem_union.mp hiHist with hiConsumed | hiOut
        · exact Finset.mem_union_left _ hiConsumed
        · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hiOut, hiOld⟩)
      · intro hi
        rcases Finset.mem_union.mp hi with hiConsumed | hiExpired
        · exact hsub hiConsumed
        · exact (Finset.mem_inter.mp hiExpired).2
    have hdisjoint : Disjoint
        (canonicalOwnedCumulativeConsumedClaimsBeforeBlock n m)
        (canonicalExpiredOutstandingClaims n H m) := by
      apply Finset.disjoint_left.mpr
      intro i hiConsumed hiExpired
      exact Finset.disjoint_left.mp
        (disjoint_canonicalOwnedCumulativeConsumedClaimsBeforeBlock_outstanding
          n m) hiConsumed (Finset.mem_inter.mp hiExpired).1
    have hcard : (canonicalOldSourceClaimCarrier n H m).card =
        (canonicalOwnedCumulativeConsumedClaimsBeforeBlock n m).card +
          (canonicalExpiredOutstandingClaims n H m).card := by
      rw [hsplit, Finset.card_union_of_disjoint hdisjoint]
    rw [card_canonicalOwnedCumulativeConsumedClaimsBeforeBlock] at hcard
    have htoNat := Int.toNat_of_nonneg (le_of_lt hpos)
    unfold canonicalSourceAgeDeficit at htoNat ⊢
    omega
  · have hnonpos : canonicalSourceAgeDeficit n H m ≤ 0 := by omega
    have hsub := old_subset_cumulativeConsumed_of_sourceAgeDeficit_nonpos hnonpos
    have hempty : canonicalExpiredOutstandingClaims n H m = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      rintro ⟨i, hi⟩
      have hiData := Finset.mem_inter.mp hi
      exact Finset.disjoint_left.mp
        (disjoint_canonicalOwnedCumulativeConsumedClaimsBeforeBlock_outstanding
          n m) (hsub hiData.2) hiData.1
    rw [hempty, Finset.card_empty, Int.toNat_of_nonpos hnonpos]

/-! ## FIFO threshold dominance for canonical assignments -/

/-- FIFO maximizes the number of retained sources above every cutoff among all
same-cardinality assignments of historical claims. -/
theorem canonicalAdmissibleOwnedRemainder_filter_card_le_fifo
    {n : OddNat} {m : ℕ} {u : Finset ℕ}
    (hu : CanonicalAdmissibleOwnedRemainder n m u)
    (t : ℕ) :
    (u.filter (fun i => t ≤ i)).card ≤
      ((canonicalOwnedOutstandingClaimsBeforeBlock n m).filter
        (fun i => t ≤ i)).card := by
  rw [canonicalOwnedOutstandingClaimsBeforeBlock_eq_eraseOldestN_historical]
  apply card_filter_le_card_filter_eraseOldestN hu.1
  rw [hu.2, ← card_canonicalOwnedOutstandingClaimsBeforeBlock,
    canonicalOwnedOutstandingClaimsBeforeBlock_eq_eraseOldestN_historical]

/-! ## Sharpened conditional repayment lag -/

/-- Under a uniform actual age bound, a source born in block `k` is consumed
strictly before block `k + H + 1`. -/
theorem exists_consumptionBlock_before_add_one_of_sourceAgeAtMost
    {n : OddNat} {H k i : ℕ}
    (h : CanonicalOwnedOutstandingClaimsHaveSourceAgeAtMost n H)
    (hi : i ∈ canonicalBlockClaimSourceCarrier n k) :
    ∃ j < k + H + 1, i ∈ canonicalOwnedConsumedClaimsAtBlock n j := by
  let m := k + H + 1
  have hiInterval := Finset.mem_Ico.mp
    (mem_canonicalBlockClaimSourceCarrier_interval hi)
  have hiCarry := carryTwoDebtAt_of_mem_canonicalBlockClaimSourceCarrier hi
  have hadvance := canonicalBlockStartTime_add_le_startTime_add n (k + 1) H
  have hmEq : (k + 1) + H = m := by simp [m]; omega
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

/-! ## Conditional finite signed-transition certificate

This wrapper deliberately receives its finite signature, potential, and
transition proof from outside the source-age deficit.  Defining any of those
objects from `canonicalSourceAgeDeficit` would merely encode the desired prefix
inequality and would therefore be circular.
-/

/-- A structural finite-potential model whose realized successor-edge weight is
the canonical source-age frontier flow at a fixed horizon. -/
structure CanonicalSourceAgeFrontierPotentialCertificate
    (n : OddNat) (H : ℕ) (Signature : Type*) [Fintype Signature] where
  certificate :
    RelationalFiniteSignedTransitionPotentialCertificate ℕ Signature
  step_succ : ∀ m, certificate.Step m (m + 1)
  actualWeight_succ : ∀ m,
    certificate.actualWeight m (m + 1) =
      canonicalSourceAgeFrontierIncrement n H m
  prefixPotentialChange_nonpos : ∀ m,
    certificate.potential (certificate.signature m) -
      certificate.potential (certificate.signature 0) ≤ 0

namespace CanonicalSourceAgeFrontierPotentialCertificate

variable {n : OddNat} {H : ℕ} {Signature : Type*} [Fintype Signature]

/-- A structurally supplied nonpositive potential change makes every realized
frontier prefix nonpositive. -/
theorem frontierPrefix_nonpos
    (F : CanonicalSourceAgeFrontierPotentialCertificate n H Signature)
    (m : ℕ) :
    (∑ k ∈ Finset.range m, canonicalSourceAgeFrontierIncrement n H k) ≤ 0 := by
  have hpath : F.certificate.IsPath (fun i => i) 0 m := by
    intro i hi
    simpa using F.step_succ i
  have hweight :=
    (F.certificate.pathWeight_le_projectedPathWeight (fun i => i) 0 m hpath).trans
      (F.certificate.projectedPathWeight_le_potential_sub (fun i => i) 0 m)
  have hpathWeight : F.certificate.pathWeight (fun i => i) 0 m =
      ∑ k ∈ Finset.range m, canonicalSourceAgeFrontierIncrement n H k := by
    unfold RelationalFiniteSignedTransitionPotentialCertificate.pathWeight
    apply Finset.sum_congr rfl
    intro i hi
    simpa using F.actualWeight_succ i
  rw [hpathWeight] at hweight
  exact hweight.trans (by simpa using F.prefixPotentialChange_nonpos m)

/-- The structural certificate closes the exact uniform actual-age target. -/
theorem to_sourceAgeAtMost
    (F : CanonicalSourceAgeFrontierPotentialCertificate n H Signature) :
    CanonicalOwnedOutstandingClaimsHaveSourceAgeAtMost n H := by
  rw [canonicalOwnedOutstandingClaimsHaveSourceAgeAtMost_iff_frontierPrefix_nonpos]
  exact F.frontierPrefix_nonpos

/-- Conditional challenge-facing closure: a noncircular finite structural
certificate yields both the scalar queue and translated endpoint-width bounds. -/
theorem to_queue_and_endpointWidth_bounds
    (F : CanonicalSourceAgeFrontierPotentialCertificate n H Signature) :
    CanonicalOutstandingClaimQueueUniformUpperBound n H ∧
      CanonicalEndpointWidthUniformUpperBound n (bitWidth n.1 + H) := by
  have hage := F.to_sourceAgeAtMost
  exact ⟨hage.to_queueUniformUpperBound,
    hage.to_endpointWidthUniformUpperBound⟩

end CanonicalSourceAgeFrontierPotentialCertificate

/-! ## Saturated-frontier arithmetic audit -/

/-- At horizon zero a saturated block contributes exactly two crossing
carry-two sources. -/
theorem CanonicalSaturatedBorderBlock.card_sourceAgeHorizonCrossing_zero_eq_two
    {n : OddNat} {m : ℕ} (h : CanonicalSaturatedBorderBlock n m) :
    (canonicalSourceAgeHorizonCrossingClaims n 0 m).card = 2 := by
  rw [canonicalSourceAgeHorizonCrossingClaims_zero_horizon,
    card_canonicalBlockClaimSourceCarrier,
    canonicalQueueDemand]
  rw [h.2.1, h.length_eq_two]

/-- A saturated block consumes exactly its one unit of terminal capacity. -/
theorem CanonicalSaturatedBorderBlock.canonicalQueueConsumed_eq_one
    {n : OddNat} {m : ℕ} (h : CanonicalSaturatedBorderBlock n m) :
    canonicalQueueConsumed n m = 1 := by
  unfold canonicalQueueConsumed canonicalQueueDemand canonicalQueueService
  rw [h.2.1, h.length_eq_two,
    canonicalBlockCapacityCount_eq_terminalValuation,
    h.terminalValuation_eq_one]
  simp

/-- Exact obstruction to a pointwise-nonpositive horizon-zero frontier:
every saturated block has signed frontier increment `+1`.  Consequently a
valid global proof must use a positive horizon or amortize this block against
other blocks; saturation alone cannot prove pointwise nonpositivity. -/
theorem CanonicalSaturatedBorderBlock.sourceAgeFrontierIncrement_zero_eq_one
    {n : OddNat} {m : ℕ} (h : CanonicalSaturatedBorderBlock n m) :
    canonicalSourceAgeFrontierIncrement n 0 m = 1 := by
  unfold canonicalSourceAgeFrontierIncrement
  rw [h.card_sourceAgeHorizonCrossing_zero_eq_two,
    h.canonicalQueueConsumed_eq_one]
  norm_num

end DkMath.Collatz
