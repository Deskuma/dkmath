/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalSourceTimeLag
import DkMath.Collatz.PetalBridge.FloatWindow.OldestFirstQueue

#print "file: DkMath.Collatz.PetalBridge.FloatWindow.CanonicalOwnedQueue"

namespace DkMath.Collatz

/-!
# Canonical source-owned queue

The scalar reflected queue records only a claim count.  This module realizes
that count by a temporally coherent finite set whose elements remain the
original carry-two source times.  Service always removes the oldest available
source identities; no endpoint is independently rematched against history.
-/

/-- Source-bearing outstanding claims immediately before canonical block `k`. -/
noncomputable def canonicalOwnedOutstandingClaimsBeforeBlock
    (n : OddNat) : ℕ → Finset ℕ
  | 0 => ∅
  | k + 1 =>
      eraseOldestN (canonicalQueueService n k)
        (canonicalOwnedOutstandingClaimsBeforeBlock n k ∪
          canonicalBlockClaimSourceCarrier n k)

/-- All source-bearing claims available for service at canonical block `k`. -/
noncomputable def canonicalOwnedAvailableClaimsAtBlock
    (n : OddNat) (k : ℕ) : Finset ℕ :=
  canonicalOwnedOutstandingClaimsBeforeBlock n k ∪
    canonicalBlockClaimSourceCarrier n k

/-- Source identities consumed by oldest-first service at block `k`. -/
noncomputable def canonicalOwnedConsumedClaimsAtBlock
    (n : OddNat) (k : ℕ) : Finset ℕ :=
  consumedOldestN (canonicalQueueService n k)
    (canonicalOwnedAvailableClaimsAtBlock n k)

@[simp] theorem canonicalOwnedOutstandingClaimsBeforeBlock_zero
    (n : OddNat) :
    canonicalOwnedOutstandingClaimsBeforeBlock n 0 = ∅ := rfl

@[simp] theorem canonicalOwnedOutstandingClaimsBeforeBlock_succ
    (n : OddNat) (k : ℕ) :
    canonicalOwnedOutstandingClaimsBeforeBlock n (k + 1) =
      eraseOldestN (canonicalQueueService n k)
        (canonicalOwnedAvailableClaimsAtBlock n k) := rfl

/-- Every outstanding identity predates the block at which it is observed. -/
theorem mem_canonicalOwnedOutstandingClaimsBeforeBlock_lt_start
    {n : OddNat} {k i : ℕ}
    (hi : i ∈ canonicalOwnedOutstandingClaimsBeforeBlock n k) :
    i < canonicalBlockStartTime n k := by
  induction k with
  | zero => simp at hi
  | succ k ih =>
      have hiAvail := mem_of_mem_eraseOldestN hi
      rcases Finset.mem_union.mp hiAvail with hiOld | hiNew
      · have hlt := ih hiOld
        rw [canonicalBlockStartTime_succ]
        have hlen := one_le_canonicalBlockLength n k
        omega
      · exact (Finset.mem_Ico.mp
          (mem_canonicalBlockClaimSourceCarrier_interval hiNew)).2

/-- Every outstanding identity remains an actual carry-two source. -/
theorem carryTwoDebtAt_of_mem_canonicalOwnedOutstandingClaimsBeforeBlock
    {n : OddNat} {k i : ℕ}
    (hi : i ∈ canonicalOwnedOutstandingClaimsBeforeBlock n k) :
    CarryTwoDebtAt n i := by
  induction k with
  | zero => simp at hi
  | succ k ih =>
      have hiAvail := mem_of_mem_eraseOldestN hi
      rcases Finset.mem_union.mp hiAvail with hiOld | hiNew
      · exact ih hiOld
      · exact carryTwoDebtAt_of_mem_canonicalBlockClaimSourceCarrier hiNew

/-- Old outstanding identities and current-block arrivals cannot coincide. -/
theorem disjoint_canonicalOwnedOutstandingClaimsBeforeBlock_blockCarrier
    (n : OddNat) (k : ℕ) :
    Disjoint (canonicalOwnedOutstandingClaimsBeforeBlock n k)
      (canonicalBlockClaimSourceCarrier n k) := by
  classical
  apply Finset.disjoint_left.mpr
  intro i hiOld hiNew
  have hlt := mem_canonicalOwnedOutstandingClaimsBeforeBlock_lt_start hiOld
  have hle := (Finset.mem_Ico.mp
    (mem_canonicalBlockClaimSourceCarrier_interval hiNew)).1
  omega

/-- Consumed identities and the successor outstanding queue are disjoint. -/
theorem disjoint_canonicalOwnedConsumedClaimsAtBlock_nextOutstanding
    (n : OddNat) (k : ℕ) :
    Disjoint (canonicalOwnedConsumedClaimsAtBlock n k)
      (canonicalOwnedOutstandingClaimsBeforeBlock n (k + 1)) := by
  exact disjoint_consumedOldestN_eraseOldestN _ _

/-- Consumption plus the next queue reconstructs all claims available now. -/
theorem canonicalOwnedConsumed_union_nextOutstanding
    (n : OddNat) (k : ℕ) :
    canonicalOwnedConsumedClaimsAtBlock n k ∪
        canonicalOwnedOutstandingClaimsBeforeBlock n (k + 1) =
      canonicalOwnedAvailableClaimsAtBlock n k := by
  exact consumedOldestN_union_eraseOldestN _ _

/-- Every source consumed at block `k` predates the next block start. -/
theorem mem_canonicalOwnedConsumedClaimsAtBlock_lt_next_start
    {n : OddNat} {k i : ℕ}
    (hi : i ∈ canonicalOwnedConsumedClaimsAtBlock n k) :
    i < canonicalBlockStartTime n (k + 1) := by
  have hiAvail := (Finset.mem_sdiff.mp hi).1
  rcases Finset.mem_union.mp hiAvail with hiOld | hiNew
  · have hlt := mem_canonicalOwnedOutstandingClaimsBeforeBlock_lt_start hiOld
    rw [canonicalBlockStartTime_succ]
    have hlen := one_le_canonicalBlockLength n k
    omega
  · exact (Finset.mem_Ico.mp
      (mem_canonicalBlockClaimSourceCarrier_interval hiNew)).2

/-- Once consumed, a source identity never reappears in a later owned queue. -/
theorem not_mem_canonicalOwnedOutstandingClaimsBeforeBlock_of_consumed
    {n : OddNat} {k m i : ℕ}
    (hi : i ∈ canonicalOwnedConsumedClaimsAtBlock n k)
    (hkm : k < m) :
    i ∉ canonicalOwnedOutstandingClaimsBeforeBlock n m := by
  induction m generalizing k i with
  | zero => omega
  | succ m ih =>
      intro hiLater
      have hiAvail := mem_of_mem_eraseOldestN hiLater
      by_cases hkmEq : k = m
      · subst k
        exact (Finset.disjoint_left.mp
          (disjoint_canonicalOwnedConsumedClaimsAtBlock_nextOutstanding n m)
          hi hiLater)
      · have hkmLt : k < m := by omega
        rcases Finset.mem_union.mp hiAvail with hiOld | hiNew
        · exact ih hi hkmLt hiOld
        · have hiLt :=
            mem_canonicalOwnedConsumedClaimsAtBlock_lt_next_start hi
          have hstart := canonicalBlockStartTime_mono n
            (show k + 1 ≤ m by omega)
          have hiGe := (Finset.mem_Ico.mp
            (mem_canonicalBlockClaimSourceCarrier_interval hiNew)).1
          omega

/-- The source-bearing outstanding queue realizes the existing scalar queue. -/
theorem card_canonicalOwnedOutstandingClaimsBeforeBlock
    (n : OddNat) (k : ℕ) :
    (canonicalOwnedOutstandingClaimsBeforeBlock n k).card =
      canonicalOutstandingClaimQueueBeforeBlock n k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [canonicalOwnedOutstandingClaimsBeforeBlock_succ,
        card_eraseOldestN, canonicalOwnedAvailableClaimsAtBlock,
        Finset.card_union_of_disjoint
          (disjoint_canonicalOwnedOutstandingClaimsBeforeBlock_blockCarrier n k),
        ih, card_canonicalBlockClaimSourceCarrier,
        canonicalOutstandingClaimQueueBeforeBlock_succ]
      have hbalance := canonicalOutstandingClaimQueue_add_consumed n k
      unfold canonicalQueueConsumed at hbalance
      omega

/-- Owned oldest-first consumption realizes the scalar consumed count. -/
theorem card_canonicalOwnedConsumedClaimsAtBlock
    (n : OddNat) (k : ℕ) :
    (canonicalOwnedConsumedClaimsAtBlock n k).card =
      canonicalQueueConsumed n k := by
  rw [canonicalOwnedConsumedClaimsAtBlock, card_consumedOldestN,
    canonicalOwnedAvailableClaimsAtBlock,
    Finset.card_union_of_disjoint
      (disjoint_canonicalOwnedOutstandingClaimsBeforeBlock_blockCarrier n k),
    card_canonicalOwnedOutstandingClaimsBeforeBlock,
    card_canonicalBlockClaimSourceCarrier]
  unfold canonicalQueueConsumed
  exact Nat.min_comm _ _

/-- Uniform actual source age for every identity retained by the owned queue. -/
def CanonicalOwnedOutstandingClaimsHaveSourceAgeAtMost
    (n : OddNat) (H : ℕ) : Prop :=
  ∀ m i, i ∈ canonicalOwnedOutstandingClaimsBeforeBlock n m →
    canonicalBlockStartTime n m - i ≤ H

/-- An owned source satisfying the age bound belongs to the actual recent
source carrier, not merely to a set of the same cardinality. -/
theorem CanonicalOwnedOutstandingClaimsHaveSourceAgeAtMost.mem_recentCarrier
    {n : OddNat} {H m i : ℕ}
    (h : CanonicalOwnedOutstandingClaimsHaveSourceAgeAtMost n H)
    (hi : i ∈ canonicalOwnedOutstandingClaimsBeforeBlock n m) :
    i ∈ canonicalRecentSourceClaimCarrier n H m := by
  rw [canonicalRecentSourceClaimCarrier, mem_carryTwoPositions_iff]
  have hlt := mem_canonicalOwnedOutstandingClaimsBeforeBlock_lt_start hi
  have hage := h m i hi
  have hcarry :=
    carryTwoDebtAt_of_mem_canonicalOwnedOutstandingClaimsBeforeBlock hi
  exact ⟨Finset.mem_Ico.mpr ⟨by omega, hlt⟩, hcarry⟩

/-- A genuine owned-queue age theorem implies the cp-333 scalar cardinal
coverage predicate. -/
theorem CanonicalOwnedOutstandingClaimsHaveSourceAgeAtMost.to_cardCovered
    {n : OddNat} {H : ℕ}
    (h : CanonicalOwnedOutstandingClaimsHaveSourceAgeAtMost n H) :
    CanonicalOutstandingQueueCardCoveredByRecentSourceClaims n H := by
  intro m
  rw [← card_canonicalOwnedOutstandingClaimsBeforeBlock]
  exact Finset.card_le_card fun i hi => h.mem_recentCarrier hi

/-- Actual uniform source age gives a uniform scalar queue bound. -/
theorem CanonicalOwnedOutstandingClaimsHaveSourceAgeAtMost.to_queueUniformUpperBound
    {n : OddNat} {H : ℕ}
    (h : CanonicalOwnedOutstandingClaimsHaveSourceAgeAtMost n H) :
    CanonicalOutstandingClaimQueueUniformUpperBound n H :=
  h.to_cardCovered.to_queueUniformUpperBound

/-- Actual uniform source age reaches the endpoint-width theorem.  No theorem
in this module asserts that such a uniform `H` exists. -/
theorem CanonicalOwnedOutstandingClaimsHaveSourceAgeAtMost.to_endpointWidthUniformUpperBound
    {n : OddNat} {H : ℕ}
    (h : CanonicalOwnedOutstandingClaimsHaveSourceAgeAtMost n H) :
    CanonicalEndpointWidthUniformUpperBound n (bitWidth n.1 + H) :=
  h.to_cardCovered.to_endpointWidthUniformUpperBound

end DkMath.Collatz
