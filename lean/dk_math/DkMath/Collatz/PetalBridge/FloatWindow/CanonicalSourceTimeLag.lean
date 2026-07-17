/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Collatz.PetalBridge.FloatWindow.BoundedRepaymentLag
import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentBlockNormalForm

#print "file: DkMath.Collatz.PetalBridge.FloatWindow.CanonicalSourceTimeLag"

namespace DkMath.Collatz

/-!
# Canonical source-time lag

Block indices are not physical time.  This module converts canonical block
arrival counts back to their actual orbit-source interval.  The resulting
conditional route asks for a uniform source-age theorem, not a uniform number
of blocks.
-/

/-- Consecutive canonical block starts differ by the exact block length. -/
theorem canonicalBlockStartTime_succ
    (n : OddNat) (k : ℕ) :
    canonicalBlockStartTime n (k + 1) =
      canonicalBlockStartTime n k + canonicalBlockLength n k := by
  have hend := canonicalBlockStartTime_add_length_sub_one_eq_endpoint n k
  have hlen := one_le_canonicalBlockLength n k
  change paymentEndpointSeq n k + 1 =
    canonicalBlockStartTime n k + canonicalBlockLength n k
  omega

/-- Canonical block lengths telescope exactly to the next block start. -/
theorem sum_canonicalBlockLength_range_eq_startTime
    (n : OddNat) (m : ℕ) :
    (∑ k ∈ Finset.range m, canonicalBlockLength n k) =
      canonicalBlockStartTime n m := by
  induction m with
  | zero => simp [canonicalBlockStartTime, canonicalEndpointBlockStart]
  | succ m ih =>
      rw [Finset.sum_range_succ, ih, canonicalBlockStartTime_succ]

/-- A block-index interval has exactly the corresponding orbit-time span. -/
theorem sum_canonicalBlockLength_Ico_eq_startTime_sub
    (n : OddNat) {q m : ℕ} (hqm : q ≤ m) :
    (∑ k ∈ Finset.Ico q m, canonicalBlockLength n k) =
      canonicalBlockStartTime n m - canonicalBlockStartTime n q := by
  have hsplit := Finset.sum_range_add_sum_Ico
    (fun k => canonicalBlockLength n k) hqm
  rw [sum_canonicalBlockLength_range_eq_startTime,
    sum_canonicalBlockLength_range_eq_startTime] at hsplit
  have hadd :
      (∑ k ∈ Finset.Ico q m, canonicalBlockLength n k) +
          canonicalBlockStartTime n q = canonicalBlockStartTime n m := by
    simpa [Nat.add_comm] using hsplit
  exact Nat.eq_sub_of_add_eq hadd

/-- Canonical demand over a block interval is bounded by its actual source-time
span. -/
theorem sum_canonicalQueueDemand_Ico_le_sourceTimeSpan
    (n : OddNat) {q m : ℕ} (hqm : q ≤ m) :
    (∑ k ∈ Finset.Ico q m, canonicalQueueDemand n k) ≤
      canonicalBlockStartTime n m - canonicalBlockStartTime n q := by
  calc
    (∑ k ∈ Finset.Ico q m, canonicalQueueDemand n k) ≤
        ∑ k ∈ Finset.Ico q m, canonicalBlockLength n k :=
      Finset.sum_le_sum fun k _ => canonicalBlockClaimCount_le_length n k
    _ = canonicalBlockStartTime n m - canonicalBlockStartTime n q :=
      sum_canonicalBlockLength_Ico_eq_startTime_sub n hqm

/-- The corrected recent block-demand window is bounded by the corresponding
actual orbit-source span. -/
theorem recentCanonicalDemand_le_sourceTimeSpan
    (n : OddNat) (L m : ℕ) :
    recentArrivalMass (canonicalQueueDemand n) L m ≤
      canonicalBlockStartTime n m - canonicalBlockStartTime n (m - L) := by
  unfold recentArrivalMass
  exact sum_canonicalQueueDemand_Ico_le_sourceTimeSpan n (Nat.sub_le m L)

/-! ## Exact block/source carrier identification -/

/-- Carry-two claim sources born in canonical block `k`. -/
noncomputable def canonicalBlockClaimSourceCarrier
    (n : OddNat) (k : ℕ) : Finset ℕ :=
  carryTwoPositions n
    (Finset.Ico (canonicalBlockStartTime n k)
      (canonicalBlockStartTime n (k + 1)))

/-- The claims born in one canonical block are exactly its carry-two source
addresses in the half-open block interval. -/
theorem canonicalQueueDemand_eq_carryTwoPositions_block_card
    (n : OddNat) (k : ℕ) :
    canonicalQueueDemand n k =
      (carryTwoPositions n
        (Finset.Ico (canonicalBlockStartTime n k)
          (canonicalBlockStartTime n (k + 1)))).card := by
  classical
  unfold canonicalQueueDemand canonicalBlockClaimCount
  rw [carryTwoPaymentClaimFiberAt_eq_filter_universalPaymentBlock_carryTwo n
    (paymentEndpointSeq n k)
    (orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n k)]
  apply congrArg Finset.card
  ext i
  rw [mem_carryTwoPositions_iff, mem_carryTwoPositions_iff]
  have hstart := canonicalBlockStartTime_eq_universalPaymentBlockStart n k
  have htop : canonicalBlockStartTime n (k + 1) =
      paymentEndpointSeq n k + 1 := by
    simp [canonicalBlockStartTime, canonicalEndpointBlockStart]
  constructor
  · rintro ⟨hi, hcarry⟩
    have hlo : canonicalBlockStartTime n k ≤ i := by
      rw [hstart]
      exact (Finset.mem_Icc.mp hi).1
    exact ⟨Finset.mem_Ico.mpr ⟨hlo, by
      have := (Finset.mem_Icc.mp hi).2
      omega⟩, hcarry⟩
  · rintro ⟨hi, hcarry⟩
    have hlo : universalPaymentBlockStart n (paymentEndpointSeq n k)
        (orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n k) ≤ i := by
      rw [← hstart]
      exact (Finset.mem_Ico.mp hi).1
    exact ⟨Finset.mem_Icc.mpr ⟨hlo, by
      have := (Finset.mem_Ico.mp hi).2
      omega⟩, hcarry⟩

/-- Named-carrier form of the exact one-block demand identity. -/
theorem card_canonicalBlockClaimSourceCarrier
    (n : OddNat) (k : ℕ) :
    (canonicalBlockClaimSourceCarrier n k).card = canonicalQueueDemand n k := by
  exact (canonicalQueueDemand_eq_carryTwoPositions_block_card n k).symm

/-- Every block claim source lies in that exact half-open source-time block. -/
theorem mem_canonicalBlockClaimSourceCarrier_interval
    {n : OddNat} {k i : ℕ}
    (hi : i ∈ canonicalBlockClaimSourceCarrier n k) :
    i ∈ Finset.Ico (canonicalBlockStartTime n k)
      (canonicalBlockStartTime n (k + 1)) := by
  exact (mem_carryTwoPositions_iff.mp hi).1

/-- Every member of a block claim carrier is an actual carry-two debt source. -/
theorem carryTwoDebtAt_of_mem_canonicalBlockClaimSourceCarrier
    {n : OddNat} {k i : ℕ}
    (hi : i ∈ canonicalBlockClaimSourceCarrier n k) :
    CarryTwoDebtAt n i := by
  exact (mem_carryTwoPositions_iff.mp hi).2

/-- Block-start time is monotone in the block index. -/
theorem canonicalBlockStartTime_mono
    (n : OddNat) {q m : ℕ} (hqm : q ≤ m) :
    canonicalBlockStartTime n q ≤ canonicalBlockStartTime n m := by
  have hsplit := Finset.sum_range_add_sum_Ico
    (fun k => canonicalBlockLength n k) hqm
  rw [sum_canonicalBlockLength_range_eq_startTime,
    sum_canonicalBlockLength_range_eq_startTime] at hsplit
  omega

/-- Distinct canonical blocks have disjoint source-address carriers. -/
theorem disjoint_canonicalBlockClaimSourceCarrier
    (n : OddNat) {j k : ℕ} (hjk : j ≠ k) :
    Disjoint (canonicalBlockClaimSourceCarrier n j)
      (canonicalBlockClaimSourceCarrier n k) := by
  classical
  have disj_of_lt : ∀ {a b : ℕ}, a < b →
      Disjoint (canonicalBlockClaimSourceCarrier n a)
        (canonicalBlockClaimSourceCarrier n b) := by
    intro a b hab
    apply Finset.disjoint_left.mpr
    intro i hia hib
    have ha := Finset.mem_Ico.mp
      (mem_canonicalBlockClaimSourceCarrier_interval hia)
    have hb := Finset.mem_Ico.mp
      (mem_canonicalBlockClaimSourceCarrier_interval hib)
    have hstart := canonicalBlockStartTime_mono n (show a + 1 ≤ b by omega)
    omega
  rcases lt_or_gt_of_ne hjk with hjklt | hkjlt
  · exact disj_of_lt hjklt
  · exact (disj_of_lt hkjlt).symm

/-- Prefix demand is exactly the number of carry-two source addresses before
the corresponding block start. -/
theorem sum_canonicalQueueDemand_range_eq_sourceClaims_card
    (n : OddNat) (m : ℕ) :
    (∑ k ∈ Finset.range m, canonicalQueueDemand n k) =
      (carryTwoPositions n
        (Finset.Ico 0 (canonicalBlockStartTime n m))).card := by
  classical
  induction m with
  | zero => simp [canonicalBlockStartTime, canonicalEndpointBlockStart,
      carryTwoPositions]
  | succ m ih =>
      let A := carryTwoPositions n (Finset.Ico 0 (canonicalBlockStartTime n m))
      let B := carryTwoPositions n
        (Finset.Ico (canonicalBlockStartTime n m)
          (canonicalBlockStartTime n (m + 1)))
      have hdisj : Disjoint A B := by
        apply Finset.disjoint_left.mpr
        intro i hiA hiB
        dsimp [A] at hiA
        dsimp [B] at hiB
        have hA := (mem_carryTwoPositions_iff.mp hiA).1
        have hB := (mem_carryTwoPositions_iff.mp hiB).1
        have hAI := Finset.mem_Ico.mp hA
        have hBI := Finset.mem_Ico.mp hB
        omega
      have hunion : A ∪ B =
          carryTwoPositions n
            (Finset.Ico 0 (canonicalBlockStartTime n (m + 1))) := by
        ext i
        have hmono := canonicalBlockStartTime_mono n (Nat.le_succ m)
        have hnextEq : canonicalBlockStartTime n m.succ =
            canonicalBlockStartTime n (m + 1) := rfl
        constructor
        · intro hi
          rcases Finset.mem_union.mp hi with hiA | hiB
          · have hA := mem_carryTwoPositions_iff.mp (by simpa [A] using hiA)
            have hAI := Finset.mem_range.mp hA.1
            exact mem_carryTwoPositions_iff.mpr
              ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, hA.2⟩
          · have hB := mem_carryTwoPositions_iff.mp (by simpa [B] using hiB)
            have hBI := Finset.mem_Ico.mp hB.1
            exact mem_carryTwoPositions_iff.mpr
              ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, hB.2⟩
        · intro hi
          have hI := mem_carryTwoPositions_iff.mp hi
          by_cases hleft : i < canonicalBlockStartTime n m
          · apply Finset.mem_union_left
            exact (show i ∈ A by
              apply mem_carryTwoPositions_iff.mpr
              exact ⟨Finset.mem_Ico.mpr ⟨by omega, hleft⟩, hI.2⟩)
          · apply Finset.mem_union_right
            exact (show i ∈ B by
              apply mem_carryTwoPositions_iff.mpr
              exact ⟨Finset.mem_Ico.mpr ⟨by omega,
                (Finset.mem_Ico.mp hI.1).2⟩, hI.2⟩)
      rw [Finset.sum_range_succ, ih,
        canonicalQueueDemand_eq_carryTwoPositions_block_card]
      change A.card + B.card = _
      rw [← Finset.card_union_of_disjoint hdisj, hunion]

/-- Canonical demand over any block interval is exactly the carry-two source
count in the corresponding orbit-time interval. -/
theorem sum_canonicalQueueDemand_Ico_eq_sourceClaims_card
    (n : OddNat) {q m : ℕ} (hqm : q ≤ m) :
    (∑ k ∈ Finset.Ico q m, canonicalQueueDemand n k) =
      (carryTwoPositions n
        (Finset.Ico (canonicalBlockStartTime n q)
          (canonicalBlockStartTime n m))).card := by
  classical
  let A := carryTwoPositions n (Finset.Ico 0 (canonicalBlockStartTime n q))
  let B := carryTwoPositions n
    (Finset.Ico (canonicalBlockStartTime n q) (canonicalBlockStartTime n m))
  have htime := canonicalBlockStartTime_mono n hqm
  have hdisj : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro i hiA hiB
    dsimp [A] at hiA
    dsimp [B] at hiB
    have hA := (mem_carryTwoPositions_iff.mp hiA).1
    have hB := (mem_carryTwoPositions_iff.mp hiB).1
    have hAI := Finset.mem_Ico.mp hA
    have hBI := Finset.mem_Ico.mp hB
    omega
  have hunion : A ∪ B =
      carryTwoPositions n (Finset.Ico 0 (canonicalBlockStartTime n m)) := by
    ext i
    constructor
    · intro hi
      rcases Finset.mem_union.mp hi with hiA | hiB
      · have hA := mem_carryTwoPositions_iff.mp (by simpa [A] using hiA)
        have hAI := Finset.mem_range.mp hA.1
        exact mem_carryTwoPositions_iff.mpr
          ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, hA.2⟩
      · have hB := mem_carryTwoPositions_iff.mp (by simpa [B] using hiB)
        have hBI := Finset.mem_Ico.mp hB.1
        exact mem_carryTwoPositions_iff.mpr
          ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, hB.2⟩
    · intro hi
      have hI := mem_carryTwoPositions_iff.mp hi
      by_cases hleft : i < canonicalBlockStartTime n q
      · apply Finset.mem_union_left
        exact (show i ∈ A by
          apply mem_carryTwoPositions_iff.mpr
          exact ⟨Finset.mem_Ico.mpr ⟨by omega, hleft⟩, hI.2⟩)
      · apply Finset.mem_union_right
        exact (show i ∈ B by
          apply mem_carryTwoPositions_iff.mpr
          exact ⟨Finset.mem_Ico.mpr ⟨by omega,
            (Finset.mem_Ico.mp hI.1).2⟩, hI.2⟩)
  have hsum := Finset.sum_range_add_sum_Ico
    (fun k => canonicalQueueDemand n k) hqm
  rw [sum_canonicalQueueDemand_range_eq_sourceClaims_card,
    sum_canonicalQueueDemand_range_eq_sourceClaims_card] at hsum
  change A.card + (∑ k ∈ Finset.Ico q m, canonicalQueueDemand n k) = _ at hsum
  have hcard : A.card + B.card =
      (carryTwoPositions n (Finset.Ico 0 (canonicalBlockStartTime n m))).card := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion]
  change (∑ k ∈ Finset.Ico q m, canonicalQueueDemand n k) = B.card
  omega

/-- Carry-two source addresses in the last `H` units of actual orbit time. -/
noncomputable def canonicalRecentSourceClaimCarrier
    (n : OddNat) (H m : ℕ) : Finset ℕ :=
  carryTwoPositions n
    (Finset.Ico (canonicalBlockStartTime n m - H)
      (canonicalBlockStartTime n m))

/-- A source-time interval of width at most `H` contains at most `H` claims. -/
theorem card_canonicalRecentSourceClaimCarrier_le
    (n : OddNat) (H m : ℕ) :
    (canonicalRecentSourceClaimCarrier n H m).card ≤ H := by
  classical
  calc
    (canonicalRecentSourceClaimCarrier n H m).card ≤
        (Finset.Ico (canonicalBlockStartTime n m - H)
          (canonicalBlockStartTime n m)).card := by
      unfold canonicalRecentSourceClaimCarrier carryTwoPositions
      exact Finset.card_filter_le _ _
    _ ≤ H := by simp; omega

@[simp] theorem canonicalRecentSourceClaimCarrier_zero_time
    (n : OddNat) (H : ℕ) :
    canonicalRecentSourceClaimCarrier n H 0 = ∅ := by
  simp [canonicalRecentSourceClaimCarrier, canonicalBlockStartTime,
    canonicalEndpointBlockStart, carryTwoPositions]

@[simp] theorem canonicalRecentSourceClaimCarrier_zero_horizon
    (n : OddNat) (m : ℕ) :
    canonicalRecentSourceClaimCarrier n 0 m = ∅ := by
  simp [canonicalRecentSourceClaimCarrier, carryTwoPositions]

/--
Scalar cardinality coverage: the anonymous outstanding queue count is no
larger than the number of recent carry-two sources.  This does not identify
queue elements with those sources and is not itself a claim-age theorem.
-/
def CanonicalOutstandingQueueCardCoveredByRecentSourceClaims
    (n : OddNat) (H : ℕ) : Prop :=
  ∀ m, canonicalOutstandingClaimQueueBeforeBlock n m ≤
    (canonicalRecentSourceClaimCarrier n H m).card

/-- Compatibility alias for the cp-333 cardinality-only predicate. -/
abbrev CanonicalOutstandingQueueCoveredByRecentSourceClaims :=
  CanonicalOutstandingQueueCardCoveredByRecentSourceClaims

/-- Uniform source-age coverage immediately bounds every pre-block queue. -/
theorem canonicalQueueBeforeBlock_le_of_recentSourceClaims
    {n : OddNat} {H : ℕ}
    (h : CanonicalOutstandingQueueCoveredByRecentSourceClaims n H) (m : ℕ) :
    canonicalOutstandingClaimQueueBeforeBlock n m ≤ H :=
  (h m).trans (card_canonicalRecentSourceClaimCarrier_le n H m)

/-- Uniform source-age coverage gives the public post-block queue bound. -/
theorem CanonicalOutstandingQueueCoveredByRecentSourceClaims.to_queueUniformUpperBound
    {n : OddNat} {H : ℕ}
    (h : CanonicalOutstandingQueueCoveredByRecentSourceClaims n H) :
    CanonicalOutstandingClaimQueueUniformUpperBound n H := by
  intro k
  simpa using canonicalQueueBeforeBlock_le_of_recentSourceClaims h (k + 1)

/-- The refined lag route reaches endpoint width once a uniform source-age
theorem is supplied. -/
theorem CanonicalOutstandingQueueCoveredByRecentSourceClaims.to_endpointWidthUniformUpperBound
    {n : OddNat} {H : ℕ}
    (h : CanonicalOutstandingQueueCoveredByRecentSourceClaims n H) :
    CanonicalEndpointWidthUniformUpperBound n (bitWidth n.1 + H) :=
  h.to_queueUniformUpperBound.to_endpointWidthUniformUpperBound

/-- Precisely named cardinal-coverage route to the scalar queue bound. -/
theorem CanonicalOutstandingQueueCardCoveredByRecentSourceClaims.to_queueUniformUpperBound
    {n : OddNat} {H : ℕ}
    (h : CanonicalOutstandingQueueCardCoveredByRecentSourceClaims n H) :
    CanonicalOutstandingClaimQueueUniformUpperBound n H :=
  CanonicalOutstandingQueueCoveredByRecentSourceClaims.to_queueUniformUpperBound h

/-- Precisely named cardinal-coverage route to the endpoint-width bound. -/
theorem CanonicalOutstandingQueueCardCoveredByRecentSourceClaims.to_endpointWidthUniformUpperBound
    {n : OddNat} {H : ℕ}
    (h : CanonicalOutstandingQueueCardCoveredByRecentSourceClaims n H) :
    CanonicalEndpointWidthUniformUpperBound n (bitWidth n.1 + H) :=
  h.to_queueUniformUpperBound.to_endpointWidthUniformUpperBound

/-!
No uniform `H` is asserted here.  The remaining input on this route is exactly
a theorem that every outstanding canonical claim has source age at most one
fixed `H`.  The carrier preserves actual source addresses, unlike block-count
lag alone.
-/

end DkMath.Collatz
