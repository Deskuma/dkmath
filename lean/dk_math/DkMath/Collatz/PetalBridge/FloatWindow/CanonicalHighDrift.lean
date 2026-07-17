/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalEndpointConservation

#print "file: DkMath.Collatz.PetalBridge.FloatWindow.CanonicalHighDrift"

namespace DkMath.Collatz

/-!
# Finite high-drift event carrier

These sets are finite diagnostics over the observed prefix `[0, M)`.  Their
finiteness is inherited from `Finset.range M` and makes no statement about the
number of high-drift blocks over all canonical time.
-/

/-- Blocks below `M` whose realized endpoint drift reaches natural threshold
`K`. -/
noncomputable def canonicalHighDriftBlocksUpTo
    (n : OddNat) (K M : ℕ) : Finset ℕ :=
  (Finset.range M).filter fun m =>
    (K : ℤ) ≤ endpointAccountingTerm n m

/-- Exact membership in the finite high-drift carrier. -/
@[simp] theorem mem_canonicalHighDriftBlocksUpTo
    {n : OddNat} {K M m : ℕ} :
    m ∈ canonicalHighDriftBlocksUpTo n K M ↔
      m < M ∧ (K : ℤ) ≤ endpointAccountingTerm n m := by
  simp [canonicalHighDriftBlocksUpTo]

/-- Structural membership form obtained from exact block conservation. -/
theorem mem_canonicalHighDriftBlocksUpTo_iff_budget
    {n : OddNat} {K M m : ℕ} :
    m ∈ canonicalHighDriftBlocksUpTo n K M ↔
      m < M ∧
        (K : ℤ) + ((canonicalBlockClaimHoles n m).card : ℤ) +
            (canonicalBlockTerminalValuation n m : ℤ) ≤
          (canonicalBlockLength n m : ℤ) := by
  rw [mem_canonicalHighDriftBlocksUpTo]
  constructor
  · rintro ⟨hm, hK⟩
    exact ⟨hm, (natCast_le_endpointAccountingTerm_iff n m K).mp hK⟩
  · rintro ⟨hm, hbudget⟩
    exact ⟨hm, (natCast_le_endpointAccountingTerm_iff n m K).mpr hbudget⟩

@[simp] theorem canonicalHighDriftBlocksUpTo_zero
    (n : OddNat) (K : ℕ) :
    canonicalHighDriftBlocksUpTo n K 0 = ∅ := by
  ext m
  simp

/-- Extending the horizon by one either inserts exactly the new terminal
index or leaves the finite carrier unchanged. -/
theorem canonicalHighDriftBlocksUpTo_succ
    (n : OddNat) (K M : ℕ) :
    canonicalHighDriftBlocksUpTo n K (M + 1) =
      if (K : ℤ) ≤ endpointAccountingTerm n M then
        insert M (canonicalHighDriftBlocksUpTo n K M)
      else canonicalHighDriftBlocksUpTo n K M := by
  unfold canonicalHighDriftBlocksUpTo
  rw [Finset.range_add_one, Finset.filter_insert]

/-- Membership at horizon `M + 1` decomposes into old membership or the new
terminal event. -/
theorem mem_canonicalHighDriftBlocksUpTo_succ_iff
    {n : OddNat} {K M m : ℕ} :
    m ∈ canonicalHighDriftBlocksUpTo n K (M + 1) ↔
      m ∈ canonicalHighDriftBlocksUpTo n K M ∨
        (m = M ∧ (K : ℤ) ≤ endpointAccountingTerm n M) := by
  rw [mem_canonicalHighDriftBlocksUpTo,
    mem_canonicalHighDriftBlocksUpTo]
  constructor <;> intro h
  · by_cases hm : m < M
    · exact Or.inl ⟨hm, h.2⟩
    · exact Or.inr ⟨by omega, by simpa [show m = M by omega] using h.2⟩
  · rcases h with h | ⟨rfl, hK⟩
    · exact ⟨by omega, h.2⟩
    · exact ⟨by omega, hK⟩

/-- Enlarging the observed prefix only adds possible events. -/
theorem canonicalHighDriftBlocksUpTo_mono_prefix
    (n : OddNat) (K : ℕ) {M N : ℕ} (hMN : M ≤ N) :
    canonicalHighDriftBlocksUpTo n K M ⊆
      canonicalHighDriftBlocksUpTo n K N := by
  intro m hm
  rw [mem_canonicalHighDriftBlocksUpTo] at hm ⊢
  exact ⟨hm.1.trans_le hMN, hm.2⟩

/-- Raising the threshold can only remove events. -/
theorem canonicalHighDriftBlocksUpTo_antitone_threshold
    (n : OddNat) (M : ℕ) {K J : ℕ} (hKJ : K ≤ J) :
    canonicalHighDriftBlocksUpTo n J M ⊆
      canonicalHighDriftBlocksUpTo n K M := by
  intro m hm
  rw [mem_canonicalHighDriftBlocksUpTo] at hm ⊢
  refine ⟨hm.1, ?_⟩
  exact (Int.ofNat_le.mpr hKJ).trans hm.2

/-- Number of observed high-drift blocks below `M`. -/
noncomputable def canonicalHighDriftEventCount
    (n : OddNat) (K M : ℕ) : ℕ :=
  (canonicalHighDriftBlocksUpTo n K M).card

/-- Exact one-step event-count update for the finite observation horizon. -/
theorem canonicalHighDriftEventCount_succ
    (n : OddNat) (K M : ℕ) :
    canonicalHighDriftEventCount n K (M + 1) =
      canonicalHighDriftEventCount n K M +
        if (K : ℤ) ≤ endpointAccountingTerm n M then 1 else 0 := by
  unfold canonicalHighDriftEventCount
  rw [canonicalHighDriftBlocksUpTo_succ]
  by_cases hnew : (K : ℤ) ≤ endpointAccountingTerm n M
  · simp [hnew, canonicalHighDriftBlocksUpTo]
  · simp [hnew]

/-- Event count is monotone in the finite observation horizon. -/
theorem canonicalHighDriftEventCount_mono_prefix
    (n : OddNat) (K : ℕ) {M N : ℕ} (hMN : M ≤ N) :
    canonicalHighDriftEventCount n K M ≤
      canonicalHighDriftEventCount n K N := by
  exact Finset.card_le_card
    (canonicalHighDriftBlocksUpTo_mono_prefix n K hMN)

/-- Event count is antitone in the drift threshold. -/
theorem canonicalHighDriftEventCount_antitone_threshold
    (n : OddNat) (M : ℕ) {K J : ℕ} (hKJ : K ≤ J) :
    canonicalHighDriftEventCount n J M ≤
      canonicalHighDriftEventCount n K M := by
  exact Finset.card_le_card
    (canonicalHighDriftBlocksUpTo_antitone_threshold n M hKJ)

/-- Every high-drift event in the finite carrier has a long enough block. -/
theorem blockLength_ge_of_mem_canonicalHighDriftBlocksUpTo
    {n : OddNat} {K M m : ℕ}
    (hm : m ∈ canonicalHighDriftBlocksUpTo n K M) :
    K ≤ canonicalBlockLength n m := by
  exact blockLength_ge_of_endpointAccountingTerm_ge
    (mem_canonicalHighDriftBlocksUpTo.mp hm).2

/-!
No union over all `M` is introduced here.  In particular, monotonicity of the
finite carriers does not establish eventual stabilization, finite total event
count, or repeated high drift for a fixed root.
-/

end DkMath.Collatz
