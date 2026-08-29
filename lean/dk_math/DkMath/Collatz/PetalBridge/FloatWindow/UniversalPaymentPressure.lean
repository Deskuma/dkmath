/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentFamily

#print "file: DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentPressure"

namespace DkMath.Collatz

/-!
# Pressure fibers on canonical universal payment blocks

The fibers below filter actual orbit times by the existing exact-depth
predicates. Closed cardinality formulas are proved only after these concrete
Finsets are fixed.
-/

/-- Exact-recovery times at depth `d` inside canonical block `k`. -/
noncomputable def canonicalPaymentBlockRecoveryFiber
    (n : OddNat) (k d : ℕ) : Finset ℕ := by
  classical
  exact (canonicalPaymentBlock n k).filter fun i =>
    OrbitDepthRecoversExactlyAt n i d

/-- Continuing times beyond depth `d` inside canonical block `k`. -/
noncomputable def canonicalPaymentBlockContinuationFiber
    (n : OddNat) (k d : ℕ) : Finset ℕ := by
  classical
  exact (canonicalPaymentBlock n k).filter fun i =>
    OrbitDepthContinuesBeyond n i d

/-- Membership API for a canonical recovery fiber. -/
theorem mem_canonicalPaymentBlockRecoveryFiber_iff
    {n : OddNat} {k d i : ℕ} :
    i ∈ canonicalPaymentBlockRecoveryFiber n k d ↔
      i ∈ canonicalPaymentBlock n k ∧ OrbitDepthRecoversExactlyAt n i d := by
  classical
  simp [canonicalPaymentBlockRecoveryFiber]

/-- Membership API for a canonical continuation fiber. -/
theorem mem_canonicalPaymentBlockContinuationFiber_iff
    {n : OddNat} {k d i : ℕ} :
    i ∈ canonicalPaymentBlockContinuationFiber n k d ↔
      i ∈ canonicalPaymentBlock n k ∧ OrbitDepthContinuesBeyond n i d := by
  classical
  simp [canonicalPaymentBlockContinuationFiber]

/-- The exact-depth staircase on a canonical block, measured from its endpoint. -/
theorem orbitExactDepth_eq_paymentEndpoint_sub_add_one_of_mem_canonicalPaymentBlock
    {n : OddNat} {k i : ℕ} (hi : i ∈ canonicalPaymentBlock n k) :
    orbitExactDepth n i = paymentEndpointSeq n k - i + 1 := by
  have hnonempty := orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n k
  apply orbitExactDepth_eq_endpoint_sub_add_one_of_mem_universalPaymentBlock
    (h := hnonempty)
  rw [← orbitPaymentSourceFiberAt_eq_Icc_universalPaymentBlockStart n
    (paymentEndpointSeq n k) hnonempty]
  rwa [← canonicalPaymentBlock_eq_sourceFiber]

/-- Canonical block length in endpoint-family coordinates. -/
noncomputable def canonicalPaymentBlockLength (n : OddNat) (k : ℕ) : ℕ :=
  (canonicalPaymentBlock n k).card

/-- The endpoint's universal fiber cardinality is the canonical block length. -/
theorem canonicalPaymentBlockLength_eq_sourceFiber_card (n : OddNat) (k : ℕ) :
    canonicalPaymentBlockLength n k =
      (orbitPaymentSourceFiberAt n (paymentEndpointSeq n k)).card := by
  unfold canonicalPaymentBlockLength
  rw [canonicalPaymentBlock_eq_sourceFiber]

/-- Canonical block length is endpoint minus start plus one. -/
theorem canonicalPaymentBlockLength_eq_endpoint_sub_start_add_one
    (n : OddNat) (k : ℕ) :
    canonicalPaymentBlockLength n k =
      paymentEndpointSeq n k -
        universalPaymentBlockStart n (paymentEndpointSeq n k)
          (orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n k) + 1 := by
  rw [canonicalPaymentBlockLength_eq_sourceFiber_card]
  exact orbitPaymentSourceFiberAt_card_eq_endpoint_sub_start_add_one n
    (paymentEndpointSeq n k)
    (orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n k)

/-- A canonical block is the closed interval from its universal start to its endpoint. -/
theorem canonicalPaymentBlock_eq_Icc_universalPaymentBlockStart
    (n : OddNat) (k : ℕ) :
    canonicalPaymentBlock n k =
      Finset.Icc
        (universalPaymentBlockStart n (paymentEndpointSeq n k)
          (orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n k))
        (paymentEndpointSeq n k) := by
  rw [canonicalPaymentBlock_eq_sourceFiber]
  exact orbitPaymentSourceFiberAt_eq_Icc_universalPaymentBlockStart n
    (paymentEndpointSeq n k)
    (orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n k)

/-- Depth zero is absent from every canonical exact-recovery fiber. -/
theorem canonicalPaymentBlockRecoveryFiber_zero_eq_empty
    (n : OddNat) (k : ℕ) :
    canonicalPaymentBlockRecoveryFiber n k 0 = ∅ := by
  ext i
  simp only [mem_canonicalPaymentBlockRecoveryFiber_iff, Finset.notMem_empty,
    iff_false, not_and]
  intro hi hrecover
  have hdepth :=
    orbitExactDepth_eq_paymentEndpoint_sub_add_one_of_mem_canonicalPaymentBlock hi
  have hrecoverDepth : orbitExactDepth n i = 0 := by
    simpa [OrbitDepthRecoversExactlyAt, orbitExactDepth] using hrecover
  omega

/-- Exact recovery inside one canonical block is injective in the source time. -/
theorem eq_of_mem_canonicalPaymentBlock_of_recovery_same_depth
    {n : OddNat} {k d i i' : ℕ}
    (hi : i ∈ canonicalPaymentBlock n k)
    (hi' : i' ∈ canonicalPaymentBlock n k)
    (hrecover : OrbitDepthRecoversExactlyAt n i d)
    (hrecover' : OrbitDepthRecoversExactlyAt n i' d) :
    i = i' := by
  have hiDepth :=
    orbitExactDepth_eq_paymentEndpoint_sub_add_one_of_mem_canonicalPaymentBlock hi
  have hi'Depth :=
    orbitExactDepth_eq_paymentEndpoint_sub_add_one_of_mem_canonicalPaymentBlock hi'
  have hrecoverDepth : orbitExactDepth n i = d := by
    simpa [OrbitDepthRecoversExactlyAt, orbitExactDepth] using hrecover
  have hrecoverDepth' : orbitExactDepth n i' = d := by
    simpa [OrbitDepthRecoversExactlyAt, orbitExactDepth] using hrecover'
  rw [hiDepth] at hrecoverDepth
  rw [hi'Depth] at hrecoverDepth'
  have hie := (mem_canonicalPaymentBlock_iff_target_eq.mp hi)
  have hi'e := (mem_canonicalPaymentBlock_iff_target_eq.mp hi')
  have hile := le_orbitPaymentTarget n i
  have hi'le := le_orbitPaymentTarget n i'
  omega

/-- Recovery fiber cardinality is at most one. -/
theorem canonicalPaymentBlockRecoveryFiber_card_le_one
    (n : OddNat) (k d : ℕ) :
    (canonicalPaymentBlockRecoveryFiber n k d).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro i hi i' hi'
  rcases mem_canonicalPaymentBlockRecoveryFiber_iff.mp hi with ⟨hib, hir⟩
  rcases mem_canonicalPaymentBlockRecoveryFiber_iff.mp hi' with ⟨hi'b, hi'r⟩
  exact eq_of_mem_canonicalPaymentBlock_of_recovery_same_depth hib hi'b hir hi'r

/-- A recovery depth occurs in a canonical block exactly on its positive staircase range. -/
theorem canonicalPaymentBlockRecoveryFiber_nonempty_iff
    (n : OddNat) (k d : ℕ) :
    (canonicalPaymentBlockRecoveryFiber n k d).Nonempty ↔
      1 ≤ d ∧ d ≤ canonicalPaymentBlockLength n k := by
  let e := paymentEndpointSeq n k
  let h := orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n k
  let b := universalPaymentBlockStart n e h
  have hblock : canonicalPaymentBlock n k = Finset.Icc b e := by
    simpa [e, h, b] using canonicalPaymentBlock_eq_Icc_universalPaymentBlockStart n k
  have hbmem := universalPaymentBlockStart_mem_sourceFiber n e h
  have hbe : b ≤ e := (mem_orbitPaymentSourceFiberAt_iff.mp hbmem).1
  have hlength : canonicalPaymentBlockLength n k = e - b + 1 := by
    simpa [e, h, b] using
      canonicalPaymentBlockLength_eq_endpoint_sub_start_add_one n k
  constructor
  · rintro ⟨i, hi⟩
    rcases mem_canonicalPaymentBlockRecoveryFiber_iff.mp hi with ⟨hiblock, hirecover⟩
    have hiIcc : i ∈ Finset.Icc b e := by simpa [hblock] using hiblock
    have hdepth :=
      orbitExactDepth_eq_paymentEndpoint_sub_add_one_of_mem_canonicalPaymentBlock hiblock
    have hirecoverDepth : orbitExactDepth n i = d := by
      simpa [OrbitDepthRecoversExactlyAt, orbitExactDepth] using hirecover
    rcases Finset.mem_Icc.mp hiIcc with ⟨hbi, hie⟩
    change orbitExactDepth n i = e - i + 1 at hdepth
    omega
  · rintro ⟨hdpos, hdle⟩
    let i := e + 1 - d
    have hbi : b ≤ i := by
      dsimp [i]
      omega
    have hie : i ≤ e := by
      dsimp [i]
      omega
    have hiblock : i ∈ canonicalPaymentBlock n k := by
      rw [hblock]
      exact Finset.mem_Icc.mpr ⟨hbi, hie⟩
    have hdepth :=
      orbitExactDepth_eq_paymentEndpoint_sub_add_one_of_mem_canonicalPaymentBlock hiblock
    have hdepthd : orbitExactDepth n i = d := by
      change orbitExactDepth n i = e - i + 1 at hdepth
      dsimp [i] at hdepth ⊢
      omega
    refine ⟨i, mem_canonicalPaymentBlockRecoveryFiber_iff.mpr ⟨hiblock, ?_⟩⟩
    simpa [OrbitDepthRecoversExactlyAt, orbitExactDepth] using hdepthd

/-- Exact local recovery cardinality, with depth zero excluded explicitly. -/
theorem canonicalPaymentBlockRecoveryFiber_card
    (n : OddNat) (k d : ℕ) :
    (canonicalPaymentBlockRecoveryFiber n k d).card =
      if 1 ≤ d ∧ d ≤ canonicalPaymentBlockLength n k then 1 else 0 := by
  by_cases hd : 1 ≤ d ∧ d ≤ canonicalPaymentBlockLength n k
  · rw [ite_eq_left hd]
    have hpos : 0 < (canonicalPaymentBlockRecoveryFiber n k d).card :=
      Finset.card_pos.mpr ((canonicalPaymentBlockRecoveryFiber_nonempty_iff n k d).2 hd)
    have hle := canonicalPaymentBlockRecoveryFiber_card_le_one n k d
    omega
  · rw [ite_eq_right hd]
    exact Finset.card_eq_zero.mpr (by
      rw [← Finset.not_nonempty_iff_eq_empty]
      simpa [canonicalPaymentBlockRecoveryFiber_nonempty_iff n k d] using hd)

/-- The explicit depth-zero recovery count is zero. -/
theorem canonicalPaymentBlockRecoveryFiber_card_zero
    (n : OddNat) (k : ℕ) :
    (canonicalPaymentBlockRecoveryFiber n k 0).card = 0 := by
  rw [canonicalPaymentBlockRecoveryFiber_zero_eq_empty]
  rfl

/-- Continuation through depth `d` is the initial interval ending `d` steps before the endpoint. -/
theorem canonicalPaymentBlockContinuationFiber_eq_Icc
    (n : OddNat) (k d : ℕ)
    (hd : d < canonicalPaymentBlockLength n k) :
    canonicalPaymentBlockContinuationFiber n k d =
      Finset.Icc
        (universalPaymentBlockStart n (paymentEndpointSeq n k)
          (orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n k))
        (paymentEndpointSeq n k - d) := by
  let e := paymentEndpointSeq n k
  let h := orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n k
  let b := universalPaymentBlockStart n e h
  have hblock : canonicalPaymentBlock n k = Finset.Icc b e := by
    simpa [e, h, b] using canonicalPaymentBlock_eq_Icc_universalPaymentBlockStart n k
  have hlength : canonicalPaymentBlockLength n k = e - b + 1 := by
    simpa [e, h, b] using
      canonicalPaymentBlockLength_eq_endpoint_sub_start_add_one n k
  ext i
  rw [mem_canonicalPaymentBlockContinuationFiber_iff]
  change (i ∈ canonicalPaymentBlock n k ∧ OrbitDepthContinuesBeyond n i d) ↔
    i ∈ Finset.Icc b (e - d)
  constructor
  · rintro ⟨hiblock, hicont⟩
    have hiIcc : i ∈ Finset.Icc b e := by simpa [hblock] using hiblock
    have hdepth :=
      orbitExactDepth_eq_paymentEndpoint_sub_add_one_of_mem_canonicalPaymentBlock hiblock
    change orbitExactDepth n i = e - i + 1 at hdepth
    have hicontDepth : d + 1 ≤ orbitExactDepth n i := by
      simpa [OrbitDepthContinuesBeyond, orbitExactDepth] using hicont
    rcases Finset.mem_Icc.mp hiIcc with ⟨hbi, hie⟩
    exact Finset.mem_Icc.mpr ⟨hbi, by omega⟩
  · intro hi
    rcases Finset.mem_Icc.mp hi with ⟨hbi, hied⟩
    have hie : i ≤ e := hied.trans (Nat.sub_le e d)
    have hiblock : i ∈ canonicalPaymentBlock n k := by
      rw [hblock]
      exact Finset.mem_Icc.mpr ⟨hbi, hie⟩
    have hdepth :=
      orbitExactDepth_eq_paymentEndpoint_sub_add_one_of_mem_canonicalPaymentBlock hiblock
    change orbitExactDepth n i = e - i + 1 at hdepth
    refine ⟨hiblock, ?_⟩
    have hicontDepth : d + 1 ≤ orbitExactDepth n i := by omega
    simpa [OrbitDepthContinuesBeyond, orbitExactDepth] using hicontDepth

/-- Exact local continuation cardinality; depth zero retains the whole block. -/
theorem canonicalPaymentBlockContinuationFiber_card
    (n : OddNat) (k d : ℕ) :
    (canonicalPaymentBlockContinuationFiber n k d).card =
      canonicalPaymentBlockLength n k - d := by
  let e := paymentEndpointSeq n k
  let h := orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n k
  let b := universalPaymentBlockStart n e h
  have hbmem := universalPaymentBlockStart_mem_sourceFiber n e h
  have hbe : b ≤ e := (mem_orbitPaymentSourceFiberAt_iff.mp hbmem).1
  have hlength : canonicalPaymentBlockLength n k = e - b + 1 := by
    simpa [e, h, b] using
      canonicalPaymentBlockLength_eq_endpoint_sub_start_add_one n k
  by_cases hd : d < canonicalPaymentBlockLength n k
  · rw [canonicalPaymentBlockContinuationFiber_eq_Icc n k d hd]
    change (Finset.Icc b (e - d)).card = canonicalPaymentBlockLength n k - d
    rw [Nat.card_Icc, hlength]
    omega
  · have hempty : canonicalPaymentBlockContinuationFiber n k d = ∅ := by
      ext i
      simp only [mem_canonicalPaymentBlockContinuationFiber_iff,
        Finset.notMem_empty, iff_false, not_and]
      intro hiblock hicont
      have hiIcc : i ∈ Finset.Icc b e := by
        rw [← canonicalPaymentBlock_eq_Icc_universalPaymentBlockStart n k]
        exact hiblock
      have hdepth :=
        orbitExactDepth_eq_paymentEndpoint_sub_add_one_of_mem_canonicalPaymentBlock hiblock
      change orbitExactDepth n i = e - i + 1 at hdepth
      have hicontDepth : d + 1 ≤ orbitExactDepth n i := by
        simpa [OrbitDepthContinuesBeyond, orbitExactDepth] using hicont
      rcases Finset.mem_Icc.mp hiIcc with ⟨hbi, hie⟩
      omega
    rw [hempty]
    simp
    omega

/-- At depth zero every source in the canonical block continues. -/
theorem canonicalPaymentBlockContinuationFiber_card_zero
    (n : OddNat) (k : ℕ) :
    (canonicalPaymentBlockContinuationFiber n k 0).card =
      canonicalPaymentBlockLength n k := by
  simpa using canonicalPaymentBlockContinuationFiber_card n k 0

/-- Signed continuation surplus over exact recovery inside one canonical block. -/
noncomputable def blockPressureContributionInt
    (n : OddNat) (k d : ℕ) : ℤ :=
  (canonicalPaymentBlockContinuationFiber n k d).card -
    (canonicalPaymentBlockRecoveryFiber n k d).card

/-- Closed form of the signed local pressure contribution. -/
theorem blockPressureContributionInt_eq
    (n : OddNat) (k d : ℕ) :
    blockPressureContributionInt n k d =
      (canonicalPaymentBlockLength n k - d : ℕ) -
        if 1 ≤ d ∧ d ≤ canonicalPaymentBlockLength n k then (1 : ℤ) else 0 := by
  unfold blockPressureContributionInt
  rw [canonicalPaymentBlockContinuationFiber_card,
    canonicalPaymentBlockRecoveryFiber_card]
  split <;> norm_num

/-- At depth zero, local pressure is the entire block length. -/
theorem blockPressureContributionInt_zero
    (n : OddNat) (k : ℕ) :
    blockPressureContributionInt n k 0 = canonicalPaymentBlockLength n k := by
  rw [blockPressureContributionInt_eq]
  norm_num

/-- Above the local staircase, both continuation and recovery are absent. -/
theorem blockPressureContributionInt_eq_zero_of_length_lt
    {n : OddNat} {k d : ℕ}
    (_hdpos : 1 ≤ d) (hlt : canonicalPaymentBlockLength n k < d) :
    blockPressureContributionInt n k d = 0 := by
  have hsub : canonicalPaymentBlockLength n k - d = 0 :=
    Nat.sub_eq_zero_of_le hlt.le
  rw [blockPressureContributionInt_eq]
  simp [hsub, Nat.not_le_of_lt hlt]

/-- At the last staircase depth, exact recovery contributes `-1`. -/
theorem blockPressureContributionInt_eq_neg_one_of_length_eq
    {n : OddNat} {k d : ℕ}
    (hdpos : 1 ≤ d) (heq : canonicalPaymentBlockLength n k = d) :
    blockPressureContributionInt n k d = -1 := by
  rw [blockPressureContributionInt_eq]
  simp [hdpos, heq]

/-- One source beyond the queried depth balances the unique recovery. -/
theorem blockPressureContributionInt_eq_zero_of_length_eq_succ
    {n : OddNat} {k d : ℕ}
    (hdpos : 1 ≤ d) (heq : canonicalPaymentBlockLength n k = d + 1) :
    blockPressureContributionInt n k d = 0 := by
  rw [blockPressureContributionInt_eq]
  simp [hdpos, heq]

/-- With at least two continuing sources, pressure is length minus depth minus recovery. -/
theorem blockPressureContributionInt_eq_sub_sub_one_of_add_two_le_length
    {n : OddNat} {k d : ℕ}
    (hdpos : 1 ≤ d) (hle : d + 2 ≤ canonicalPaymentBlockLength n k) :
    blockPressureContributionInt n k d =
      (canonicalPaymentBlockLength n k - d : ℕ) - 1 := by
  rw [blockPressureContributionInt_eq]
  simp [hdpos, show d ≤ canonicalPaymentBlockLength n k by omega]

/-- The canonical prefix through `m` is the ordinary initial range through its endpoint. -/
theorem canonicalPaymentBlockPrefix_eq_range (n : OddNat) (m : ℕ) :
    canonicalPaymentBlockPrefix n m = Finset.range (paymentEndpointSeq n m + 1) := by
  rw [canonicalPaymentBlockPrefix_eq_Icc]
  ext i
  simp

/-- A list-range Boolean count is the corresponding filtered Finset cardinality. -/
private theorem listRange_countP_decide_eq_card_filter
    (K : ℕ) (p : ℕ → Prop) [DecidablePred p] :
    (List.range K).countP (fun i => decide (p i)) =
      ((Finset.range K).filter p).card := by
  rw [List.countP_eq_length_filter]
  rw [← List.toFinset_card_of_nodup
    ((List.nodup_range (n := K)).filter fun i => decide (p i))]
  rw [List.toFinset_filter, List.toFinset_range]
  congr 1
  ext i
  simp

/-- Actual exact-recovery fiber in an ordinary initial orbit-time range. -/
noncomputable def orbitDepthRecoveryRangeFiber
    (n : OddNat) (K d : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range K).filter fun i => OrbitDepthRecoversExactlyAt n i d

/-- Actual continuation fiber in an ordinary initial orbit-time range. -/
noncomputable def orbitDepthContinuationRangeFiber
    (n : OddNat) (K d : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range K).filter fun i => OrbitDepthContinuesBeyond n i d

/-- Existing recovery count as an actual filtered initial Finset. -/
theorem orbitDepthRecoveryFiberCount_eq_card_filter_range
    (n : OddNat) (K d : ℕ) :
    orbitDepthRecoveryFiberCount n K d =
      (orbitDepthRecoveryRangeFiber n K d).card := by
  classical
  unfold orbitDepthRecoveryRangeFiber
  rw [← listRange_countP_decide_eq_card_filter]
  unfold orbitDepthRecoveryFiberCount
  apply List.countP_congr
  intro i hi
  simp only [decide_eq_true_eq]
  exact (orbitDepthRecoversExactlyAt_iff_recoverySibling n i d).symm

/-- Existing continuation count as an actual filtered initial Finset. -/
theorem orbitDepthContinuationFiberCount_eq_card_filter_range
    (n : OddNat) (K d : ℕ) :
    orbitDepthContinuationFiberCount n K d =
      (orbitDepthContinuationRangeFiber n K d).card := by
  classical
  unfold orbitDepthContinuationRangeFiber
  rw [← listRange_countP_decide_eq_card_filter]
  unfold orbitDepthContinuationFiberCount
  apply List.countP_congr
  intro i hi
  simp only [decide_eq_true_eq]
  exact (orbitDepthContinuesBeyond_iff_mod_eq_allOnes_succ n i d).symm

/-- The block prefix is disjoint from the immediately following canonical block. -/
theorem disjoint_canonicalPaymentBlockPrefix_next
    (n : OddNat) (m : ℕ) :
    Disjoint (canonicalPaymentBlockPrefix n m) (canonicalPaymentBlock n (m + 1)) := by
  rw [canonicalPaymentBlockPrefix_eq_Icc, canonicalPaymentBlock]
  rw [Finset.disjoint_left]
  intro i hi hi'
  rcases Finset.mem_Icc.mp hi with ⟨_, him⟩
  rcases Finset.mem_Icc.mp hi' with ⟨hmi, _⟩
  omega

/-- Filtering any predicate commutes with the canonical finite block partition at card level. -/
theorem card_filter_canonicalPaymentBlockPrefix_eq_sum
    (n : OddNat) (m : ℕ) (p : ℕ → Prop) [DecidablePred p] :
    ((canonicalPaymentBlockPrefix n m).filter p).card =
      ∑ k ∈ Finset.range (m + 1), ((canonicalPaymentBlock n k).filter p).card := by
  induction m with
  | zero =>
      simp [canonicalPaymentBlockPrefix]
  | succ m ih =>
      have hdisjoint : Disjoint
          ((canonicalPaymentBlockPrefix n m).filter p)
          ((canonicalPaymentBlock n (m + 1)).filter p) :=
        (disjoint_canonicalPaymentBlockPrefix_next n m).mono
          (Finset.filter_subset _ _) (Finset.filter_subset _ _)
      calc
        ((canonicalPaymentBlockPrefix n (m + 1)).filter p).card =
            (((canonicalPaymentBlockPrefix n m).filter p) ∪
              ((canonicalPaymentBlock n (m + 1)).filter p)).card := by
              rw [canonicalPaymentBlockPrefix, Finset.filter_union]
        _ = ((canonicalPaymentBlockPrefix n m).filter p).card +
              ((canonicalPaymentBlock n (m + 1)).filter p).card :=
              Finset.card_union_of_disjoint hdisjoint
        _ = (∑ k ∈ Finset.range (m + 1),
              ((canonicalPaymentBlock n k).filter p).card) +
              ((canonicalPaymentBlock n (m + 1)).filter p).card := by rw [ih]
        _ = ∑ k ∈ Finset.range (m + 1 + 1),
              ((canonicalPaymentBlock n k).filter p).card := by
              symm
              apply Finset.sum_range_succ

/-- Endpoint-aligned recovery count is the sum of canonical block recovery fibers. -/
theorem orbitDepthRecoveryFiberCount_paymentEndpointSeq_eq_sum
    (n : OddNat) (m d : ℕ) :
    orbitDepthRecoveryFiberCount n (paymentEndpointSeq n m + 1) d =
      ∑ k ∈ Finset.range (m + 1),
        (canonicalPaymentBlockRecoveryFiber n k d).card := by
  rw [orbitDepthRecoveryFiberCount_eq_card_filter_range,
    orbitDepthRecoveryRangeFiber,
    ← canonicalPaymentBlockPrefix_eq_range,
    card_filter_canonicalPaymentBlockPrefix_eq_sum]
  rfl

/-- Endpoint-aligned continuation count is the sum of canonical block continuation fibers. -/
theorem orbitDepthContinuationFiberCount_paymentEndpointSeq_eq_sum
    (n : OddNat) (m d : ℕ) :
    orbitDepthContinuationFiberCount n (paymentEndpointSeq n m + 1) d =
      ∑ k ∈ Finset.range (m + 1),
        (canonicalPaymentBlockContinuationFiber n k d).card := by
  rw [orbitDepthContinuationFiberCount_eq_card_filter_range,
    orbitDepthContinuationRangeFiber,
    ← canonicalPaymentBlockPrefix_eq_range,
    card_filter_canonicalPaymentBlockPrefix_eq_sum]
  rfl

/-- Existing source pressure is exactly the sum of canonical block contributions. -/
theorem sourcePressureMarginInt_paymentEndpointSeq_eq_sum_blockPressureContributionInt
    (n : OddNat) (m d : ℕ) :
    SourcePressureMarginInt n (paymentEndpointSeq n m + 1) d =
      ∑ k ∈ Finset.range (m + 1), blockPressureContributionInt n k d := by
  rw [sourcePressureMarginInt_eq_continuationFiber_sub_recoveryFiber,
    orbitDepthContinuationFiberCount_paymentEndpointSeq_eq_sum,
    orbitDepthRecoveryFiberCount_paymentEndpointSeq_eq_sum]
  simp_rw [blockPressureContributionInt]
  push_cast
  rw [Finset.sum_sub_distrib]

/-- Staircase depth address attached to a source in canonical block `k`. -/
noncomputable def canonicalPaymentDebtDepth (n : OddNat) (k i : ℕ) : ℕ :=
  paymentEndpointSeq n k - i + 1

/-- Every delayed debt source at endpoint `k` has its exact staircase depth address. -/
theorem canonicalPaymentDebtDepth_eq_orbitExactDepth_of_mem_growthDebt
    {n : OddNat} {k i : ℕ}
    (hi : i ∈ floatGrowthDebtFiberAt n (paymentEndpointSeq n k)) :
    canonicalPaymentDebtDepth n k i = orbitExactDepth n i := by
  have hiblock : i ∈ canonicalPaymentBlock n k := by
    rw [canonicalPaymentBlock_eq_sourceFiber]
    exact mem_orbitPaymentSourceFiberAt_of_mem_floatGrowthDebtFiberAt hi
  rw [orbitExactDepth_eq_paymentEndpoint_sub_add_one_of_mem_canonicalPaymentBlock hiblock]
  rfl

/-- Distinct delayed debt sources in one block receive distinct depth addresses. -/
theorem injective_canonicalPaymentDebtDepth_on_growthDebtFiber
    (n : OddNat) (k : ℕ) :
    Set.InjOn (canonicalPaymentDebtDepth n k)
      (floatGrowthDebtFiberAt n (paymentEndpointSeq n k)) := by
  intro i hi i' hi' heq
  have hil := lt_of_mem_floatGrowthDebtFiberAt hi
  have hi'l := lt_of_mem_floatGrowthDebtFiberAt hi'
  unfold canonicalPaymentDebtDepth at heq
  omega

/-- Actual marked depth addresses of delayed debts in canonical block `k`. -/
noncomputable def canonicalPaymentMarkedDebtDepths
    (n : OddNat) (k : ℕ) : Finset ℕ :=
  (floatGrowthDebtFiberAt n (paymentEndpointSeq n k)).image
    (canonicalPaymentDebtDepth n k)

/-- Delayed debt multiplicity is exactly marked staircase-depth multiplicity. -/
theorem canonicalPaymentMarkedDebtDepths_card
    (n : OddNat) (k : ℕ) :
    (canonicalPaymentMarkedDebtDepths n k).card =
      (floatGrowthDebtFiberAt n (paymentEndpointSeq n k)).card := by
  unfold canonicalPaymentMarkedDebtDepths
  rw [Finset.card_image_iff.mpr]
  exact injective_canonicalPaymentDebtDepth_on_growthDebtFiber n k

/-- Actual capacity slots exposed by canonical endpoint `k`. -/
noncomputable def canonicalEndpointCapacitySlots
    (n : OddNat) (k : ℕ) : Finset ℕ :=
  Finset.range (extraPaymentCapacityAt n (paymentEndpointSeq n k))

/-- The capacity-slot carrier has exactly the endpoint's extra capacity. -/
theorem canonicalEndpointCapacitySlots_card
    (n : OddNat) (k : ℕ) :
    (canonicalEndpointCapacitySlots n k).card =
      extraPaymentCapacityAt n (paymentEndpointSeq n k) := by
  simp [canonicalEndpointCapacitySlots]

/-- Total delayed and immediate claims through canonical endpoint `m`. -/
noncomputable def cumulativeCanonicalEndpointClaims
    (n : OddNat) (m : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (m + 1),
    ((floatGrowthDebtFiberAt n (paymentEndpointSeq n k)).card +
      (endpointImmediateCarryTwoClaimFiberAt n (paymentEndpointSeq n k)).card)

/-- Total endpoint capacity through canonical endpoint `m`. -/
noncomputable def cumulativeCanonicalEndpointCapacity
    (n : OddNat) (m : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (m + 1),
    (canonicalEndpointCapacitySlots n k).card

/-- Cumulative accounting term is claims minus capacity. -/
theorem sum_endpointAccountingTerm_eq_claims_sub_capacity
    (n : OddNat) (m : ℕ) :
    (∑ k ∈ Finset.range (m + 1), endpointAccountingTerm n k) =
      (cumulativeCanonicalEndpointClaims n m : ℤ) -
        cumulativeCanonicalEndpointCapacity n m := by
  unfold endpointAccountingTerm cumulativeCanonicalEndpointClaims
    cumulativeCanonicalEndpointCapacity
  simp_rw [canonicalEndpointCapacitySlots_card]
  push_cast
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]

/-- Prefix Hall condition: every initial endpoint family has enough cumulative capacity. -/
def CanonicalEndpointPrefixCapacityDominance
    (n : OddNat) (m : ℕ) : Prop :=
  ∀ q, q ≤ m →
    cumulativeCanonicalEndpointClaims n q ≤ cumulativeCanonicalEndpointCapacity n q

/-- The finite Hall frontier is exactly nonpositivity of every accounting prefix. -/
theorem canonicalEndpointPrefixCapacityDominance_iff_accounting_nonpos
    (n : OddNat) (m : ℕ) :
    CanonicalEndpointPrefixCapacityDominance n m ↔
      ∀ q, q ≤ m →
        (∑ k ∈ Finset.range (q + 1), endpointAccountingTerm n k) ≤ 0 := by
  constructor
  · intro h q hqm
    rw [sum_endpointAccountingTerm_eq_claims_sub_capacity]
    exact sub_nonpos.mpr (Int.ofNat_le.mpr (h q hqm))
  · intro h q hqm
    have hq := h q hqm
    rw [sum_endpointAccountingTerm_eq_claims_sub_capacity] at hq
    exact Int.ofNat_le.mp (sub_nonpos.mp hq)

/-- A claim is identified by its block and source time. -/
def CanonicalEndpointClaimCarrier
    (n : OddNat) (m : ℕ) :=
  {p : Fin (m + 1) × ℕ //
    p.2 ∈ floatGrowthDebtFiberAt n (paymentEndpointSeq n p.1.val) ∨
      p.2 ∈ endpointImmediateCarryTwoClaimFiberAt n (paymentEndpointSeq n p.1.val)}

/-- A capacity slot is identified by its endpoint block and local slot. -/
def CanonicalEndpointCapacityCarrier
    (n : OddNat) (m : ℕ) :=
  {p : Fin (m + 1) × ℕ // p.2 ∈ canonicalEndpointCapacitySlots n p.1.val}

/--
The honest finite matching target. A claim may use a capacity slot at its own
endpoint or an earlier endpoint in the selected prefix. Existence is deliberately not asserted:
constructing this ordered injection is the remaining structural sign problem.
-/
def CanonicalEndpointOrderedCapacityMatching
    (n : OddNat) (m : ℕ) : Prop :=
  ∃ pay : CanonicalEndpointClaimCarrier n m → CanonicalEndpointCapacityCarrier n m,
    Function.Injective pay ∧ ∀ claim, (pay claim).val.1.val ≤ claim.val.1.val

/-- Prefix capacity dominance conditionally bounds bit width at the selected endpoint. -/
theorem bitWidth_paymentEndpointSeq_le_initial_of_prefixCapacityDominance
    {n : OddNat} {m : ℕ}
    (h : CanonicalEndpointPrefixCapacityDominance n m) :
    bitWidth (iterateT (paymentEndpointSeq n m + 1) n).1 ≤ bitWidth n.1 := by
  have hnonpos :=
    (canonicalEndpointPrefixCapacityDominance_iff_accounting_nonpos n m).mp h m le_rfl
  rw [sum_endpointAccountingTerm_paymentEndpointSeq] at hnonpos
  omega

/-- Global version of the still-open cumulative capacity dominance condition. -/
def CanonicalEndpointCapacityDominance (n : OddNat) : Prop :=
  ∀ m, CanonicalEndpointPrefixCapacityDominance n m

/-- Global capacity dominance conditionally bounds every canonical endpoint width. -/
theorem bitWidth_paymentEndpointSeq_le_initial_of_capacityDominance
    {n : OddNat} (h : CanonicalEndpointCapacityDominance n) (m : ℕ) :
    bitWidth (iterateT (paymentEndpointSeq n m + 1) n).1 ≤ bitWidth n.1 :=
  bitWidth_paymentEndpointSeq_le_initial_of_prefixCapacityDominance (h m)

/-!
## Exact stopping point

All finite reindexing, block-local depth counting, and pressure summation are
now closed. The next theorem cannot be obtained by another cardinality rewrite:
one must construct `CanonicalEndpointOrderedCapacityMatching`, or prove the
equivalent prefix-capacity dominance by a structural rule. The conditional bit
width bound above is boundedness at canonical endpoints only. It is not a
convergence theorem; strict decay or a rigidity classification of zero-drift
families remains separate.
-/

end DkMath.Collatz
