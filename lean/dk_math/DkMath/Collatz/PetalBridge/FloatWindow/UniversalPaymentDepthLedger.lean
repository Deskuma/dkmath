/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentRepayment

#print "file: DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentDepthLedger"

namespace DkMath.Collatz

/-!
# Window repayment and depth ledgers

This module distinguishes two finite statements:

* a fixed old claim prefix embeds into a larger future slot prefix;
* all claims born in a window `q..r` are paid by slots born in that same window.

Only the second statement certifies repayment of that window's balance drift.
No general depth eligibility relation is assumed here.
-/

/-! ## Exact excursion identities -/

/-- Balance immediately before block `q` is its block-start width drift. -/
theorem canonicalEndpointBalanceBefore_eq_bitWidth_sub
    (n : OddNat) (q : ℕ) :
    canonicalEndpointBalanceBefore n q =
      (bitWidth (iterateT (canonicalEndpointBlockStart n q) n).1 : ℤ) - bitWidth n.1 := by
  cases q with
  | zero => simp [canonicalEndpointBalanceBefore, canonicalEndpointBlockStart, iterateT]
  | succ q =>
      rw [canonicalEndpointBalanceBefore, canonicalEndpointBalanceInt_eq_bitWidth_sub]
      rfl

/-- A positive excursion at `q` is exactly a positive drift of block `q`. -/
theorem canonicalEndpointPositiveExcursionAt_iff_accountingTerm_pos
    (n : OddNat) (q : ℕ) :
    CanonicalEndpointPositiveExcursionAt n q ↔ 0 < endpointAccountingTerm n q := by
  unfold CanonicalEndpointPositiveExcursionAt
  cases q with
  | zero =>
      simp [canonicalEndpointBalanceBefore, canonicalEndpointBalanceInt]
  | succ q =>
      simp only [canonicalEndpointBalanceBefore, canonicalEndpointBalanceInt]
      rw [show ∑ k ∈ Finset.range (q + 1 + 1), endpointAccountingTerm n k =
          (∑ k ∈ Finset.range (q + 1), endpointAccountingTerm n k) +
            endpointAccountingTerm n (q + 1) by
        simp [Finset.sum_range_succ]]
      omega

/-- A window drift is the difference between its terminal and prior balances. -/
theorem sum_endpointAccountingTerm_Icc_eq_balance_sub_before
    (n : OddNat) {q r : ℕ} (hqr : q ≤ r) :
    (∑ k ∈ Finset.Icc q r, endpointAccountingTerm n k) =
      canonicalEndpointBalanceInt n r - canonicalEndpointBalanceBefore n q := by
  rw [sum_endpointAccountingTerm_Icc_eq_bitWidth_sub n hqr,
    canonicalEndpointBalanceInt_eq_bitWidth_sub,
    canonicalEndpointBalanceBefore_eq_bitWidth_sub]
  omega

/-- Repayment at `r` is exactly nonpositive signed drift over `q..r`. -/
theorem canonicalEndpointExcursionRepaidAt_iff_window_sum_nonpos
    (n : OddNat) {q r : ℕ} (hqr : q ≤ r) :
    CanonicalEndpointExcursionRepaidAt n q r ↔
      (∑ k ∈ Finset.Icc q r, endpointAccountingTerm n k) ≤ 0 := by
  rw [sum_endpointAccountingTerm_Icc_eq_balance_sub_before n hqr]
  unfold CanonicalEndpointExcursionRepaidAt
  constructor
  · exact fun h => sub_nonpos.mpr h.2
  · exact fun h => ⟨hqr, sub_nonpos.mp h⟩

/-- Claims born in the selected canonical block window. -/
noncomputable def canonicalEndpointWindowClaims
    (n : OddNat) (q r : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc q r,
    ((floatGrowthDebtFiberAt n (paymentEndpointSeq n k)).card +
      (endpointImmediateCarryTwoClaimFiberAt n (paymentEndpointSeq n k)).card)

/-- Capacity born in the selected canonical block window. -/
noncomputable def canonicalEndpointWindowCapacity
    (n : OddNat) (q r : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc q r, extraPaymentCapacityAt n (paymentEndpointSeq n k)

/-- Exact claims-versus-capacity criterion for repayment of a block window. -/
theorem canonicalEndpointExcursionRepaidAt_iff_windowClaims_le_capacity
    (n : OddNat) {q r : ℕ} (hqr : q ≤ r) :
    CanonicalEndpointExcursionRepaidAt n q r ↔
      canonicalEndpointWindowClaims n q r ≤ canonicalEndpointWindowCapacity n q r := by
  rw [canonicalEndpointExcursionRepaidAt_iff_window_sum_nonpos n hqr]
  rw [sum_endpointAccountingTerm_Icc_eq_claims_sub_capacity n hqr]
  unfold canonicalEndpointWindowClaims canonicalEndpointWindowCapacity
  rw [sub_nonpos]
  constructor <;> intro h <;> exact_mod_cast h

/-! ## Actual finite window carriers -/

/-- Claims identified by a block in `q..r` and a source in its complete claim fiber. -/
def CanonicalEndpointClaimWindowCarrier
    (n : OddNat) (q r : ℕ) :=
  Σ k : {k : ℕ // k ∈ Finset.Icc q r},
    {i : ℕ // i ∈ carryTwoPaymentClaimFiberAt n (paymentEndpointSeq n k.val)}

/-- Capacity slots identified by a block in `q..r` and its local zero-based slot. -/
def CanonicalEndpointCapacityWindowCarrier
    (n : OddNat) (q r : ℕ) :=
  Σ k : {k : ℕ // k ∈ Finset.Icc q r},
    {s : ℕ // s ∈ canonicalEndpointCapacitySlots n k.val}

/-- Exact cardinality of the complete claim window carrier. -/
theorem natCard_canonicalEndpointClaimWindowCarrier
    (n : OddNat) (q r : ℕ) :
    Nat.card (CanonicalEndpointClaimWindowCarrier n q r) =
      canonicalEndpointWindowClaims n q r := by
  unfold CanonicalEndpointClaimWindowCarrier
  rw [Nat.card_sigma]
  simp_rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  rw [Finset.univ_eq_attach]
  calc
    ∑ x ∈ (Finset.Icc q r).attach,
        (carryTwoPaymentClaimFiberAt n (paymentEndpointSeq n x.val)).card =
        ∑ k ∈ Finset.Icc q r,
          (carryTwoPaymentClaimFiberAt n (paymentEndpointSeq n k)).card :=
      Finset.sum_attach (Finset.Icc q r) fun k =>
        (carryTwoPaymentClaimFiberAt n (paymentEndpointSeq n k)).card
    _ = canonicalEndpointWindowClaims n q r := by
      unfold canonicalEndpointWindowClaims
      apply Finset.sum_congr rfl
      intro k hk
      exact carryTwoPaymentClaimFiberAt_card_eq_growthDebt_card_add_endpoint_card
        n (paymentEndpointSeq n k)
          (orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n k)

/-- Exact cardinality of the capacity window carrier. -/
theorem natCard_canonicalEndpointCapacityWindowCarrier
    (n : OddNat) (q r : ℕ) :
    Nat.card (CanonicalEndpointCapacityWindowCarrier n q r) =
      canonicalEndpointWindowCapacity n q r := by
  unfold CanonicalEndpointCapacityWindowCarrier
  rw [Nat.card_sigma]
  simp_rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  rw [Finset.univ_eq_attach]
  calc
    ∑ x ∈ (Finset.Icc q r).attach,
        (canonicalEndpointCapacitySlots n x.val).card =
        ∑ k ∈ Finset.Icc q r, (canonicalEndpointCapacitySlots n k).card :=
      Finset.sum_attach (Finset.Icc q r) fun k =>
        (canonicalEndpointCapacitySlots n k).card
    _ = canonicalEndpointWindowCapacity n q r := by
      unfold canonicalEndpointWindowCapacity
      apply Finset.sum_congr rfl
      intro k hk
      exact canonicalEndpointCapacitySlots_card n k

/--
All claims born in `q..r` are injected into slots born in `q..r`, without
paying a claim before its own block.
-/
def CanonicalEndpointForwardWindowMatching
    (n : OddNat) (q r : ℕ) : Prop :=
  q ≤ r ∧
    ∃ pay : CanonicalEndpointClaimWindowCarrier n q r →
        CanonicalEndpointCapacityWindowCarrier n q r,
      Function.Injective pay ∧ ∀ claim, claim.1.val ≤ (pay claim).1.val

/-- A forward window matching certifies repayment of that same window. -/
theorem CanonicalEndpointForwardWindowMatching.to_excursionRepaidAt
    {n : OddNat} {q r : ℕ}
    (h : CanonicalEndpointForwardWindowMatching n q r) :
    CanonicalEndpointExcursionRepaidAt n q r := by
  rcases h with ⟨hqr, pay, hpay, _⟩
  letI : Finite (CanonicalEndpointCapacityWindowCarrier n q r) := by
    unfold CanonicalEndpointCapacityWindowCarrier
    infer_instance
  have hcard := Nat.card_le_card_of_injective pay hpay
  rw [natCard_canonicalEndpointClaimWindowCarrier,
    natCard_canonicalEndpointCapacityWindowCarrier] at hcard
  exact (canonicalEndpointExcursionRepaidAt_iff_windowClaims_le_capacity n hqr).2 hcard

/-! ## Scalar depth ledger -/

/-- Semantic alias: endpoint capacity coordinates are levels, not recovery depths. -/
noncomputable abbrev canonicalEndpointCapacityLevelSlots :=
  canonicalEndpointCapacityDepthSlots

/-- Claim incidence minus capacity incidence at one numeric depth/level coordinate. -/
noncomputable def canonicalDepthAccountingTerm
    (n : OddNat) (k d : ℕ) : ℤ := by
  classical
  exact (if d ∈ canonicalPaymentClaimDepths n k then 1 else 0) -
    if d ∈ canonicalEndpointCapacityLevelSlots n k then 1 else 0

/-- Finite support containing every claim depth and capacity level of block `k`. -/
noncomputable def canonicalDepthAccountingSupport
    (n : OddNat) (k : ℕ) : Finset ℕ :=
  canonicalPaymentClaimDepths n k ∪ canonicalEndpointCapacityLevelSlots n k

/-- Endpoint drift is exactly the sum of its scalar depth ledger. -/
theorem endpointAccountingTerm_eq_sum_canonicalDepthAccountingTerm
    (n : OddNat) (k : ℕ) :
    endpointAccountingTerm n k =
      ∑ d ∈ canonicalDepthAccountingSupport n k,
        canonicalDepthAccountingTerm n k d := by
  classical
  unfold canonicalDepthAccountingTerm canonicalDepthAccountingSupport
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_boole]
  have hclaimFilter :
      (canonicalPaymentClaimDepths n k ∪ canonicalEndpointCapacityLevelSlots n k).filter
        (· ∈ canonicalPaymentClaimDepths n k) = canonicalPaymentClaimDepths n k := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_union]
    tauto
  have hcapacityFilter :
      (canonicalPaymentClaimDepths n k ∪ canonicalEndpointCapacityLevelSlots n k).filter
        (· ∈ canonicalEndpointCapacityLevelSlots n k) =
          canonicalEndpointCapacityLevelSlots n k := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_union]
    tauto
  rw [hclaimFilter, hcapacityFilter, canonicalPaymentClaimDepths_card,
    canonicalEndpointCapacityDepthSlots_card]
  rfl

/-- Family accounting is the iterated sum of the block-local scalar ledgers. -/
theorem sum_endpointAccountingTerm_eq_sum_depthLedger
    (n : OddNat) (m : ℕ) :
    (∑ k ∈ Finset.range (m + 1), endpointAccountingTerm n k) =
      ∑ k ∈ Finset.range (m + 1),
        ∑ d ∈ canonicalDepthAccountingSupport n k,
          canonicalDepthAccountingTerm n k d := by
  apply Finset.sum_congr rfl
  intro k hk
  exact endpointAccountingTerm_eq_sum_canonicalDepthAccountingTerm n k

/-! ## Proof-independent depth and level carriers -/

/-- Complete claims through `m`, addressed by block and recovery depth. -/
def CanonicalEndpointDepthClaimCarrier
    (n : OddNat) (m : ℕ) :=
  Σ k : Fin (m + 1), {d : ℕ // d ∈ canonicalPaymentClaimDepths n k.val}

/-- Capacity through `m`, addressed by block and positive capacity level. -/
def CanonicalEndpointLevelCapacityCarrier
    (n : OddNat) (m : ℕ) :=
  Σ k : Fin (m + 1),
    {l : ℕ // l ∈ canonicalEndpointCapacityLevelSlots n k.val}

/-- Depth-addressed claim carrier has exactly the cumulative claim count. -/
theorem natCard_canonicalEndpointDepthClaimCarrier
    (n : OddNat) (m : ℕ) :
    Nat.card (CanonicalEndpointDepthClaimCarrier n m) =
      cumulativeCanonicalEndpointClaims n m := by
  unfold CanonicalEndpointDepthClaimCarrier
  rw [Nat.card_sigma]
  simp_rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  rw [Finset.sum_fin_eq_sum_range]
  unfold cumulativeCanonicalEndpointClaims
  apply Finset.sum_congr rfl
  intro k hk
  rw [dif_pos (Finset.mem_range.mp hk), canonicalPaymentClaimDepths_card]

/-- Level-addressed capacity carrier has exactly the cumulative capacity count. -/
theorem natCard_canonicalEndpointLevelCapacityCarrier
    (n : OddNat) (m : ℕ) :
    Nat.card (CanonicalEndpointLevelCapacityCarrier n m) =
      cumulativeCanonicalEndpointCapacity n m := by
  unfold CanonicalEndpointLevelCapacityCarrier
  rw [Nat.card_sigma]
  simp_rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  rw [Finset.sum_fin_eq_sum_range]
  unfold cumulativeCanonicalEndpointCapacity
  apply Finset.sum_congr rfl
  intro k hk
  rw [dif_pos (Finset.mem_range.mp hk),
    canonicalEndpointCapacityDepthSlots_card, canonicalEndpointCapacitySlots_card]

/-- Source-time claims mapped to their exact canonical recovery depths. -/
noncomputable def canonicalEndpointClaimToDepth
    (n : OddNat) (m : ℕ) :
    CanonicalEndpointClaimCarrier n m → CanonicalEndpointDepthClaimCarrier n m :=
  fun claim => ⟨claim.val.1,
    canonicalPaymentDebtDepth n claim.val.1.val claim.val.2,
    by
      rw [canonicalPaymentClaimDepths_eq_image_completeClaimFiber]
      apply Finset.mem_image.mpr
      exact ⟨claim.val.2,
        (mem_carryTwoPaymentClaimFiberAt_iff_growthDebt_or_endpointImmediate
          (h := orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n claim.val.1.val)).2
          claim.property,
        rfl⟩⟩

/-- Source-time and recovery-depth claim carriers are equivalent. -/
noncomputable def canonicalEndpointClaimCarrierEquivDepthClaimCarrier
    (n : OddNat) (m : ℕ) :
    CanonicalEndpointClaimCarrier n m ≃ CanonicalEndpointDepthClaimCarrier n m :=
  Equiv.ofBijective (canonicalEndpointClaimToDepth n m) ⟨by
    intro a b hab
    have hblock : a.val.1 = b.val.1 := congrArg Sigma.fst hab
    have hdepth : canonicalPaymentDebtDepth n a.val.1.val a.val.2 =
        canonicalPaymentDebtDepth n b.val.1.val b.val.2 := by
      exact congrArg (fun claim => claim.2.val) hab
    apply Subtype.ext
    apply Prod.ext hblock
    unfold canonicalPaymentDebtDepth at hdepth
    have haClaim :=
      (mem_carryTwoPaymentClaimFiberAt_iff_growthDebt_or_endpointImmediate
        (h := orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n a.val.1.val)).2
        a.property
    have hbClaim :=
      (mem_carryTwoPaymentClaimFiberAt_iff_growthDebt_or_endpointImmediate
        (h := orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n b.val.1.val)).2
        b.property
    have hale := (Finset.mem_Icc.mp
      ((mem_carryTwoPaymentClaimFiberAt_iff_mem_universalPaymentBlock_and_carryTwo
        (h := orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n a.val.1.val)).1
        haClaim).1).2
    have hble := (Finset.mem_Icc.mp
      ((mem_carryTwoPaymentClaimFiberAt_iff_mem_universalPaymentBlock_and_carryTwo
        (h := orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n b.val.1.val)).1
        hbClaim).1).2
    have hendpoint : paymentEndpointSeq n a.val.1.val =
        paymentEndpointSeq n b.val.1.val := by rw [hblock]
    omega,
  by
    intro depth
    have hdepthMem : depth.2.val ∈
        (carryTwoPaymentClaimFiberAt n (paymentEndpointSeq n depth.1.val)).image
          (canonicalPaymentDebtDepth n depth.1.val) := by
      rw [← canonicalPaymentClaimDepths_eq_image_completeClaimFiber]
      exact depth.2.property
    rcases Finset.mem_image.mp hdepthMem with ⟨i, hiClaim, hiDepth⟩
    refine ⟨⟨⟨depth.1, i⟩,
      (mem_carryTwoPaymentClaimFiberAt_iff_growthDebt_or_endpointImmediate
        (h := orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n depth.1.val)).1
        hiClaim⟩, ?_⟩
    exact Sigma.ext rfl (heq_of_eq (Subtype.ext hiDepth))⟩

/-- Zero-based capacity slots mapped to their positive endpoint levels. -/
noncomputable def canonicalEndpointCapacityToLevel
    (n : OddNat) (m : ℕ) :
    CanonicalEndpointCapacityCarrier n m → CanonicalEndpointLevelCapacityCarrier n m :=
  fun slot => ⟨slot.val.1, slot.val.2 + 2, by
    rw [canonicalEndpointCapacityLevelSlots, canonicalEndpointCapacityDepthSlots]
    have hslt : slot.val.2 <
        extraPaymentCapacityAt n (paymentEndpointSeq n slot.val.1.val) := by
      simpa [canonicalEndpointCapacitySlots] using slot.property
    have hheight := two_le_orbitWindowHeight_paymentEndpointSeq n slot.val.1.val
    unfold extraPaymentCapacityAt at hslt
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩

/-- The zero-based and level-addressed endpoint-capacity carriers are equivalent. -/
noncomputable def canonicalEndpointCapacityCarrierEquivLevelCapacityCarrier
    (n : OddNat) (m : ℕ) :
    CanonicalEndpointCapacityCarrier n m ≃ CanonicalEndpointLevelCapacityCarrier n m :=
  Equiv.ofBijective (canonicalEndpointCapacityToLevel n m) ⟨by
    intro a b hab
    have hblock : a.val.1 = b.val.1 := congrArg Sigma.fst hab
    have hslot : a.val.2 + 2 = b.val.2 + 2 :=
      congrArg (fun slot => slot.2.val) hab
    apply Subtype.ext
    exact Prod.ext hblock (by omega),
  by
    intro level
    rcases level with ⟨k, level⟩
    have hlevel : level.val ∈
        canonicalEndpointCapacityDepthSlots n k.val := level.property
    rw [canonicalEndpointCapacityDepthSlots] at hlevel
    rcases Finset.mem_Icc.mp hlevel with ⟨hlevelTwo, hlevelHeight⟩
    have hheight := two_le_orbitWindowHeight_paymentEndpointSeq n k.val
    refine ⟨⟨⟨k, level.val - 2⟩, ?_⟩, ?_⟩
    · change level.val - 2 ∈ canonicalEndpointCapacitySlots n k.val
      rw [canonicalEndpointCapacitySlots, Finset.mem_range]
      unfold extraPaymentCapacityAt
      omega
    · unfold canonicalEndpointCapacityToLevel
      apply Sigma.ext_iff.mpr
      constructor
      · rfl
      · apply heq_of_eq
        apply Subtype.ext
        change level.val - 2 + 2 = level.val
        omega⟩

/-! ## Exact depth regression for the orbit from seven -/

section SevenDepthRegression

private def sevenDepthOdd : OddNat := mkOddNat 7 (by decide)

/-- Public root used by the exact seven depth and scalar repayment regressions. -/
def sevenDepthRegressionRoot : OddNat := sevenDepthOdd

private lemma sevenDepth_v2_22 : v2 22 = 1 := by
  have h := (DkMath.ABC.padic_val_two_of_even 11).2 (by decide)
  simpa [v2, v2_odd 11 (by decide)] using h

private lemma sevenDepth_v2_34 : v2 34 = 1 := by
  have h := (DkMath.ABC.padic_val_two_of_even 17).2 (by decide)
  simpa [v2, v2_odd 17 (by decide)] using h

private lemma sevenDepth_v2_52 : v2 52 = 2 := by
  have h26 := (DkMath.ABC.padic_val_two_of_even 13).2 (by decide)
  have h52 := (DkMath.ABC.padic_val_two_of_even 26).2 (by decide)
  have hv13 : v2 13 = 0 := v2_odd 13 (by decide)
  have hv26 : v2 26 = 1 := by simpa [v2, hv13] using h26
  simpa [v2, hv26] using h52

private lemma sevenDepth_v2_40 : v2 40 = 3 := by
  have h10 := (DkMath.ABC.padic_val_two_of_even 5).2 (by decide)
  have h20 := (DkMath.ABC.padic_val_two_of_even 10).2 (by decide)
  have h40 := (DkMath.ABC.padic_val_two_of_even 20).2 (by decide)
  have hv5 : v2 5 = 0 := v2_odd 5 (by decide)
  have hv10 : v2 10 = 1 := by simpa [v2, hv5] using h10
  have hv20 : v2 20 = 2 := by simpa [v2, hv10] using h20
  simpa [v2, hv20] using h40

private lemma sevenDepth_v2_8 : v2 8 = 3 := by
  have h4 := (DkMath.ABC.padic_val_two_of_even 2).2 (by decide)
  have h8 := (DkMath.ABC.padic_val_two_of_even 4).2 (by decide)
  have hv2 : v2 2 = 1 := by
    have h := (DkMath.ABC.padic_val_two_of_even 1).2 (by decide)
    simp [v2]
  have hv4 : v2 4 = 2 := by simpa [v2, hv2] using h4
  simpa [v2, hv4] using h8

private lemma sevenDepth_v2_14 : v2 14 = 1 := by
  have h := (DkMath.ABC.padic_val_two_of_even 7).2 (by decide)
  simpa [v2, v2_odd 7 (by decide)] using h

private theorem sevenDepth_endpoint_zero : paymentEndpointSeq sevenDepthOdd 0 = 2 := by
  norm_num [paymentEndpointSeq, orbitPaymentTarget, orbitExactDepth,
    ResidualAllOnesDepth, oddOrbitLabel, iterateT, sevenDepthOdd, mkOddNat,
    sevenDepth_v2_8]

private theorem sevenDepth_endpoint_one : paymentEndpointSeq sevenDepthOdd 1 = 3 := by
  rw [show paymentEndpointSeq sevenDepthOdd 1 =
    orbitPaymentTarget sevenDepthOdd (paymentEndpointSeq sevenDepthOdd 0 + 1) by rfl]
  rw [sevenDepth_endpoint_zero]
  norm_num [orbitPaymentTarget, orbitExactDepth, ResidualAllOnesDepth, oddOrbitLabel,
    iterateT, T, sevenDepthOdd, mkOddNat, threeNPlusOne, pow2,
    sevenDepth_v2_22, sevenDepth_v2_34, sevenDepth_v2_52, sevenDepth_v2_14]

private theorem sevenDepth_blockLength_zero :
    canonicalPaymentBlockLength sevenDepthOdd 0 = 3 := by
  rw [canonicalPaymentBlockLength_eq_endpoint_sub_start_add_one,
    universalPaymentBlockStart_paymentEndpointSeq_zero, sevenDepth_endpoint_zero]

private theorem sevenDepth_blockLength_one :
    canonicalPaymentBlockLength sevenDepthOdd 1 = 1 := by
  rw [canonicalPaymentBlockLength_eq_endpoint_sub_start_add_one,
    universalPaymentBlockStart_paymentEndpointSeq_succ,
    sevenDepth_endpoint_zero, sevenDepth_endpoint_one]

private theorem sevenDepth_carry_zero : CarryTwoDebtAt sevenDepthOdd 0 := by
  norm_num [CarryTwoDebtAt, stateUpperCarry, upperCarry3n1, bitWidth,
    iterateT, sevenDepthOdd, mkOddNat]

private theorem sevenDepth_carry_one : CarryTwoDebtAt sevenDepthOdd 1 := by
  norm_num [CarryTwoDebtAt, stateUpperCarry, upperCarry3n1, bitWidth,
    iterateT, T, sevenDepthOdd, mkOddNat, threeNPlusOne, pow2,
    sevenDepth_v2_22]

private theorem sevenDepth_not_carry_two : ¬ CarryTwoDebtAt sevenDepthOdd 2 := by
  norm_num [CarryTwoDebtAt, stateUpperCarry, upperCarry3n1, bitWidth,
    iterateT, T, sevenDepthOdd, mkOddNat, threeNPlusOne, pow2,
    sevenDepth_v2_22, sevenDepth_v2_34]

private theorem sevenDepth_carry_three : CarryTwoDebtAt sevenDepthOdd 3 := by
  norm_num [CarryTwoDebtAt, stateUpperCarry, upperCarry3n1, bitWidth,
    iterateT, T, sevenDepthOdd, mkOddNat, threeNPlusOne, pow2,
    sevenDepth_v2_22, sevenDepth_v2_34, sevenDepth_v2_52]

/-- The first seven-regression block has delayed claim depths two and three. -/
theorem canonicalPaymentClaimDepths_seven_zero :
    canonicalPaymentClaimDepths sevenDepthOdd 0 = {2, 3} := by
  classical
  ext d
  rw [mem_canonicalPaymentClaimDepths_iff]
  rw [sevenDepth_blockLength_zero]
  unfold canonicalPaymentSourceAtDepth
  rw [sevenDepth_endpoint_zero]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hd1, hd3, hcarry⟩
    interval_cases d <;>
      simp_all [sevenDepth_carry_zero, sevenDepth_carry_one,
        sevenDepth_not_carry_two]
  · rintro (rfl | rfl) <;>
      simp [sevenDepth_carry_zero, sevenDepth_carry_one]

/-- The first seven-regression endpoint exposes only capacity level two. -/
theorem canonicalEndpointCapacityLevelSlots_seven_zero :
    canonicalEndpointCapacityLevelSlots sevenDepthOdd 0 = {2} := by
  classical
  rw [canonicalEndpointCapacityLevelSlots, canonicalEndpointCapacityDepthSlots,
    sevenDepth_endpoint_zero]
  norm_num [orbitWindowHeight_eq_s_iterateT, s, iterateT, T, sevenDepthOdd,
    mkOddNat, threeNPlusOne, pow2, sevenDepth_v2_22, sevenDepth_v2_34,
    sevenDepth_v2_52]

/-- The second seven-regression block has only its immediate depth-one claim. -/
theorem canonicalPaymentClaimDepths_seven_one :
    canonicalPaymentClaimDepths sevenDepthOdd 1 = {1} := by
  classical
  ext d
  rw [mem_canonicalPaymentClaimDepths_iff]
  rw [sevenDepth_blockLength_one]
  unfold canonicalPaymentSourceAtDepth
  rw [sevenDepth_endpoint_one]
  simp only [Finset.mem_singleton]
  constructor
  · rintro ⟨hd1, hdle, hcarry⟩
    omega
  · rintro rfl
    simp [sevenDepth_carry_three]

/-- The second seven-regression endpoint exposes capacity levels two and three. -/
theorem canonicalEndpointCapacityLevelSlots_seven_one :
    canonicalEndpointCapacityLevelSlots sevenDepthOdd 1 = {2, 3} := by
  classical
  rw [canonicalEndpointCapacityLevelSlots, canonicalEndpointCapacityDepthSlots,
    sevenDepth_endpoint_one]
  norm_num [orbitWindowHeight_eq_s_iterateT, s, iterateT, T, sevenDepthOdd,
    mkOddNat, threeNPlusOne, pow2, sevenDepth_v2_22, sevenDepth_v2_34,
    sevenDepth_v2_52, sevenDepth_v2_40]
  ext d
  simp
  omega

/-- One concrete claim-to-capacity assignment entry. -/
def CanonicalDepthAllocationEntry
    (n : OddNat) (entry : (ℕ × ℕ) × (ℕ × ℕ)) : Prop :=
  entry.1.2 ∈ canonicalPaymentClaimDepths n entry.1.1 ∧
    entry.2.2 ∈ canonicalEndpointCapacityLevelSlots n entry.2.1 ∧
      entry.1.1 ≤ entry.2.1

/-- The explicit three-claim repayment allocation for the first two blocks from seven. -/
private def sevenDepthAllocation : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  {((0, 2), (0, 2)), ((0, 3), (1, 3)), ((1, 1), (1, 2))}

/-- Every entry of the concrete seven allocation is valid and forward in time. -/
theorem sevenDepthAllocation_valid :
    ∀ entry ∈ sevenDepthAllocation,
      CanonicalDepthAllocationEntry sevenDepthOdd entry := by
  intro entry hentry
  simp only [sevenDepthAllocation, Finset.mem_insert, Finset.mem_singleton] at hentry
  rcases hentry with rfl | rfl | rfl <;>
    simp [CanonicalDepthAllocationEntry,
      canonicalPaymentClaimDepths_seven_zero,
      canonicalPaymentClaimDepths_seven_one,
      canonicalEndpointCapacityLevelSlots_seven_zero,
      canonicalEndpointCapacityLevelSlots_seven_one]

/-- The concrete allocation contains all three claims without duplication. -/
theorem sevenDepthAllocation_left_card :
    (sevenDepthAllocation.image Prod.fst).card = 3 := by
  decide

/-- The concrete allocation uses three distinct capacity slots. -/
theorem sevenDepthAllocation_right_card :
    (sevenDepthAllocation.image Prod.snd).card = 3 := by
  decide

/-- The concrete allocation itself has exactly three entries. -/
theorem sevenDepthAllocation_card : sevenDepthAllocation.card = 3 := by
  decide

/-- Public-root form of the first seven endpoint drift. -/
theorem endpointAccountingTerm_sevenDepthRegressionRoot_zero :
    endpointAccountingTerm sevenDepthRegressionRoot 0 = 1 := by
  simpa [sevenDepthRegressionRoot, sevenDepthOdd] using endpointAccountingTerm_seven_zero

/-- Public-root form of the second seven endpoint drift. -/
theorem endpointAccountingTerm_sevenDepthRegressionRoot_one :
    endpointAccountingTerm sevenDepthRegressionRoot 1 = -1 := by
  simpa [sevenDepthRegressionRoot, sevenDepthOdd] using endpointAccountingTerm_seven_one

end SevenDepthRegression

/-! ## Audited candidate queue and the corrected frontier

The first orbit-derived eligibility candidate was intentionally audited before
being exported as a relation.  It assigned depths one and two to level two and
assigned every depth `d >= 3` only to level `d`, at the same or a later block.
The finite cp-315 audit refutes that rule: roots 27 and 31 retain a depth-five
claim, while root 511 retains depth-eight and depth-nine claims after exact
integer evaluation reaches the fixed state one, which exposes only level two.
Consequently this module does **not** define `CanonicalRepaymentEligible`.

The definitions below retain the rejected rule only as an observable queue.
They are useful for stating the exact obstruction and for testing a future
eligibility rule that permits a justified cross-level payment.  A bounded
candidate queue would still be weaker than a coherent repayment schedule, and
neither follows from independent finite-prefix cardinality embeddings.
-/

/-- Required level under the audited, but refuted, exact-level candidate rule. -/
def canonicalCandidateRequiredLevel (depth : ℕ) : ℕ :=
  max 2 depth

/-- Number of claims in block `k` routed to candidate level `level`. -/
noncomputable def canonicalCandidateLevelDemand
    (n : OddNat) (k level : ℕ) : ℕ :=
  ((canonicalPaymentClaimDepths n k).filter fun depth =>
    canonicalCandidateRequiredLevel depth = level).card

/-- Whether canonical block `k` exposes the selected capacity level. -/
noncomputable def canonicalCandidateLevelCapacity
    (n : OddNat) (k level : ℕ) : ℕ :=
  if level ∈ canonicalEndpointCapacityLevelSlots n k then 1 else 0

/--
FIFO outstanding queue generated by the audited exact-level candidate.

Capacity is not banked: each block first adds its demand and then consumes its
single slot at that level when present.  This is an executable obstruction
observable, not a valid general repayment theorem.
-/
noncomputable def canonicalCandidateLevelOutstandingQueue
    (n : OddNat) (level : ℕ) : ℕ → ℕ
  | 0 => canonicalCandidateLevelDemand n 0 level -
      canonicalCandidateLevelCapacity n 0 level
  | k + 1 => canonicalCandidateLevelOutstandingQueue n level k +
      canonicalCandidateLevelDemand n (k + 1) level -
        canonicalCandidateLevelCapacity n (k + 1) level

/-- The candidate queue's successor equation, exposed for later comparisons. -/
theorem canonicalCandidateLevelOutstandingQueue_succ
    (n : OddNat) (level k : ℕ) :
    canonicalCandidateLevelOutstandingQueue n level (k + 1) =
      canonicalCandidateLevelOutstandingQueue n level k +
        canonicalCandidateLevelDemand n (k + 1) level -
          canonicalCandidateLevelCapacity n (k + 1) level := rfl

/-- Strong queue target; the cp-315 audit does not establish this predicate. -/
def CanonicalCandidateLevelQueuesUniformlyBounded
    (n : OddNat) (C : ℕ) : Prop :=
  ∀ level k, canonicalCandidateLevelOutstandingQueue n level k ≤ C

/-!
The valid global target remains `CanonicalEndpointBalanceUniformUpperBound`,
already proved to imply a canonical endpoint bit-width bound.  Passing from an
endpoint bound to an all-time bound additionally requires a uniform in-block
overshoot estimate.  Passing from an all-time bit-width bound to eventual
periodicity is a separate finite-state argument.  Neither implication is
silently folded into the rejected exact-level queue model.
-/

end DkMath.Collatz
