/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentPressure

#print "file: DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentRepayment"

namespace DkMath.Collatz

/-!
# Repayment across canonical universal payment blocks

Prefix capacity dominance is a no-overdraft special case, not the general
target.  This module retains positive endpoint excursions and records the
finite-horizon repayment structures needed to discharge them later.
-/

section SevenRegression

/-- The concrete odd initial state used by the first overdraft regression. -/
private def sevenOdd : OddNat := mkOddNat 7 (by decide)

private lemma v2_22 : v2 22 = 1 := by
  have h := (DkMath.ABC.padic_val_two_of_even 11).2 (by decide)
  simpa [v2, v2_odd 11 (by decide)] using h

private lemma v2_34 : v2 34 = 1 := by
  have h := (DkMath.ABC.padic_val_two_of_even 17).2 (by decide)
  simpa [v2, v2_odd 17 (by decide)] using h

private lemma v2_52 : v2 52 = 2 := by
  have h26 := (DkMath.ABC.padic_val_two_of_even 13).2 (by decide)
  have h52 := (DkMath.ABC.padic_val_two_of_even 26).2 (by decide)
  have hv13 : v2 13 = 0 := v2_odd 13 (by decide)
  have hv26 : v2 26 = 1 := by simpa [v2, hv13] using h26
  simpa [v2, hv26] using h52

private lemma v2_40 : v2 40 = 3 := by
  have h10 := (DkMath.ABC.padic_val_two_of_even 5).2 (by decide)
  have h20 := (DkMath.ABC.padic_val_two_of_even 10).2 (by decide)
  have h40 := (DkMath.ABC.padic_val_two_of_even 20).2 (by decide)
  have hv5 : v2 5 = 0 := v2_odd 5 (by decide)
  have hv10 : v2 10 = 1 := by simpa [v2, hv5] using h10
  have hv20 : v2 20 = 2 := by simpa [v2, hv10] using h20
  simpa [v2, hv20] using h40

private lemma v2_8 : v2 8 = 3 := by
  have h4 := (DkMath.ABC.padic_val_two_of_even 2).2 (by decide)
  have h8 := (DkMath.ABC.padic_val_two_of_even 4).2 (by decide)
  have hv2 : v2 2 = 1 := by
    have h := (DkMath.ABC.padic_val_two_of_even 1).2 (by decide)
    simp [v2]
  have hv4 : v2 4 = 2 := by simpa [v2, hv2] using h4
  simpa [v2, hv4] using h8

private lemma v2_14 : v2 14 = 1 := by
  have h := (DkMath.ABC.padic_val_two_of_even 7).2 (by decide)
  simpa [v2, v2_odd 7 (by decide)] using h

/-- The first canonical endpoint for the orbit from seven is time two. -/
theorem paymentEndpointSeq_seven_zero : paymentEndpointSeq sevenOdd 0 = 2 := by
  norm_num [paymentEndpointSeq, orbitPaymentTarget, orbitExactDepth,
    ResidualAllOnesDepth, oddOrbitLabel, iterateT, sevenOdd, mkOddNat, v2_8]

/-- The second canonical endpoint for the orbit from seven is time three. -/
theorem paymentEndpointSeq_seven_one : paymentEndpointSeq sevenOdd 1 = 3 := by
  rw [show paymentEndpointSeq sevenOdd 1 =
    orbitPaymentTarget sevenOdd (paymentEndpointSeq sevenOdd 0 + 1) by rfl]
  rw [paymentEndpointSeq_seven_zero]
  norm_num [orbitPaymentTarget, orbitExactDepth, ResidualAllOnesDepth, oddOrbitLabel,
    iterateT, T, sevenOdd, mkOddNat, threeNPlusOne, pow2,
    v2_22, v2_34, v2_52, v2_14]

/-- The first canonical block from seven has positive signed drift one. -/
theorem endpointAccountingTerm_seven_zero : endpointAccountingTerm sevenOdd 0 = 1 := by
  rw [endpointAccountingTerm_eq_universalPaymentBlockSignedDriftAt]
  rw [universalPaymentBlockSignedDriftAt_eq_bitWidth_sub sevenOdd
    (paymentEndpointSeq sevenOdd 0)
    (orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq sevenOdd 0)]
  rw [universalPaymentBlockStart_paymentEndpointSeq_zero,
    paymentEndpointSeq_seven_zero]
  norm_num [iterateT, T, sevenOdd, mkOddNat, threeNPlusOne, pow2,
    v2_22, v2_34, v2_52, bitWidth]

/-- The immediately following canonical block repays the first drift by minus one. -/
theorem endpointAccountingTerm_seven_one : endpointAccountingTerm sevenOdd 1 = -1 := by
  rw [endpointAccountingTerm_eq_universalPaymentBlockSignedDriftAt]
  rw [universalPaymentBlockSignedDriftAt_eq_bitWidth_sub sevenOdd
    (paymentEndpointSeq sevenOdd 1)
    (orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq sevenOdd 1)]
  rw [universalPaymentBlockStart_paymentEndpointSeq_succ,
    paymentEndpointSeq_seven_zero, paymentEndpointSeq_seven_one]
  norm_num [iterateT, T, sevenOdd, mkOddNat, threeNPlusOne, pow2,
    v2_22, v2_34, v2_52, v2_40, bitWidth]

/-- The two-block overdraft excursion from seven returns exactly to baseline. -/
theorem endpointAccountingTerm_seven_first_two_sum :
    endpointAccountingTerm sevenOdd 0 + endpointAccountingTerm sevenOdd 1 = 0 := by
  rw [endpointAccountingTerm_seven_zero, endpointAccountingTerm_seven_one]
  norm_num

end SevenRegression

/-- Signed endpoint balance through canonical block `m`. -/
noncomputable def canonicalEndpointBalanceInt (n : OddNat) (m : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (m + 1), endpointAccountingTerm n k

/-- Endpoint balance is exactly endpoint width minus initial width. -/
theorem canonicalEndpointBalanceInt_eq_bitWidth_sub
    (n : OddNat) (m : ℕ) :
    canonicalEndpointBalanceInt n m =
      (bitWidth (iterateT (paymentEndpointSeq n m + 1) n).1 : ℤ) - bitWidth n.1 := by
  exact sum_endpointAccountingTerm_paymentEndpointSeq n m

/-- Capacity dominance only at the selected terminal endpoint. -/
def CanonicalEndpointTerminalCapacityDominance
    (n : OddNat) (m : ℕ) : Prop :=
  cumulativeCanonicalEndpointClaims n m ≤ cumulativeCanonicalEndpointCapacity n m

/-- Terminal capacity dominance is exactly nonpositive terminal balance. -/
theorem canonicalEndpointTerminalCapacityDominance_iff_balance_nonpos
    (n : OddNat) (m : ℕ) :
    CanonicalEndpointTerminalCapacityDominance n m ↔
      canonicalEndpointBalanceInt n m ≤ 0 := by
  rw [canonicalEndpointBalanceInt, sum_endpointAccountingTerm_eq_claims_sub_capacity]
  exact ⟨fun h => sub_nonpos.mpr (Int.ofNat_le.mpr h),
    fun h => Int.ofNat_le.mp (sub_nonpos.mp h)⟩

/-- Terminal capacity dominance is exactly return to at most the initial width. -/
theorem canonicalEndpointTerminalCapacityDominance_iff_bitWidth_le
    (n : OddNat) (m : ℕ) :
    CanonicalEndpointTerminalCapacityDominance n m ↔
      bitWidth (iterateT (paymentEndpointSeq n m + 1) n).1 ≤ bitWidth n.1 := by
  rw [canonicalEndpointTerminalCapacityDominance_iff_balance_nonpos,
    canonicalEndpointBalanceInt_eq_bitWidth_sub]
  omega

/-- Orbit-time start of canonical block `q`. -/
noncomputable def canonicalEndpointBlockStart (n : OddNat) : ℕ → ℕ
  | 0 => 0
  | q + 1 => paymentEndpointSeq n q + 1

/-- A canonical block starts where its universal source interval starts. -/
theorem canonicalEndpointBlockStart_eq_universalPaymentBlockStart
    (n : OddNat) (q : ℕ) :
    canonicalEndpointBlockStart n q =
      universalPaymentBlockStart n (paymentEndpointSeq n q)
        (orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n q) := by
  cases q with
  | zero =>
      simp [canonicalEndpointBlockStart,
        universalPaymentBlockStart_paymentEndpointSeq_zero]
  | succ q =>
      simp [canonicalEndpointBlockStart,
        universalPaymentBlockStart_paymentEndpointSeq_succ]

/-- Sliding endpoint-block telescope from block `q` through block `m`. -/
theorem sum_endpointAccountingTerm_Icc_eq_bitWidth_sub
    (n : OddNat) {q m : ℕ} (hqm : q ≤ m) :
    (∑ k ∈ Finset.Icc q m, endpointAccountingTerm n k) =
      (bitWidth (iterateT (paymentEndpointSeq n m + 1) n).1 : ℤ) -
        bitWidth (iterateT (canonicalEndpointBlockStart n q) n).1 := by
  have hsubset : Finset.range q ⊆ Finset.range (m + 1) := by
    intro i hi
    simp only [Finset.mem_range] at hi ⊢
    omega
  have hIcc : Finset.Icc q m = Finset.range (m + 1) \ Finset.range q := by
    ext i
    simp
    omega
  rw [hIcc, Finset.sum_sdiff_eq_sub hsubset]
  rw [sum_endpointAccountingTerm_paymentEndpointSeq]
  cases q with
  | zero =>
      simp [canonicalEndpointBlockStart, iterateT]
  | succ q =>
      rw [show ∑ k ∈ Finset.range (q + 1), endpointAccountingTerm n k =
          (bitWidth (iterateT (paymentEndpointSeq n q + 1) n).1 : ℤ) - bitWidth n.1 by
        exact sum_endpointAccountingTerm_paymentEndpointSeq n q]
      simp [canonicalEndpointBlockStart]

/-- Claims-minus-capacity form of the sliding block telescope. -/
theorem sum_endpointAccountingTerm_Icc_eq_claims_sub_capacity
    (n : OddNat) {q m : ℕ} (_hqm : q ≤ m) :
    (∑ k ∈ Finset.Icc q m, endpointAccountingTerm n k) =
      (∑ k ∈ Finset.Icc q m,
        (((floatGrowthDebtFiberAt n (paymentEndpointSeq n k)).card : ℤ) +
          (endpointImmediateCarryTwoClaimFiberAt n (paymentEndpointSeq n k)).card)) -
      ∑ k ∈ Finset.Icc q m,
        (extraPaymentCapacityAt n (paymentEndpointSeq n k) : ℤ) := by
  simp_rw [endpointAccountingTerm]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]

/-!
## Matching directions

The old ordered matching points from a claim to an already available slot.  It
is therefore a backward-credit certificate.  A repayment certificate has the
opposite temporal inequality and may extend its payment horizon beyond the
claim horizon.  Keeping these predicates separate prevents a temporary
overdraft from being silently ruled out by the type of the matching.
-/

/-- Compatibility name exposing the temporal meaning of the old matching. -/
abbrev CanonicalEndpointBackwardCreditMatching :=
  CanonicalEndpointOrderedCapacityMatching

/--
A finite claim prefix repaid by slots at its own or later endpoint, up to a
possibly larger payment horizon. Existence is not asserted here.
-/
def CanonicalEndpointForwardRepaymentMatching
    (n : OddNat) (claimHorizon payHorizon : ℕ) : Prop :=
  claimHorizon ≤ payHorizon ∧
    ∃ pay : CanonicalEndpointClaimCarrier n claimHorizon →
        CanonicalEndpointCapacityCarrier n payHorizon,
      Function.Injective pay ∧
        ∀ claim, claim.val.1.val ≤ (pay claim).val.1.val

/-- Every finite claim prefix has some finite future repayment horizon. -/
def EveryFiniteCanonicalClaimPrefixEventuallyRepayable (n : OddNat) : Prop :=
  ∀ q, ∃ r, q ≤ r ∧ CanonicalEndpointForwardRepaymentMatching n q r

/-- A forward repayment matching records its horizon order explicitly. -/
theorem CanonicalEndpointForwardRepaymentMatching.claimHorizon_le
    {n : OddNat} {q r : ℕ}
    (h : CanonicalEndpointForwardRepaymentMatching n q r) : q ≤ r :=
  h.1

/-- Claim carriers are finite dependent sums of the complete block fibers. -/
noncomputable def canonicalEndpointClaimCarrierEquiv
    (n : OddNat) (m : ℕ) :
    CanonicalEndpointClaimCarrier n m ≃
      Σ k : Fin (m + 1),
        {i : ℕ // i ∈ carryTwoPaymentClaimFiberAt n (paymentEndpointSeq n k.val)} where
  toFun claim :=
    ⟨claim.val.1, claim.val.2,
      (mem_carryTwoPaymentClaimFiberAt_iff_growthDebt_or_endpointImmediate
        (h := orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n claim.val.1.val)).2
        claim.property⟩
  invFun claim :=
    ⟨⟨claim.1, claim.2.val⟩,
      (mem_carryTwoPaymentClaimFiberAt_iff_growthDebt_or_endpointImmediate
        (h := orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n claim.1.val)).1
        claim.2.property⟩
  left_inv claim := by
    apply Subtype.ext
    rfl
  right_inv claim := by
    rcases claim with ⟨k, i⟩
    rfl

/-- Capacity carriers are finite dependent sums of local capacity fibers. -/
noncomputable def canonicalEndpointCapacityCarrierEquiv
    (n : OddNat) (m : ℕ) :
    CanonicalEndpointCapacityCarrier n m ≃
      Σ k : Fin (m + 1), {s : ℕ // s ∈ canonicalEndpointCapacitySlots n k.val} where
  toFun slot := ⟨slot.val.1, slot.val.2, slot.property⟩
  invFun slot := ⟨⟨slot.1, slot.2.val⟩, slot.2.property⟩
  left_inv slot := by
    apply Subtype.ext
    rfl
  right_inv slot := by
    rcases slot with ⟨k, s⟩
    rfl

/-- The abstract claim carrier has the cumulative complete-claim cardinality. -/
theorem natCard_canonicalEndpointClaimCarrier
    (n : OddNat) (m : ℕ) :
    Nat.card (CanonicalEndpointClaimCarrier n m) =
      cumulativeCanonicalEndpointClaims n m := by
  rw [Nat.card_congr (canonicalEndpointClaimCarrierEquiv n m), Nat.card_sigma]
  simp_rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  unfold cumulativeCanonicalEndpointClaims
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k hk
  rw [dif_pos (Finset.mem_range.mp hk)]
  rw [carryTwoPaymentClaimFiberAt_card_eq_growthDebt_card_add_endpoint_card
    n (paymentEndpointSeq n k)
      (orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n k)]

/-- The abstract capacity carrier has the cumulative slot cardinality. -/
theorem natCard_canonicalEndpointCapacityCarrier
    (n : OddNat) (m : ℕ) :
    Nat.card (CanonicalEndpointCapacityCarrier n m) =
      cumulativeCanonicalEndpointCapacity n m := by
  rw [Nat.card_congr (canonicalEndpointCapacityCarrierEquiv n m), Nat.card_sigma]
  simp_rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  unfold cumulativeCanonicalEndpointCapacity
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k hk
  rw [dif_pos (Finset.mem_range.mp hk)]

/-- A backward-credit matching is a no-overdraft certificate on every prefix. -/
theorem CanonicalEndpointBackwardCreditMatching.to_prefixCapacityDominance
    {n : OddNat} {m : ℕ}
    (h : CanonicalEndpointBackwardCreditMatching n m) :
    CanonicalEndpointPrefixCapacityDominance n m := by
  intro q hqm
  rcases h with ⟨pay, hpayInjective, hdeadline⟩
  let extendClaim : CanonicalEndpointClaimCarrier n q →
      CanonicalEndpointClaimCarrier n m := fun claim =>
    ⟨⟨⟨claim.val.1.val, by omega⟩, claim.val.2⟩, claim.property⟩
  let prefixPay : CanonicalEndpointClaimCarrier n q →
      CanonicalEndpointCapacityCarrier n q := fun claim =>
    ⟨⟨⟨(pay (extendClaim claim)).val.1.val, by
          have hbefore := hdeadline (extendClaim claim)
          have hclaimle : claim.val.1.val ≤ q := Nat.lt_succ_iff.mp claim.val.1.isLt
          change (pay (extendClaim claim)).val.1.val ≤ claim.val.1.val at hbefore
          omega⟩,
        (pay (extendClaim claim)).val.2⟩,
      (pay (extendClaim claim)).property⟩
  have hextendInjective : Function.Injective extendClaim := by
    intro a b hab
    have hblock := congrArg (fun claim => claim.val.1.val) hab
    have hsource := congrArg (fun claim => claim.val.2) hab
    apply Subtype.ext
    apply Prod.ext
    · apply Fin.ext
      exact hblock
    · exact hsource
  have hprefixInjective : Function.Injective prefixPay := by
    intro a b hab
    have hblock := congrArg (fun slot => slot.val.1.val) hab
    have hslot := congrArg (fun slot => slot.val.2) hab
    apply hextendInjective
    apply hpayInjective
    apply Subtype.ext
    apply Prod.ext
    · apply Fin.ext
      exact hblock
    · exact hslot
  let : Finite (CanonicalEndpointCapacityCarrier n q) :=
    Finite.of_injective (canonicalEndpointCapacityCarrierEquiv n q).toFun
      (canonicalEndpointCapacityCarrierEquiv n q).injective
  have hcard := Nat.card_le_card_of_injective prefixPay hprefixInjective
  rwa [natCard_canonicalEndpointClaimCarrier,
    natCard_canonicalEndpointCapacityCarrier] at hcard

/-- Forward repayment matching implies enough capacity at its future horizon. -/
theorem CanonicalEndpointForwardRepaymentMatching.claims_le_capacity
    {n : OddNat} {q r : ℕ}
    (h : CanonicalEndpointForwardRepaymentMatching n q r) :
    cumulativeCanonicalEndpointClaims n q ≤ cumulativeCanonicalEndpointCapacity n r := by
  rcases h with ⟨_, pay, hpayInjective, _⟩
  let : Finite (CanonicalEndpointCapacityCarrier n r) :=
    Finite.of_injective (canonicalEndpointCapacityCarrierEquiv n r).toFun
      (canonicalEndpointCapacityCarrierEquiv n r).injective
  have hcard := Nat.card_le_card_of_injective pay hpayInjective
  rwa [natCard_canonicalEndpointClaimCarrier,
    natCard_canonicalEndpointCapacityCarrier] at hcard

/-!
## Depth-coordinate claim and capacity surfaces

Depth one is the canonical endpoint. Increasing depth walks backwards through
the block.  This coordinate is intrinsic to the exact-recovery staircase and
does not yet prescribe which future capacity slot may pay a marked claim.
-/

/-- Source time at positive staircase depth `d` in canonical block `k`. -/
noncomputable def canonicalPaymentSourceAtDepth
    (n : OddNat) (k d : ℕ) : ℕ :=
  paymentEndpointSeq n k + 1 - d

/-- Complete carry-two claim depths in canonical block `k`. -/
noncomputable def canonicalPaymentClaimDepths
    (n : OddNat) (k : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 (canonicalPaymentBlockLength n k)).filter fun d =>
    CarryTwoDebtAt n (canonicalPaymentSourceAtDepth n k d)

/-- Membership in the marked claim-depth carrier. -/
theorem mem_canonicalPaymentClaimDepths_iff
    {n : OddNat} {k d : ℕ} :
    d ∈ canonicalPaymentClaimDepths n k ↔
      1 ≤ d ∧ d ≤ canonicalPaymentBlockLength n k ∧
        CarryTwoDebtAt n (canonicalPaymentSourceAtDepth n k d) := by
  classical
  rw [canonicalPaymentClaimDepths]
  simp only [Finset.mem_filter, Finset.mem_Icc]
  tauto

/-- Every canonical block has at least its endpoint. -/
theorem canonicalPaymentBlockLength_pos (n : OddNat) (k : ℕ) :
    0 < canonicalPaymentBlockLength n k := by
  rw [canonicalPaymentBlockLength_eq_sourceFiber_card]
  exact Finset.card_pos.mpr
    (orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n k)

/-- Depth one is exactly the endpoint source. -/
theorem canonicalPaymentSourceAtDepth_one (n : OddNat) (k : ℕ) :
    canonicalPaymentSourceAtDepth n k 1 = paymentEndpointSeq n k := by
  simp [canonicalPaymentSourceAtDepth]

/-- The endpoint depth is marked exactly when the immediate claim is present. -/
theorem one_mem_canonicalPaymentClaimDepths_iff
    (n : OddNat) (k : ℕ) :
    1 ∈ canonicalPaymentClaimDepths n k ↔
      CarryTwoDebtAt n (paymentEndpointSeq n k) := by
  rw [mem_canonicalPaymentClaimDepths_iff, canonicalPaymentSourceAtDepth_one]
  have hlen := canonicalPaymentBlockLength_pos n k
  constructor
  · exact fun h => h.2.2
  · intro hcarry
    exact ⟨by omega, by omega, hcarry⟩

/-- Levelled endpoint-capacity slots; level one is reserved for the center. -/
noncomputable def canonicalEndpointCapacityDepthSlots
    (n : OddNat) (k : ℕ) : Finset ℕ :=
  Finset.Icc 2 (orbitWindowHeight n (paymentEndpointSeq n k))

/-- The levelled slot carrier has exactly the endpoint's extra capacity. -/
theorem canonicalEndpointCapacityDepthSlots_card
    (n : OddNat) (k : ℕ) :
    (canonicalEndpointCapacityDepthSlots n k).card =
      extraPaymentCapacityAt n (paymentEndpointSeq n k) := by
  rw [canonicalEndpointCapacityDepthSlots, Nat.card_Icc]
  unfold extraPaymentCapacityAt
  have hheight := two_le_orbitWindowHeight_paymentEndpointSeq n k
  omega

/--
At every valid positive depth, the recovery fiber is the singleton containing
the source obtained by walking backwards from the endpoint.
-/
theorem canonicalPaymentBlockRecoveryFiber_eq_singleton_sourceAtDepth
    (n : OddNat) (k d : ℕ)
    (hdpos : 1 ≤ d) (hdle : d ≤ canonicalPaymentBlockLength n k) :
    canonicalPaymentBlockRecoveryFiber n k d =
      {canonicalPaymentSourceAtDepth n k d} := by
  classical
  have hnonempty :=
    (canonicalPaymentBlockRecoveryFiber_nonempty_iff n k d).2 ⟨hdpos, hdle⟩
  rcases hnonempty with ⟨i, hi⟩
  rcases mem_canonicalPaymentBlockRecoveryFiber_iff.mp hi with ⟨hiblock, hirecover⟩
  have hdepth :=
    orbitExactDepth_eq_paymentEndpoint_sub_add_one_of_mem_canonicalPaymentBlock hiblock
  have hrecoverDepth : orbitExactDepth n i = d := by
    simpa [OrbitDepthRecoversExactlyAt, orbitExactDepth] using hirecover
  have hsource : i = canonicalPaymentSourceAtDepth n k d := by
    have hiend : i ≤ paymentEndpointSeq n k := by
      exact (mem_orbitPaymentSourceFiberAt_iff.mp
        (by simpa [canonicalPaymentBlock_eq_sourceFiber] using hiblock)).1
    unfold canonicalPaymentSourceAtDepth
    omega
  ext i'
  simp only [Finset.mem_singleton]
  constructor
  · intro hi'
    rcases mem_canonicalPaymentBlockRecoveryFiber_iff.mp hi' with
      ⟨hi'block, hi'recover⟩
    have hii' := eq_of_mem_canonicalPaymentBlock_of_recovery_same_depth
      hiblock hi'block hirecover hi'recover
    omega
  · rintro rfl
    simpa [← hsource] using hi

/-- A valid recovery depth has the expected unique source. -/
theorem mem_canonicalPaymentBlockRecoveryFiber_iff_eq_sourceAtDepth
    {n : OddNat} {k d i : ℕ}
    (hdpos : 1 ≤ d) (hdle : d ≤ canonicalPaymentBlockLength n k) :
    i ∈ canonicalPaymentBlockRecoveryFiber n k d ↔
      i = canonicalPaymentSourceAtDepth n k d := by
  rw [canonicalPaymentBlockRecoveryFiber_eq_singleton_sourceAtDepth n k d hdpos hdle]
  simp

/-- A marked depth is precisely a valid singleton recovery carrying two. -/
theorem mem_canonicalPaymentClaimDepths_iff_recovery_carryTwo
    {n : OddNat} {k d : ℕ} :
    d ∈ canonicalPaymentClaimDepths n k ↔
      1 ≤ d ∧ d ≤ canonicalPaymentBlockLength n k ∧
        ∃ i, canonicalPaymentBlockRecoveryFiber n k d = {i} ∧ CarryTwoDebtAt n i := by
  rw [mem_canonicalPaymentClaimDepths_iff]
  constructor
  · rintro ⟨hdpos, hdle, hcarry⟩
    exact ⟨hdpos, hdle, canonicalPaymentSourceAtDepth n k d,
      canonicalPaymentBlockRecoveryFiber_eq_singleton_sourceAtDepth n k d hdpos hdle,
      hcarry⟩
  · rintro ⟨hdpos, hdle, i, hfiber, hcarry⟩
    have hcanonical :=
      canonicalPaymentBlockRecoveryFiber_eq_singleton_sourceAtDepth n k d hdpos hdle
    have hi : canonicalPaymentSourceAtDepth n k d = i := by
      rw [hcanonical] at hfiber
      simpa using Finset.singleton_inj.mp hfiber
    exact ⟨hdpos, hdle, by simpa [hi] using hcarry⟩

/-- Source/depth coordinates are inverse on the valid canonical staircase. -/
theorem canonicalPaymentDebtDepth_sourceAtDepth
    (n : OddNat) (k d : ℕ)
    (hdpos : 1 ≤ d) (hdle : d ≤ canonicalPaymentBlockLength n k) :
    canonicalPaymentDebtDepth n k (canonicalPaymentSourceAtDepth n k d) = d := by
  rw [canonicalPaymentBlockLength_eq_endpoint_sub_start_add_one] at hdle
  unfold canonicalPaymentDebtDepth canonicalPaymentSourceAtDepth
  omega

/--
Marked recovery depths are the depth-coordinate image of the complete claim
fiber, including the optional immediate endpoint claim.
-/
theorem canonicalPaymentClaimDepths_eq_image_completeClaimFiber
    (n : OddNat) (k : ℕ) :
    canonicalPaymentClaimDepths n k =
      (carryTwoPaymentClaimFiberAt n (paymentEndpointSeq n k)).image
        (canonicalPaymentDebtDepth n k) := by
  classical
  let e := paymentEndpointSeq n k
  let h := orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n k
  ext d
  constructor
  · intro hd
    rcases mem_canonicalPaymentClaimDepths_iff.mp hd with ⟨hdpos, hdle, hcarry⟩
    let i := canonicalPaymentSourceAtDepth n k d
    have hfiber : canonicalPaymentBlockRecoveryFiber n k d = {i} := by
      simpa [i] using
        canonicalPaymentBlockRecoveryFiber_eq_singleton_sourceAtDepth n k d hdpos hdle
    have hiRecovery : i ∈ canonicalPaymentBlockRecoveryFiber n k d := by
      rw [hfiber]
      simp
    have hiBlock := (mem_canonicalPaymentBlockRecoveryFiber_iff.mp hiRecovery).1
    have hiIcc : i ∈ Finset.Icc
        (universalPaymentBlockStart n e h) e := by
      simpa [e, h, canonicalPaymentBlock_eq_Icc_universalPaymentBlockStart] using hiBlock
    have hiClaim : i ∈ carryTwoPaymentClaimFiberAt n e :=
      (mem_carryTwoPaymentClaimFiberAt_iff_mem_universalPaymentBlock_and_carryTwo
        (h := h)).2 ⟨hiIcc, by simpa [i, e] using hcarry⟩
    apply Finset.mem_image.mpr
    refine ⟨i, by simpa [e] using hiClaim, ?_⟩
    simpa [i] using canonicalPaymentDebtDepth_sourceAtDepth n k d hdpos hdle
  · intro hd
    rcases Finset.mem_image.mp hd with ⟨i, hiClaim, hid⟩
    have hiClaim' : i ∈ carryTwoPaymentClaimFiberAt n e := by
      simpa [e] using hiClaim
    rcases
        (mem_carryTwoPaymentClaimFiberAt_iff_mem_universalPaymentBlock_and_carryTwo
          (h := h)).1 hiClaim' with ⟨hiIcc, hiCarry⟩
    have hiBlock : i ∈ canonicalPaymentBlock n k := by
      rw [canonicalPaymentBlock_eq_Icc_universalPaymentBlockStart]
      simpa [e, h] using hiIcc
    have hiDepth :=
      orbitExactDepth_eq_paymentEndpoint_sub_add_one_of_mem_canonicalPaymentBlock hiBlock
    have hiRecover : OrbitDepthRecoversExactlyAt n i d := by
      have hdepth : orbitExactDepth n i = d := by
        rw [hiDepth]
        simpa [canonicalPaymentDebtDepth] using hid
      simpa [OrbitDepthRecoversExactlyAt, orbitExactDepth] using hdepth
    have hvalid := (canonicalPaymentBlockRecoveryFiber_nonempty_iff n k d).1
      ⟨i, mem_canonicalPaymentBlockRecoveryFiber_iff.mpr ⟨hiBlock, hiRecover⟩⟩
    rcases hvalid with ⟨hdpos, hdle⟩
    have hiSource : i = canonicalPaymentSourceAtDepth n k d :=
      (mem_canonicalPaymentBlockRecoveryFiber_iff_eq_sourceAtDepth hdpos hdle).mp
        (mem_canonicalPaymentBlockRecoveryFiber_iff.mpr ⟨hiBlock, hiRecover⟩)
    exact mem_canonicalPaymentClaimDepths_iff.mpr
      ⟨hdpos, hdle, by simpa [← hiSource] using hiCarry⟩

/-- Complete claim count is exactly marked recovery-depth count. -/
theorem canonicalPaymentClaimDepths_card
    (n : OddNat) (k : ℕ) :
    (canonicalPaymentClaimDepths n k).card =
      (floatGrowthDebtFiberAt n (paymentEndpointSeq n k)).card +
        (endpointImmediateCarryTwoClaimFiberAt n (paymentEndpointSeq n k)).card := by
  rw [canonicalPaymentClaimDepths_eq_image_completeClaimFiber]
  rw [Finset.card_image_iff.mpr]
  · exact carryTwoPaymentClaimFiberAt_card_eq_growthDebt_card_add_endpoint_card
      n (paymentEndpointSeq n k)
        (orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n k)
  · intro i hi i' hi' heq
    have hiIcc :=
      (mem_carryTwoPaymentClaimFiberAt_iff_mem_universalPaymentBlock_and_carryTwo
        (h := orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n k)).1 hi
    have hi'Icc :=
      (mem_carryTwoPaymentClaimFiberAt_iff_mem_universalPaymentBlock_and_carryTwo
        (h := orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n k)).1 hi'
    have hile := (Finset.mem_Icc.mp hiIcc.1).2
    have hi'le := (Finset.mem_Icc.mp hi'Icc.1).2
    unfold canonicalPaymentDebtDepth at heq
    omega

/-- Delayed marked claims are complete marked claims above depth one. -/
noncomputable def canonicalPaymentDelayedClaimDepths
    (n : OddNat) (k : ℕ) : Finset ℕ := by
  classical
  exact (canonicalPaymentClaimDepths n k).filter fun d => 2 ≤ d

/-- Membership API for delayed marked claim depths. -/
theorem mem_canonicalPaymentDelayedClaimDepths_iff
    {n : OddNat} {k d : ℕ} :
    d ∈ canonicalPaymentDelayedClaimDepths n k ↔
      d ∈ canonicalPaymentClaimDepths n k ∧ 2 ≤ d := by
  classical
  simp [canonicalPaymentDelayedClaimDepths]

/-- Existing delayed-debt addresses lie in the staircase interval `2..L`. -/
theorem canonicalPaymentMarkedDebtDepths_subset_Icc
    (n : OddNat) (k : ℕ) :
    canonicalPaymentMarkedDebtDepths n k ⊆
      Finset.Icc 2 (canonicalPaymentBlockLength n k) := by
  intro d hd
  rcases Finset.mem_image.mp hd with ⟨i, hiDebt, hid⟩
  have hdebt := (mem_floatGrowthDebtFiberAt_iff.mp hiDebt).2.1
  have hdelayed := (floatDebtAt_iff_delayedCarryTwoDebtAt n i).mp hdebt
  have htwoExact :=
    (orbitWindowHeight_eq_one_iff_two_le_orbitExactDepth n i).mp hdelayed.2
  have hdepth := canonicalPaymentDebtDepth_eq_orbitExactDepth_of_mem_growthDebt hiDebt
  have hiBlock : i ∈ canonicalPaymentBlock n k := by
    rw [canonicalPaymentBlock_eq_sourceFiber]
    exact mem_orbitPaymentSourceFiberAt_of_mem_floatGrowthDebtFiberAt hiDebt
  have hiRecover : OrbitDepthRecoversExactlyAt n i d := by
    have : orbitExactDepth n i = d := by omega
    simpa [OrbitDepthRecoversExactlyAt, orbitExactDepth] using this
  have hvalid := (canonicalPaymentBlockRecoveryFiber_nonempty_iff n k d).1
    ⟨i, mem_canonicalPaymentBlockRecoveryFiber_iff.mpr ⟨hiBlock, hiRecover⟩⟩
  exact Finset.mem_Icc.mpr ⟨by omega, hvalid.2⟩

/-- Delayed claim depths are exactly the old marked delayed-debt addresses. -/
theorem canonicalPaymentDelayedClaimDepths_eq_markedDebtDepths
    (n : OddNat) (k : ℕ) :
    canonicalPaymentDelayedClaimDepths n k = canonicalPaymentMarkedDebtDepths n k := by
  classical
  ext d
  constructor
  · intro hd
    rcases mem_canonicalPaymentDelayedClaimDepths_iff.mp hd with ⟨hdClaim, hd2⟩
    rcases mem_canonicalPaymentClaimDepths_iff.mp hdClaim with
      ⟨hdpos, hdle, hcarry⟩
    let i := canonicalPaymentSourceAtDepth n k d
    have hiRecovery : i ∈ canonicalPaymentBlockRecoveryFiber n k d :=
      (mem_canonicalPaymentBlockRecoveryFiber_iff_eq_sourceAtDepth hdpos hdle).2 rfl
    have hiBlock := (mem_canonicalPaymentBlockRecoveryFiber_iff.mp hiRecovery).1
    have hiIcc : i ∈ Finset.Icc
        (universalPaymentBlockStart n (paymentEndpointSeq n k)
          (orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n k))
        (paymentEndpointSeq n k) := by
      rw [← canonicalPaymentBlock_eq_Icc_universalPaymentBlockStart]
      exact hiBlock
    have hiInterior : i ∈ Finset.Ico
        (universalPaymentBlockStart n (paymentEndpointSeq n k)
          (orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n k))
        (paymentEndpointSeq n k) := by
      have hstaircase :=
        orbitExactDepth_eq_paymentEndpoint_sub_add_one_of_mem_canonicalPaymentBlock hiBlock
      have hrecovery :=
        (mem_canonicalPaymentBlockRecoveryFiber_iff.mp hiRecovery).2
      have hdepth : orbitExactDepth n i = d := by
        simpa [OrbitDepthRecoversExactlyAt, orbitExactDepth] using hrecovery
      exact Finset.mem_Ico.mpr ⟨(Finset.mem_Icc.mp hiIcc).1, by
        omega⟩
    have hiDebt : i ∈ floatGrowthDebtFiberAt n (paymentEndpointSeq n k) :=
      (mem_floatGrowthDebtFiberAt_iff_mem_universalPaymentBlockInterior_and_carryTwo
        (h := orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n k)).2
        ⟨hiInterior, by simpa [i] using hcarry⟩
    apply Finset.mem_image.mpr
    exact ⟨i, hiDebt, by
      simpa [i] using canonicalPaymentDebtDepth_sourceAtDepth n k d hdpos hdle⟩
  · intro hd
    have hdIcc := canonicalPaymentMarkedDebtDepths_subset_Icc n k hd
    rcases Finset.mem_Icc.mp hdIcc with ⟨hd2, hdle⟩
    have hdpos : 1 ≤ d := by omega
    rcases Finset.mem_image.mp hd with ⟨i, hiDebt, hid⟩
    have hiBlock : i ∈ canonicalPaymentBlock n k := by
      rw [canonicalPaymentBlock_eq_sourceFiber]
      exact mem_orbitPaymentSourceFiberAt_of_mem_floatGrowthDebtFiberAt hiDebt
    have hdepth := canonicalPaymentDebtDepth_eq_orbitExactDepth_of_mem_growthDebt hiDebt
    have hiRecover : OrbitDepthRecoversExactlyAt n i d := by
      have : orbitExactDepth n i = d := by omega
      simpa [OrbitDepthRecoversExactlyAt, orbitExactDepth] using this
    have hiSource :=
      (mem_canonicalPaymentBlockRecoveryFiber_iff_eq_sourceAtDepth
        hdpos hdle).mp
        (mem_canonicalPaymentBlockRecoveryFiber_iff.mpr ⟨hiBlock, hiRecover⟩)
    have hcarry :=
      ((floatDebtAt_iff_delayedCarryTwoDebtAt n i).mp
        (mem_floatGrowthDebtFiberAt_iff.mp hiDebt).2.1).1
    exact mem_canonicalPaymentDelayedClaimDepths_iff.mpr
      ⟨mem_canonicalPaymentClaimDepths_iff.mpr
        ⟨hdpos, hdle,
          by simpa [← hiSource] using hcarry⟩,
        hd2⟩

/-- Delayed debt count is exactly the number of marked recovery depths above one. -/
theorem canonicalPaymentDelayedClaimDepths_card
    (n : OddNat) (k : ℕ) :
    (canonicalPaymentDelayedClaimDepths n k).card =
      (floatGrowthDebtFiberAt n (paymentEndpointSeq n k)).card := by
  rw [canonicalPaymentDelayedClaimDepths_eq_markedDebtDepths,
    canonicalPaymentMarkedDebtDepths_card]

/-!
## Excursion and boundedness surfaces

These predicates deliberately describe endpoint balance only. They neither
state nor imply convergence of the underlying orbit.
-/

/-- Balance immediately before canonical block `q`. -/
noncomputable def canonicalEndpointBalanceBefore (n : OddNat) : ℕ → ℤ
  | 0 => 0
  | q + 1 => canonicalEndpointBalanceInt n q

/-- A canonical endpoint lies strictly above the balance before its block. -/
def CanonicalEndpointPositiveExcursionAt (n : OddNat) (q : ℕ) : Prop :=
  canonicalEndpointBalanceBefore n q < canonicalEndpointBalanceInt n q

/-- Endpoint `r` has repaid the excursion beginning at block `q`. -/
def CanonicalEndpointExcursionRepaidAt (n : OddNat) (q r : ℕ) : Prop :=
  q ≤ r ∧ canonicalEndpointBalanceInt n r ≤ canonicalEndpointBalanceBefore n q

/-- Every positive endpoint excursion eventually returns to its prior baseline. -/
def EveryCanonicalEndpointExcursionEventuallyRepaid (n : OddNat) : Prop :=
  ∀ q, CanonicalEndpointPositiveExcursionAt n q →
    ∃ r, CanonicalEndpointExcursionRepaidAt n q r

/-- The orbit from seven has a genuine positive first endpoint excursion. -/
theorem canonicalEndpointPositiveExcursionAt_seven_zero :
    CanonicalEndpointPositiveExcursionAt sevenOdd 0 := by
  simp [CanonicalEndpointPositiveExcursionAt, canonicalEndpointBalanceBefore,
    canonicalEndpointBalanceInt, endpointAccountingTerm_seven_zero]

/-- The second canonical endpoint repays the first excursion from seven. -/
theorem canonicalEndpointExcursionRepaidAt_seven_zero_one :
    CanonicalEndpointExcursionRepaidAt sevenOdd 0 1 := by
  constructor
  · omega
  · change (∑ k ∈ Finset.range 2, endpointAccountingTerm sevenOdd k) ≤ 0
    rw [show ∑ k ∈ Finset.range 2, endpointAccountingTerm sevenOdd k =
        endpointAccountingTerm sevenOdd 0 + endpointAccountingTerm sevenOdd 1 by
      norm_num [Finset.sum_range_succ]]
    rw [endpointAccountingTerm_seven_first_two_sum]

/-- A uniform integer balance ceiling at every canonical endpoint. -/
def CanonicalEndpointBalanceUniformUpperBound (n : OddNat) (C : ℕ) : Prop :=
  ∀ m, canonicalEndpointBalanceInt n m ≤ C

/-- A uniform balance ceiling gives the corresponding canonical width ceiling. -/
theorem bitWidth_paymentEndpointSeq_le_of_balanceUniformUpperBound
    {n : OddNat} {C : ℕ}
    (h : CanonicalEndpointBalanceUniformUpperBound n C) (m : ℕ) :
    bitWidth (iterateT (paymentEndpointSeq n m + 1) n).1 ≤ bitWidth n.1 + C := by
  have hm := h m
  rw [canonicalEndpointBalanceInt_eq_bitWidth_sub] at hm
  omega

/-!
## Genuine frontier: eligibility

The claim and capacity sides now both have exact depth coordinates, and marked
recovery incidence has exact cardinality. What is not proved is that a claim
depth is eligible for a same-depth slot at its own or a later endpoint. That
relation must encode an orbit invariant, not merely matching cardinalities.
Accordingly no eligibility predicate is exported here and no forward repayment
matching is asserted.  The cp-315 audit in `UniversalPaymentDepthLedger` tests
the first exact-level candidate and refutes it on roots 27, 31, and 511.  A
future relation must therefore justify cross-level payment or identify a
different orbit-derived capacity coordinate before constructing a payment map.
-/

end DkMath.Collatz
