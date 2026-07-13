/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentBlockNormalForm

#print "file: DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentPositiveBlock"

namespace DkMath.Collatz

/-!
# Positive canonical blocks: pressure or saturation

Claim depths are split at the terminal valuation `v`.  Claims above `v` are
not merely counted: their exact source times continue beyond depth `v`, giving
an explicit injection into the local continuation fiber.  The resulting
cardinality arithmetic isolates one rigid exception to positive pressure.
-/

/-- Marked claim depths at or below the terminal valuation. -/
noncomputable def canonicalBlockLowClaimDepths
    (n : OddNat) (k : ℕ) : Finset ℕ := by
  classical
  exact (canonicalPaymentClaimDepths n k).filter fun d =>
    d ≤ canonicalBlockTerminalValuation n k

/-- Marked claim depths strictly above the terminal valuation. -/
noncomputable def canonicalBlockHighClaimDepths
    (n : OddNat) (k : ℕ) : Finset ℕ := by
  classical
  exact (canonicalPaymentClaimDepths n k).filter fun d =>
    canonicalBlockTerminalValuation n k < d

/-- Membership API for low claim depths. -/
theorem mem_canonicalBlockLowClaimDepths_iff
    {n : OddNat} {k d : ℕ} :
    d ∈ canonicalBlockLowClaimDepths n k ↔
      d ∈ canonicalPaymentClaimDepths n k ∧
        d ≤ canonicalBlockTerminalValuation n k := by
  classical
  simp [canonicalBlockLowClaimDepths]

/-- Membership API for high claim depths. -/
theorem mem_canonicalBlockHighClaimDepths_iff
    {n : OddNat} {k d : ℕ} :
    d ∈ canonicalBlockHighClaimDepths n k ↔
      d ∈ canonicalPaymentClaimDepths n k ∧
        canonicalBlockTerminalValuation n k < d := by
  classical
  simp [canonicalBlockHighClaimDepths]

/-- Low and high depths partition all marked claim depths. -/
theorem canonicalPaymentClaimDepths_eq_low_union_high
    (n : OddNat) (k : ℕ) :
    canonicalPaymentClaimDepths n k =
      canonicalBlockLowClaimDepths n k ∪ canonicalBlockHighClaimDepths n k := by
  classical
  ext d
  simp only [Finset.mem_union, mem_canonicalBlockLowClaimDepths_iff,
    mem_canonicalBlockHighClaimDepths_iff]
  constructor
  · intro hd
    by_cases hdv : d ≤ canonicalBlockTerminalValuation n k
    · exact Or.inl ⟨hd, hdv⟩
    · exact Or.inr ⟨hd, by omega⟩
  · rintro (⟨hd, _⟩ | ⟨hd, _⟩) <;> exact hd

/-- The valuation cut makes the low and high depth families disjoint. -/
theorem canonicalBlockLowClaimDepths_disjoint_high
    (n : OddNat) (k : ℕ) :
    Disjoint (canonicalBlockLowClaimDepths n k)
      (canonicalBlockHighClaimDepths n k) := by
  classical
  apply Finset.disjoint_left.mpr
  intro d hdLow hdHigh
  have hlow := (mem_canonicalBlockLowClaimDepths_iff.mp hdLow).2
  have hhigh := (mem_canonicalBlockHighClaimDepths_iff.mp hdHigh).2
  omega

/-- Complete scalar claim count is the marked claim-depth cardinality. -/
theorem canonicalBlockClaimCount_eq_claimDepths_card
    (n : OddNat) (k : ℕ) :
    canonicalBlockClaimCount n k = (canonicalPaymentClaimDepths n k).card := by
  have hdepth := canonicalPaymentClaimDepths_card n k
  have hclaim := carryTwoPaymentClaimFiberAt_card_eq_growthDebt_card_add_endpoint_card
    n (paymentEndpointSeq n k)
      (orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n k)
  unfold canonicalBlockClaimCount
  omega

/-- Claim count splits exactly across the terminal-valuation cut. -/
theorem canonicalBlockClaimCount_eq_low_card_add_high_card
    (n : OddNat) (k : ℕ) :
    canonicalBlockClaimCount n k =
      (canonicalBlockLowClaimDepths n k).card +
        (canonicalBlockHighClaimDepths n k).card := by
  rw [canonicalBlockClaimCount_eq_claimDepths_card,
    canonicalPaymentClaimDepths_eq_low_union_high]
  exact Finset.card_union_of_disjoint
    (canonicalBlockLowClaimDepths_disjoint_high n k)

/-- There are at most `v` distinct positive claim depths at or below `v`. -/
theorem canonicalBlockLowClaimDepths_card_le_terminalValuation
    (n : OddNat) (k : ℕ) :
    (canonicalBlockLowClaimDepths n k).card ≤
      canonicalBlockTerminalValuation n k := by
  classical
  have hsubset : canonicalBlockLowClaimDepths n k ⊆
      Finset.Icc 1 (canonicalBlockTerminalValuation n k) := by
    intro d hd
    rcases mem_canonicalBlockLowClaimDepths_iff.mp hd with ⟨hdClaim, hdle⟩
    exact Finset.mem_Icc.mpr
      ⟨(mem_canonicalPaymentClaimDepths_iff.mp hdClaim).1, hdle⟩
  have hcard := Finset.card_le_card hsubset
  rw [Nat.card_Icc] at hcard
  omega

/-- Exact signed drift after splitting marked depths at the terminal valuation. -/
theorem endpointAccountingTerm_eq_high_card_sub_terminalValuation_sub_low_card
    (n : OddNat) (k : ℕ) :
    endpointAccountingTerm n k =
      ((canonicalBlockHighClaimDepths n k).card : ℤ) -
        (canonicalBlockTerminalValuation n k -
          (canonicalBlockLowClaimDepths n k).card : ℕ) := by
  rw [endpointAccountingTerm_eq_blockClaimCount_sub_capacityCount,
    canonicalBlockCapacityCount_eq_terminalValuation,
    canonicalBlockClaimCount_eq_low_card_add_high_card]
  have hlow := canonicalBlockLowClaimDepths_card_le_terminalValuation n k
  push_cast
  omega

/-- Positive low-depth cancellation can never make drift exceed the high count. -/
theorem endpointAccountingTerm_le_highClaimDepths_card
    (n : OddNat) (k : ℕ) :
    endpointAccountingTerm n k ≤
      (canonicalBlockHighClaimDepths n k).card := by
  rw [endpointAccountingTerm_eq_high_card_sub_terminalValuation_sub_low_card]
  exact sub_le_self _ (Int.natCast_nonneg _)

/-- A positive block must contain a marked depth above terminal capacity. -/
theorem canonicalBlockHighClaimDepths_nonempty_of_endpointAccountingTerm_pos
    {n : OddNat} {k : ℕ} (hpos : 0 < endpointAccountingTerm n k) :
    (canonicalBlockHighClaimDepths n k).Nonempty := by
  have hle := endpointAccountingTerm_le_highClaimDepths_card n k
  apply Finset.card_pos.mp
  omega

/-! ## High-depth claims inject into continuation pressure -/

/-- A high marked depth's exact source continues beyond terminal valuation. -/
theorem canonicalPaymentSourceAtDepth_mem_terminalContinuation_of_mem_high
    {n : OddNat} {k d : ℕ} (hd : d ∈ canonicalBlockHighClaimDepths n k) :
    canonicalPaymentSourceAtDepth n k d ∈
      canonicalPaymentBlockContinuationFiber n k
        (canonicalBlockTerminalValuation n k) := by
  rcases mem_canonicalBlockHighClaimDepths_iff.mp hd with ⟨hdClaim, hvd⟩
  rcases mem_canonicalPaymentClaimDepths_iff.mp hdClaim with
    ⟨hdpos, hdle, _⟩
  have hrecover : canonicalPaymentSourceAtDepth n k d ∈
      canonicalPaymentBlockRecoveryFiber n k d :=
    (mem_canonicalPaymentBlockRecoveryFiber_iff_eq_sourceAtDepth hdpos hdle).2 rfl
  rcases mem_canonicalPaymentBlockRecoveryFiber_iff.mp hrecover with
    ⟨hblock, hexact⟩
  apply mem_canonicalPaymentBlockContinuationFiber_iff.mpr
  refine ⟨hblock, ?_⟩
  have hdepth : orbitExactDepth n (canonicalPaymentSourceAtDepth n k d) = d := by
    simpa [OrbitDepthRecoversExactlyAt, orbitExactDepth] using hexact
  change canonicalBlockTerminalValuation n k + 1 ≤
    orbitExactDepth n (canonicalPaymentSourceAtDepth n k d)
  rw [hdepth]
  omega

/-- Source-at-depth is injective on valid marked canonical depths. -/
theorem canonicalPaymentSourceAtDepth_injective_on_claimDepths
    {n : OddNat} {k d e : ℕ}
    (hd : d ∈ canonicalPaymentClaimDepths n k)
    (he : e ∈ canonicalPaymentClaimDepths n k)
    (hsource : canonicalPaymentSourceAtDepth n k d =
      canonicalPaymentSourceAtDepth n k e) :
    d = e := by
  rcases mem_canonicalPaymentClaimDepths_iff.mp hd with ⟨hdpos, hdle, _⟩
  rcases mem_canonicalPaymentClaimDepths_iff.mp he with ⟨hepos, hele, _⟩
  have hdepthD := canonicalPaymentDebtDepth_sourceAtDepth n k d hdpos hdle
  have hdepthE := canonicalPaymentDebtDepth_sourceAtDepth n k e hepos hele
  rw [hsource] at hdepthD
  omega

/-- High-depth claims inject into the continuation fiber at terminal valuation. -/
theorem canonicalBlockHighClaimDepths_card_le_terminalContinuationFiber_card
    (n : OddNat) (k : ℕ) :
    (canonicalBlockHighClaimDepths n k).card ≤
      (canonicalPaymentBlockContinuationFiber n k
        (canonicalBlockTerminalValuation n k)).card := by
  classical
  apply Finset.card_le_card_of_injOn (canonicalPaymentSourceAtDepth n k)
  · intro d hd
    exact canonicalPaymentSourceAtDepth_mem_terminalContinuation_of_mem_high hd
  · intro d hd e he hsource
    exact canonicalPaymentSourceAtDepth_injective_on_claimDepths
      (mem_canonicalBlockHighClaimDepths_iff.mp hd).1
      (mem_canonicalBlockHighClaimDepths_iff.mp he).1 hsource

/-! ## Exact positive-pressure/saturated-border dichotomy -/

/-- The rigid border case: length just exceeds valuation and every source claims. -/
def CanonicalSaturatedBorderBlock (n : OddNat) (k : ℕ) : Prop :=
  canonicalBlockLength n k = canonicalBlockTerminalValuation n k + 1 ∧
    canonicalBlockClaimCount n k = canonicalBlockLength n k ∧
      endpointAccountingTerm n k = 1

/-- Saturation gives positive unit drift. -/
theorem CanonicalSaturatedBorderBlock.drift_pos
    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k) :
    0 < endpointAccountingTerm n k := by
  rw [h.2.2]
  norm_num

/-- Saturation lies exactly on the nonpositive-pressure border. -/
theorem CanonicalSaturatedBorderBlock.pressure_nonpos
    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k) :
    blockPressureContributionInt n k (canonicalBlockTerminalValuation n k) ≤ 0 := by
  have hvpos : 1 ≤ canonicalBlockTerminalValuation n k := by
    have hheight := two_le_orbitWindowHeight_paymentEndpointSeq n k
    rw [canonicalBlock_endpointHeight_eq_terminalValuation_add_one] at hheight
    omega
  rw [blockPressureContributionInt_eq]
  have hLen : canonicalPaymentBlockLength n k =
      canonicalBlockTerminalValuation n k + 1 := by
    simpa [canonicalBlockLength] using h.1
  simp [hvpos, hLen]

/-- Positive drift has either positive terminal-depth pressure or rigid saturation. -/
theorem positive_blockPressure_or_saturatedBorder_of_endpointAccountingTerm_pos
    {n : OddNat} {k : ℕ} (hpos : 0 < endpointAccountingTerm n k) :
    0 < blockPressureContributionInt n k (canonicalBlockTerminalValuation n k) ∨
      CanonicalSaturatedBorderBlock n k := by
  by_cases hp : 0 < blockPressureContributionInt n k
      (canonicalBlockTerminalValuation n k)
  · exact Or.inl hp
  · right
    have hvlt :=
      canonicalBlockTerminalValuation_lt_length_of_endpointAccountingTerm_pos hpos
    have hvpos : 1 ≤ canonicalBlockTerminalValuation n k := by
      by_contra hv
      have hvzero : canonicalBlockTerminalValuation n k = 0 := by omega
      rw [hvzero] at hp
      rw [blockPressureContributionInt_zero] at hp
      have hL := one_le_canonicalBlockLength n k
      have hLen : canonicalPaymentBlockLength n k = canonicalBlockLength n k := rfl
      rw [hLen] at hp
      omega
    have hpressure := blockPressureContributionInt_eq n k
      (canonicalBlockTerminalValuation n k)
    have hclaimLe := canonicalBlockClaimCount_le_length n k
    have hdrift := endpointAccountingTerm_eq_blockClaimCount_sub_capacityCount n k
    rw [canonicalBlockCapacityCount_eq_terminalValuation] at hdrift
    have hL : canonicalBlockLength n k = canonicalBlockTerminalValuation n k + 1 := by
      have hLen : canonicalPaymentBlockLength n k = canonicalBlockLength n k := rfl
      rw [hLen] at hpressure
      simp [hvpos, hvlt.le] at hpressure
      omega
    have hclaim : canonicalBlockClaimCount n k = canonicalBlockLength n k := by
      omega
    have hone : endpointAccountingTerm n k = 1 := by omega
    exact ⟨hL, hclaim, hone⟩

/-- Saturation is exactly the positive-drift, nonpositive-pressure branch. -/
theorem canonicalSaturatedBorderBlock_iff_positive_drift_and_pressure_nonpos
    (n : OddNat) (k : ℕ) :
    CanonicalSaturatedBorderBlock n k ↔
      0 < endpointAccountingTerm n k ∧
        blockPressureContributionInt n k
          (canonicalBlockTerminalValuation n k) ≤ 0 := by
  constructor
  · intro h
    exact ⟨h.drift_pos, h.pressure_nonpos⟩
  · rintro ⟨hpos, hpressure⟩
    rcases positive_blockPressure_or_saturatedBorder_of_endpointAccountingTerm_pos hpos with
      hp | hsaturated
    · omega
    · exact hsaturated

/-- In a saturated block every positive staircase depth is marked. -/
theorem CanonicalSaturatedBorderBlock.claimDepths_eq_Icc
    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k) :
    canonicalPaymentClaimDepths n k =
      Finset.Icc 1 (canonicalBlockLength n k) := by
  classical
  apply Finset.eq_of_subset_of_card_le
  · intro d hd
    rcases mem_canonicalPaymentClaimDepths_iff.mp hd with ⟨hdpos, hdle, _⟩
    exact Finset.mem_Icc.mpr ⟨hdpos, hdle⟩
  · rw [← canonicalBlockClaimCount_eq_claimDepths_card, h.2.1, Nat.card_Icc]
    have hL := one_le_canonicalBlockLength n k
    omega

/-! ## Saturated arithmetic normal form -/

/-- Saturated terminal valuation is exactly one below block length. -/
theorem CanonicalSaturatedBorderBlock.terminalValuation_eq_length_sub_one
    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k) :
    canonicalBlockTerminalValuation n k = canonicalBlockLength n k - 1 := by
  have hL := one_le_canonicalBlockLength n k
  have hEq := h.1
  omega

/-- A saturated endpoint has height exactly equal to its block length. -/
theorem CanonicalSaturatedBorderBlock.endpointHeight_eq_length
    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k) :
    orbitWindowHeight n (paymentEndpointSeq n k) = canonicalBlockLength n k := by
  rw [canonicalBlock_endpointHeight_eq_terminalValuation_add_one,
    h.terminalValuation_eq_length_sub_one]
  have hL := one_le_canonicalBlockLength n k
  omega

/-- Every source in a saturated canonical block has upper carry two. -/
theorem CanonicalSaturatedBorderBlock.carryTwo_of_mem
    {n : OddNat} {k i : ℕ} (h : CanonicalSaturatedBorderBlock n k)
    (hi : i ∈ canonicalPaymentBlock n k) :
    CarryTwoDebtAt n i := by
  let d := orbitExactDepth n i
  have hiRecovery : i ∈ canonicalPaymentBlockRecoveryFiber n k d := by
    apply mem_canonicalPaymentBlockRecoveryFiber_iff.mpr
    refine ⟨hi, ?_⟩
    change orbitExactDepth n i = d
    rfl
  have hvalid := (canonicalPaymentBlockRecoveryFiber_nonempty_iff n k d).mp
    ⟨i, hiRecovery⟩
  have hdClaim : d ∈ canonicalPaymentClaimDepths n k := by
    rw [h.claimDepths_eq_Icc]
    exact Finset.mem_Icc.mpr hvalid
  have hsource : i = canonicalPaymentSourceAtDepth n k d :=
    (mem_canonicalPaymentBlockRecoveryFiber_iff_eq_sourceAtDepth
      hvalid.1 hvalid.2).mp hiRecovery
  have hcarry := (mem_canonicalPaymentClaimDepths_iff.mp hdClaim).2.2
  simpa [← hsource] using hcarry

/-- Every strict canonical interior has the universal height-one staircase. -/
theorem CanonicalSaturatedBorderBlock.interior_height_eq_one
    {n : OddNat} {k i : ℕ} (_h : CanonicalSaturatedBorderBlock n k)
    (hi : i ∈ Finset.Ico (canonicalBlockStartTime n k)
      (paymentEndpointSeq n k)) :
    orbitWindowHeight n i = 1 := by
  apply orbitWindowHeight_eq_one_of_mem_universalPaymentBlockInterior
  simpa [canonicalBlockStartTime_eq_universalPaymentBlockStart] using hi

/-- Every strict saturated interior step increases bit width by exactly one. -/
theorem CanonicalSaturatedBorderBlock.interior_bitWidth_succ_eq_add_one
    {n : OddNat} {k i : ℕ} (h : CanonicalSaturatedBorderBlock n k)
    (hi : i ∈ Finset.Ico (canonicalBlockStartTime n k)
      (paymentEndpointSeq n k)) :
    bitWidth (iterateT (i + 1) n).1 = bitWidth (iterateT i n).1 + 1 := by
  have hheight := h.interior_height_eq_one hi
  have hs : s (iterateT i n) = 1 := by
    simpa [orbitWindowHeight_eq_s_iterateT] using hheight
  have hcarry : stateUpperCarry (iterateT i n).1 = 2 := by
    exact h.carryTwo_of_mem (by
      rw [canonicalPaymentBlock_eq_Icc_universalPaymentBlockStart]
      exact Finset.mem_Icc.mpr ⟨
        (Finset.mem_Ico.mp (by simpa
          [canonicalBlockStartTime_eq_universalPaymentBlockStart] using hi)).1,
        (Finset.mem_Ico.mp hi).2.le⟩)
  have hbalance := bitWidth_T_add_height_eq_bitWidth_add_upperCarry (iterateT i n)
  rw [iterateT_succ_eq_T_iterateT]
  rw [hs, hcarry] at hbalance
  omega

/-- Saturated blocks have exact unit net drift. -/
theorem CanonicalSaturatedBorderBlock.netDrift_eq_one
    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k) :
    endpointAccountingTerm n k = 1 := h.2.2

/-- Saturated block start and terminal carrier satisfy the exact power normal form. -/
theorem CanonicalSaturatedBorderBlock.normalForm
    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k) :
    canonicalBlockStartState n k + 1 =
        2 ^ canonicalBlockLength n k * canonicalBlockOddCore n k ∧
      v2 (3 ^ canonicalBlockLength n k * canonicalBlockOddCore n k - 1) =
        canonicalBlockLength n k - 1 := by
  exact ⟨canonicalBlockStartState_add_one_eq_pow_mul_oddCore n k, by
    change canonicalBlockTerminalValuation n k = canonicalBlockLength n k - 1
    exact h.terminalValuation_eq_length_sub_one⟩

/-- The exact saturated terminal two-power divides the terminal carrier. -/
theorem CanonicalSaturatedBorderBlock.pow_length_sub_one_dvd_terminalCarrier
    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k) :
    2 ^ (canonicalBlockLength n k - 1) ∣ canonicalBlockTerminalCarrier n k := by
  rw [← h.terminalValuation_eq_length_sub_one]
  simpa [v2] using
    (pow_padicValNat_dvd (p := 2) (n := canonicalBlockTerminalCarrier n k))

/-- Saturation is exact: the next power of two does not divide the carrier. -/
theorem CanonicalSaturatedBorderBlock.not_pow_length_dvd_terminalCarrier
    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k) :
    ¬ 2 ^ canonicalBlockLength n k ∣ canonicalBlockTerminalCarrier n k := by
  have hL := one_le_canonicalBlockLength n k
  have hnot := pow_succ_padicValNat_not_dvd
    (p := 2) (n := canonicalBlockTerminalCarrier n k)
  have hnot' := hnot (canonicalBlockTerminalCarrier_pos n k).ne'
  have hval : padicValNat 2 (canonicalBlockTerminalCarrier n k) =
      canonicalBlockLength n k - 1 := by
    simpa [canonicalBlockTerminalValuation, v2] using
      h.terminalValuation_eq_length_sub_one
  rw [hval] at hnot'
  simpa [show canonicalBlockLength n k - 1 + 1 = canonicalBlockLength n k by omega]
    using hnot'

/-- Modulo `2^(L-1)`, the saturated terminal carrier is exactly zero. -/
theorem CanonicalSaturatedBorderBlock.terminalCarrier_mod_pow_length_sub_one_eq_zero
    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k) :
    canonicalBlockTerminalCarrier n k % 2 ^ (canonicalBlockLength n k - 1) = 0 :=
  Nat.dvd_iff_mod_eq_zero.mp h.pow_length_sub_one_dvd_terminalCarrier

/-- Modulo `2^L`, the saturated terminal carrier remains nonzero. -/
theorem CanonicalSaturatedBorderBlock.terminalCarrier_mod_pow_length_ne_zero
    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k) :
    canonicalBlockTerminalCarrier n k % 2 ^ canonicalBlockLength n k ≠ 0 := by
  exact fun hzero => h.not_pow_length_dvd_terminalCarrier
    (Nat.dvd_iff_mod_eq_zero.mpr hzero)

/-!
## Saturated-successor audit and exact stopping point (cp-318)

The dedicated finite audit in
`python/Collatz/PetalBridge/saturated_block_audit.py` examined 65,536
consecutive odd roots and 1,280 deterministic random roots up to 1024 bits.
It found 33,435 saturated blocks.  All observed saturated blocks had length
two, no two observed saturated blocks were consecutive, and every observed
saturated run reached a later nonpositive-drift block within five blocks.

The simplest proposed successor rule is false: 1,785 saturated blocks had an
immediately following block with positive drift.  Consequently this module
does **not** export

`saturated block -> next block has nonpositive drift`.

The former stopping point has since been crossed in
`UniversalPaymentSaturatedSuccessor`.  The exact normal form and signed width
ledger prove that saturation has length two and that saturated blocks cannot
be consecutive.  That module also replaces the false unconditional successor
rule by the exact disjunction: the successor has nonpositive drift or positive
terminal-depth pressure.  The audit remains useful as evidence, but these two
structural facts no longer depend on it.
-/

/-- The non-saturated positive branch carries its dynamic terminal pressure depth. -/
structure CanonicalPositiveBlockPressureWitness (n : OddNat) where
  block : ℕ
  depth : ℕ := canonicalBlockTerminalValuation n block
  depth_eq : depth = canonicalBlockTerminalValuation n block := by rfl
  pressure_pos : 0 < blockPressureContributionInt n block depth

/-- A positive non-saturated block produces a block-local pressure witness. -/
theorem exists_positiveBlockPressureWitness_of_pos_of_not_saturated
    {n : OddNat} {k : ℕ} (hpos : 0 < endpointAccountingTerm n k)
    (hnot : ¬ CanonicalSaturatedBorderBlock n k) :
    ∃ W : CanonicalPositiveBlockPressureWitness n, W.block = k := by
  rcases positive_blockPressure_or_saturatedBorder_of_endpointAccountingTerm_pos hpos with
    hp | hsaturated
  · exact ⟨⟨k, canonicalBlockTerminalValuation n k, rfl, hp⟩, rfl⟩
  · exact (hnot hsaturated).elim

end DkMath.Collatz
