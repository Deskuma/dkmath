/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentPrimitiveExcursion

#print "file: DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentSaturatedSuccessor"

namespace DkMath.Collatz

/-!
# Saturated canonical blocks and their successors

This module replaces the finite cp-318 saturation observations by exact
arithmetic wherever possible.  The key input is not the audit: it is the
combination of the canonical block normal form with the signed width ledger.
-/

/-! ## Minimal saturation surface -/

/-- The unit-drift field of saturation follows from length and complete claims. -/
theorem canonicalSaturatedBorderBlock_iff_length_and_claims
    (n : OddNat) (k : ℕ) :
    CanonicalSaturatedBorderBlock n k ↔
      canonicalBlockLength n k = canonicalBlockTerminalValuation n k + 1 ∧
        canonicalBlockClaimCount n k = canonicalBlockLength n k := by
  constructor
  · intro h
    exact ⟨h.1, h.2.1⟩
  · rintro ⟨hlength, hclaims⟩
    refine ⟨hlength, hclaims, ?_⟩
    rw [endpointAccountingTerm_eq_blockClaimCount_sub_capacityCount,
      canonicalBlockCapacityCount_eq_terminalValuation, hclaims, hlength]
    norm_num

/-- Saturated pressure is exactly zero at the terminal valuation depth. -/
theorem CanonicalSaturatedBorderBlock.pressure_eq_zero
    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k) :
    blockPressureContributionInt n k (canonicalBlockTerminalValuation n k) = 0 := by
  have hvpos : 1 ≤ canonicalBlockTerminalValuation n k := by
    have hheight := two_le_orbitWindowHeight_paymentEndpointSeq n k
    rw [canonicalBlock_endpointHeight_eq_terminalValuation_add_one] at hheight
    omega
  apply blockPressureContributionInt_eq_zero_of_length_eq_succ hvpos
  simpa [canonicalBlockLength] using h.1

/-! ## Exponential comparison -/

/-- From length three onward, `3^L` lies below the relevant dyadic scale. -/
theorem three_pow_lt_two_pow_two_mul_sub_one {L : ℕ} (hL : 3 ≤ L) :
    3 ^ L < 2 ^ (2 * L - 1) := by
  induction L, hL using Nat.le_induction with
  | base => norm_num
  | succ L hL ih =>
      have hexp : 2 * (L + 1) - 1 = (2 * L - 1) + 2 := by omega
      rw [pow_succ, hexp, pow_add]
      have hpos : 0 < 2 ^ (2 * L - 1) := pow_pos (by norm_num) _
      nlinarith

/-- Multiplication by a positive core preserves the exponential comparison. -/
theorem three_pow_mul_lt_two_pow_two_mul_sub_one_mul
    {L u : ℕ} (hL : 3 ≤ L) (hu : 0 < u) :
    3 ^ L * u < 2 ^ (2 * L - 1) * u := by
  exact (Nat.mul_lt_mul_right hu).2 (three_pow_lt_two_pow_two_mul_sub_one hL)

/-- Binary width is monotone on positive natural words. -/
private theorem bitWidth_mono_of_pos {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) :
    bitWidth a ≤ bitWidth b := by
  have hb : 0 < b := ha.trans_le hab
  rw [bitWidth_eq_log_two_add_one ha.ne', bitWidth_eq_log_two_add_one hb.ne']
  exact Nat.add_le_add_right (Nat.log_mono_right hab) 1

/-! ## Saturated length -/

/-- Unit saturated drift is exact one-bit growth from block start to next start. -/
theorem CanonicalSaturatedBorderBlock.nextStart_bitWidth_eq_start_add_one
    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k) :
    bitWidth (canonicalBlockNextStartState n k) =
      bitWidth (canonicalBlockStartState n k) + 1 := by
  have hdrift := universalPaymentBlockSignedDriftAt_eq_bitWidth_sub n
    (paymentEndpointSeq n k)
    (orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n k)
  rw [← endpointAccountingTerm_eq_universalPaymentBlockSignedDriftAt, h.2.2] at hdrift
  unfold canonicalBlockNextStartState canonicalBlockStartState
  rw [canonicalBlockStartTime_eq_universalPaymentBlockStart]
  omega

/-- Length at least three would make the next start no larger than the old start. -/
theorem CanonicalSaturatedBorderBlock.nextStart_lt_start_add_one_of_three_le_length
    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k)
    (hL : 3 ≤ canonicalBlockLength n k) :
    canonicalBlockNextStartState n k < canonicalBlockStartState n k + 1 := by
  have hcore := canonicalBlockOddCore_pos n k
  have hpow := three_pow_mul_lt_two_pow_two_mul_sub_one_mul hL hcore
  rw [canonicalBlockNextStartState_eq_terminalCarrier_div_pow_valuation,
    h.terminalValuation_eq_length_sub_one]
  apply (Nat.div_lt_iff_lt_mul (pow_pos (by norm_num)
    (canonicalBlockLength n k - 1))).2
  rw [h.normalForm.1]
  calc
    canonicalBlockTerminalCarrier n k
        ≤ 3 ^ canonicalBlockLength n k * canonicalBlockOddCore n k := by
          unfold canonicalBlockTerminalCarrier
          omega
    _ < 2 ^ (2 * canonicalBlockLength n k - 1) *
          canonicalBlockOddCore n k := hpow
    _ = (2 ^ canonicalBlockLength n k * canonicalBlockOddCore n k) *
          2 ^ (canonicalBlockLength n k - 1) := by
          have hexp : 2 * canonicalBlockLength n k - 1 =
              canonicalBlockLength n k + (canonicalBlockLength n k - 1) := by
            omega
          rw [hexp, pow_add]
          ring

/-- Every saturated canonical block has length exactly two. -/
theorem CanonicalSaturatedBorderBlock.length_eq_two
    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k) :
    canonicalBlockLength n k = 2 := by
  have hvpos : 1 ≤ canonicalBlockTerminalValuation n k := by
    have hheight := two_le_orbitWindowHeight_paymentEndpointSeq n k
    rw [canonicalBlock_endpointHeight_eq_terminalValuation_add_one] at hheight
    omega
  have hLtwo : 2 ≤ canonicalBlockLength n k := by
    rw [h.1]
    omega
  by_contra hne
  have hLthree : 3 ≤ canonicalBlockLength n k := by omega
  have hnextLe : canonicalBlockNextStartState n k ≤ canonicalBlockStartState n k := by
    have := h.nextStart_lt_start_add_one_of_three_le_length hLthree
    omega
  have hnextPos : 0 < canonicalBlockNextStartState n k := by
    unfold canonicalBlockNextStartState
    have hodd := (iterateT (paymentEndpointSeq n k + 1) n).2
    omega
  have hwidthLe : bitWidth (canonicalBlockNextStartState n k) ≤
      bitWidth (canonicalBlockStartState n k) :=
    bitWidth_mono_of_pos hnextPos hnextLe
  rw [h.nextStart_bitWidth_eq_start_add_one] at hwidthLe
  omega

/-- Saturated terminal valuation is one. -/
theorem CanonicalSaturatedBorderBlock.terminalValuation_eq_one
    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k) :
    canonicalBlockTerminalValuation n k = 1 := by
  have hval := h.terminalValuation_eq_length_sub_one
  rw [h.length_eq_two] at hval
  exact hval

/-- Saturated endpoint height is two. -/
theorem CanonicalSaturatedBorderBlock.endpointHeight_eq_two
    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k) :
    orbitWindowHeight n (paymentEndpointSeq n k) = 2 := by
  rw [h.endpointHeight_eq_length, h.length_eq_two]

/-! ## Exact length-two normal form -/

/-- Saturated start state is one below four times its odd core. -/
theorem CanonicalSaturatedBorderBlock.startState_eq_four_mul_core_sub_one
    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k) :
    canonicalBlockStartState n k = 4 * canonicalBlockOddCore n k - 1 := by
  have hnormal := h.normalForm.1
  rw [h.length_eq_two] at hnormal
  norm_num at hnormal ⊢
  omega

/-- Saturated next start has the exact length-two quotient form. -/
theorem CanonicalSaturatedBorderBlock.nextStartState_eq
    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k) :
    canonicalBlockNextStartState n k =
      (9 * canonicalBlockOddCore n k - 1) / 2 := by
  rw [canonicalBlockNextStartState_eq_terminalCarrier_div_pow_valuation,
    h.terminalValuation_eq_one]
  unfold canonicalBlockTerminalCarrier
  rw [h.length_eq_two]
  norm_num

/-- The length-two terminal carrier has exact two-adic valuation one. -/
theorem CanonicalSaturatedBorderBlock.v2_nine_mul_core_sub_one_eq_one
    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k) :
    v2 (9 * canonicalBlockOddCore n k - 1) = 1 := by
  have hnormal := h.normalForm.2
  rw [h.length_eq_two] at hnormal
  norm_num at hnormal ⊢
  exact hnormal

/-- A saturated odd core is exactly in residue class three modulo four. -/
theorem CanonicalSaturatedBorderBlock.oddCore_mod_four_eq_three
    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k) :
    canonicalBlockOddCore n k % 4 = 3 := by
  have hnot : ¬ 4 ∣ 9 * canonicalBlockOddCore n k - 1 := by
    have hraw := h.not_pow_length_dvd_terminalCarrier
    rw [h.length_eq_two] at hraw
    simpa [canonicalBlockTerminalCarrier, h.length_eq_two] using hraw
  rcases odd_mod_four_eq_one_or_three
      (canonicalBlockOddCore_mod_two_eq_one n k) with hone | hthree
  · exfalso
    apply hnot
    rw [Nat.dvd_iff_mod_eq_zero]
    omega
  · exact hthree

/-- The mod-eight refinement leaves exactly the observed classes three and seven. -/
theorem CanonicalSaturatedBorderBlock.oddCore_mod_eight_eq_three_or_seven
    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k) :
    canonicalBlockOddCore n k % 8 = 3 ∨
      canonicalBlockOddCore n k % 8 = 7 := by
  rcases odd_mod_eight_eq_one_or_three_or_five_or_seven
      (canonicalBlockOddCore_mod_two_eq_one n k) with
    hone | hthree | hfive | hseven
  · have := h.oddCore_mod_four_eq_three
    omega
  · exact Or.inl hthree
  · have := h.oddCore_mod_four_eq_three
    omega
  · exact Or.inr hseven

/-! ## No consecutive saturated blocks -/

/-- The next canonical block starts at the state produced by the current block. -/
theorem canonicalBlockStartState_succ_eq_nextStartState
    (n : OddNat) (k : ℕ) :
    canonicalBlockStartState n (k + 1) = canonicalBlockNextStartState n k := by
  unfold canonicalBlockStartState canonicalBlockNextStartState
  rw [canonicalBlockStartTime_eq_universalPaymentBlockStart,
    universalPaymentBlockStart_paymentEndpointSeq_succ]

/--
The block following a saturated block starts with own-width carry one.

This is stronger than excluding a consecutive saturated block: the exact
length-two normal form leaves the raw word `3*y+1` strictly below the next
binary boundary at the successor start, independently of the successor
block's length or terminal valuation.
-/
theorem CanonicalSaturatedBorderBlock.nextStart_stateUpperCarry_eq_one
    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k) :
    stateUpperCarry (canonicalBlockStartState n (k + 1)) = 1 := by
  let u := canonicalBlockOddCore n k
  let x := canonicalBlockStartState n k
  let y := canonicalBlockStartState n (k + 1)
  have hu : 0 < u := canonicalBlockOddCore_pos n k
  have hu4 := h.oddCore_mod_four_eq_three
  have hu3 : 3 ≤ u := by omega
  have hx : x = 4 * u - 1 := h.startState_eq_four_mul_core_sub_one
  have hy : y = (9 * u - 1) / 2 := by
    dsimp [y]
    rw [canonicalBlockStartState_succ_eq_nextStartState]
    exact h.nextStartState_eq
  have hdvd : 2 ∣ 9 * u - 1 := by
    have hdvd := h.pow_length_sub_one_dvd_terminalCarrier
    simpa [u, canonicalBlockTerminalCarrier, h.length_eq_two] using hdvd
  have hyDouble : 2 * y = 9 * u - 1 := by
    rw [hy]
    have := Nat.div_mul_cancel hdvd
    omega
  have hraw : 3 * y + 1 < 4 * x := by omega
  have hxpos : 0 < x := by omega
  have hypos : 0 < y := by omega
  have hwidth : bitWidth y = bitWidth x + 1 := by
    simpa [x, y, canonicalBlockStartState_succ_eq_nextStartState] using
      h.nextStart_bitWidth_eq_start_add_one
  have hxpow := lt_pow_bitWidth hxpos
  have hbelow : 3 * y + 1 < 2 ^ (bitWidth y + 1) := by
    calc
      3 * y + 1 < 4 * x := hraw
      _ < 4 * 2 ^ bitWidth x := by omega
      _ = 2 ^ (bitWidth y + 1) := by
        rw [hwidth]
        simp [pow_succ]
        ring
  rcases stateUpperCarry_one_or_two hypos with hone | htwo
  · exact hone
  · have hcross :=
      (stateUpperCarry_eq_two_iff_pow_succ_le_threeNPlusOne hypos).1 htwo
    omega

/-- A two-bit width increase forces more than a doubling of positive words. -/
private theorem two_mul_lt_of_bitWidth_eq_add_two
    {x y : ℕ} (hx : 0 < x) (hy : 0 < y)
    (hwidth : bitWidth y = bitWidth x + 2) :
    2 * x < y := by
  have hxlt := lt_pow_bitWidth hx
  have hylead := pow_bitWidth_sub_one_le hy
  have hpow : 2 ^ (bitWidth x + 1) ≤ y := by
    rw [hwidth] at hylead
    simpa using hylead
  calc
    2 * x < 2 * 2 ^ bitWidth x :=
      (Nat.mul_lt_mul_left (by norm_num : 0 < 2)).2 hxlt
    _ = 2 ^ (bitWidth x + 1) := by rw [pow_succ]; ring
    _ ≤ y := hpow

/-- Saturated blocks cannot occur at consecutive canonical indices. -/
theorem CanonicalSaturatedBorderBlock.not_succ
    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k) :
    ¬ CanonicalSaturatedBorderBlock n (k + 1) := by
  intro hnext
  let u := canonicalBlockOddCore n k
  let u' := canonicalBlockOddCore n (k + 1)
  let x₀ := canonicalBlockStartState n k
  let x₁ := canonicalBlockNextStartState n k
  let x₂ := canonicalBlockNextStartState n (k + 1)
  have hu : 0 < u := canonicalBlockOddCore_pos n k
  have hx₀ : x₀ = 4 * u - 1 := h.startState_eq_four_mul_core_sub_one
  have hx₁ : x₁ = (9 * u - 1) / 2 := h.nextStartState_eq
  have hstart₁ : canonicalBlockStartState n (k + 1) = x₁ :=
    canonicalBlockStartState_succ_eq_nextStartState n k
  have hstart₁core : canonicalBlockStartState n (k + 1) = 4 * u' - 1 :=
    hnext.startState_eq_four_mul_core_sub_one
  have hx₂ : x₂ = (9 * u' - 1) / 2 := hnext.nextStartState_eq
  have hdvd₁ : 2 ∣ 9 * u - 1 := by
    have hdvd := h.pow_length_sub_one_dvd_terminalCarrier
    simpa [u, canonicalBlockTerminalCarrier, h.length_eq_two] using hdvd
  have hdvd₂ : 2 ∣ 9 * u' - 1 := by
    have hdvd := hnext.pow_length_sub_one_dvd_terminalCarrier
    simpa [u', canonicalBlockTerminalCarrier, hnext.length_eq_two] using hdvd
  have hdouble₁ : 2 * x₁ = 9 * u - 1 := by
    rw [hx₁]
    have := Nat.div_mul_cancel hdvd₁
    omega
  have hdouble₂ : 2 * x₂ = 9 * u' - 1 := by
    rw [hx₂]
    have := Nat.div_mul_cancel hdvd₂
    omega
  have hu' : 8 * u' = 9 * u + 1 := by
    omega
  have hx₂closed : 16 * x₂ = 81 * u + 1 := by
    omega
  have hx₂lt : x₂ < 2 * x₀ := by
    omega
  have hx₀pos : 0 < x₀ := by omega
  have hx₂pos : 0 < x₂ := by
    unfold x₂ canonicalBlockNextStartState
    have hodd := (iterateT (paymentEndpointSeq n (k + 1) + 1) n).2
    omega
  have hwidth₁ := h.nextStart_bitWidth_eq_start_add_one
  have hwidth₂ := hnext.nextStart_bitWidth_eq_start_add_one
  have hwidth : bitWidth x₂ = bitWidth x₀ + 2 := by
    change bitWidth x₁ = bitWidth x₀ + 1 at hwidth₁
    change bitWidth x₂ = bitWidth (canonicalBlockStartState n (k + 1)) + 1 at hwidth₂
    rw [hstart₁] at hwidth₂
    omega
  have hx₂gt : 2 * x₀ < x₂ :=
    two_mul_lt_of_bitWidth_eq_add_two hx₀pos hx₂pos hwidth
  omega

/-! ## Correct saturated-successor pressure theorem -/

/-- A saturated block is followed by nonpositive drift or positive pressure. -/
theorem CanonicalSaturatedBorderBlock.successor_nonpos_or_pressure_pos
    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k) :
    endpointAccountingTerm n (k + 1) ≤ 0 ∨
      0 < blockPressureContributionInt n (k + 1)
        (canonicalBlockTerminalValuation n (k + 1)) := by
  by_cases hpos : 0 < endpointAccountingTerm n (k + 1)
  · right
    rcases positive_blockPressure_or_saturatedBorder_of_endpointAccountingTerm_pos
      hpos with hpressure | hsaturated
    · exact hpressure
    · exact (h.not_succ hsaturated).elim
  · exact Or.inl (by omega)

/-! ## Sharper pressure depth -/

/-- Positive drift is dominated by pressure one level before a terminal
valuation of at least two.  At that depth the pressure is exactly `L - v`,
the same universal upper bound supplied by the endpoint ledger. -/
theorem endpointAccountingTerm_le_blockPressure_pred_terminal
    {n : OddNat} {k : ℕ}
    (hpos : 0 < endpointAccountingTerm n k)
    (hv : 2 ≤ canonicalBlockTerminalValuation n k) :
    endpointAccountingTerm n k ≤
      blockPressureContributionInt n k
        (canonicalBlockTerminalValuation n k - 1) := by
  let v := canonicalBlockTerminalValuation n k
  let L := canonicalBlockLength n k
  have hvlt : v < L :=
    canonicalBlockTerminalValuation_lt_length_of_endpointAccountingTerm_pos hpos
  have hdrift := endpointAccountingTerm_le_length_sub_capacity n k
  rw [canonicalBlockCapacityCount_eq_terminalValuation] at hdrift
  have hpressure :=
    blockPressureContributionInt_eq_sub_sub_one_of_add_two_le_length
      (n := n) (k := k) (d := v - 1) (by omega) (by
        change v - 1 + 2 ≤ L
        omega)
  have hpressureExact :
      blockPressureContributionInt n k (v - 1) = (L : ℤ) - v := by
    rw [hpressure]
    change ((L - (v - 1) : ℕ) : ℤ) - 1 = (L : ℤ) - v
    omega
  rw [hpressureExact]
  exact hdrift

/-- At terminal valuation one, positive length-two blocks are precisely the
saturated border blocks; every nonsaturated alternative has length at least
three and positive pressure at depth one. -/
theorem positive_terminalValuation_one_saturated_or_length_three_pressure
    {n : OddNat} {k : ℕ}
    (hpos : 0 < endpointAccountingTerm n k)
    (hv : canonicalBlockTerminalValuation n k = 1) :
    CanonicalSaturatedBorderBlock n k ∨
      (3 ≤ canonicalBlockLength n k ∧
        0 < blockPressureContributionInt n k 1) := by
  rcases positive_blockPressure_or_saturatedBorder_of_endpointAccountingTerm_pos
      hpos with hpressure | hsaturated
  · right
    constructor
    · have hvlt :=
        canonicalBlockTerminalValuation_lt_length_of_endpointAccountingTerm_pos hpos
      by_contra hL
      have hLtwo : canonicalBlockLength n k = 2 := by omega
      have hclaimLe := canonicalBlockClaimCount_le_length n k
      have hdrift := endpointAccountingTerm_eq_blockClaimCount_sub_capacityCount n k
      rw [canonicalBlockCapacityCount_eq_terminalValuation, hv] at hdrift
      rw [hLtwo] at hclaimLe
      have hclaims : canonicalBlockClaimCount n k = 2 := by omega
      have hsaturated : CanonicalSaturatedBorderBlock n k :=
        (canonicalSaturatedBorderBlock_iff_length_and_claims n k).2
          ⟨by omega, by simpa [hLtwo] using hclaims⟩
      rw [hsaturated.pressure_eq_zero] at hpressure
      omega
    · simpa [hv] using hpressure
  · exact Or.inl hsaturated

/-! ## Finite saturated sets and open-excursion decomposition -/

/-- Actual saturated canonical indices in the closed block interval `q..m`. -/
noncomputable def canonicalSaturatedBlockIndices
    (n : OddNat) (q m : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc q m).filter (CanonicalSaturatedBorderBlock n)

/-- Positive-pressure canonical indices in the closed block interval `q..m`. -/
noncomputable def canonicalPositivePressureBlockIndices
    (n : OddNat) (q m : ℕ) : Finset ℕ :=
  (Finset.Icc q m).filter fun k =>
    0 < endpointAccountingTerm n k ∧
      0 < blockPressureContributionInt n k
        (canonicalBlockTerminalValuation n k)

/-- Nonpositive-drift canonical indices in the closed block interval `q..m`. -/
noncomputable def canonicalNonpositiveBlockIndices
    (n : OddNat) (q m : ℕ) : Finset ℕ :=
  (Finset.Icc q m).filter fun k => endpointAccountingTerm n k ≤ 0

@[simp] theorem mem_canonicalSaturatedBlockIndices
    {n : OddNat} {q m k : ℕ} :
    k ∈ canonicalSaturatedBlockIndices n q m ↔
      k ∈ Finset.Icc q m ∧ CanonicalSaturatedBorderBlock n k := by
  simp [canonicalSaturatedBlockIndices]

@[simp] theorem mem_canonicalPositivePressureBlockIndices
    {n : OddNat} {q m k : ℕ} :
    k ∈ canonicalPositivePressureBlockIndices n q m ↔
      k ∈ Finset.Icc q m ∧ 0 < endpointAccountingTerm n k ∧
        0 < blockPressureContributionInt n k
          (canonicalBlockTerminalValuation n k) := by
  simp [canonicalPositivePressureBlockIndices]

@[simp] theorem mem_canonicalNonpositiveBlockIndices
    {n : OddNat} {q m k : ℕ} :
    k ∈ canonicalNonpositiveBlockIndices n q m ↔
      k ∈ Finset.Icc q m ∧ endpointAccountingTerm n k ≤ 0 := by
  simp [canonicalNonpositiveBlockIndices]

/-- Saturated membership excludes membership of the immediate successor. -/
theorem canonicalSaturatedBlockIndices_not_succ_mem
    {n : OddNat} {q m k : ℕ}
    (hk : k ∈ canonicalSaturatedBlockIndices n q m) :
    k + 1 ∉ canonicalSaturatedBlockIndices n q m := by
  intro hsucc
  exact (mem_canonicalSaturatedBlockIndices.mp hk).2.not_succ
    (mem_canonicalSaturatedBlockIndices.mp hsucc).2

/-- Isolated saturation occupies at most every other slot of a finite interval. -/
theorem two_mul_card_canonicalSaturatedBlockIndices_le
    (n : OddNat) (q m : ℕ) :
    2 * (canonicalSaturatedBlockIndices n q m).card ≤ m - q + 2 := by
  classical
  let S := canonicalSaturatedBlockIndices n q m
  let T := S.image fun k => k + 1
  have hdisjoint : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro x hxS hxT
    rcases Finset.mem_image.mp hxT with ⟨k, hkS, hkx⟩
    subst x
    exact canonicalSaturatedBlockIndices_not_succ_mem hkS hxS
  have hsubset : S ∪ T ⊆ Finset.Icc q (m + 1) := by
    intro x hx
    rcases Finset.mem_union.mp hx with hxS | hxT
    · change x ∈ canonicalSaturatedBlockIndices n q m at hxS
      have hxIcc := (mem_canonicalSaturatedBlockIndices.mp hxS).1
      simp only [Finset.mem_Icc] at hxIcc
      rcases hxIcc with ⟨hqx, hxm⟩
      exact Finset.mem_Icc.mpr ⟨hqx, by omega⟩
    · rcases Finset.mem_image.mp hxT with ⟨k, hkS, rfl⟩
      change k ∈ canonicalSaturatedBlockIndices n q m at hkS
      have hkIcc := (mem_canonicalSaturatedBlockIndices.mp hkS).1
      simp only [Finset.mem_Icc] at hkIcc
      rcases hkIcc with ⟨hqk, hkm⟩
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hcardT : T.card = S.card := by
    exact Finset.card_image_iff.mpr (fun _ _ _ _ h => by omega)
  have hcardUnion : (S ∪ T).card = S.card + T.card :=
    Finset.card_union_of_disjoint hdisjoint
  have hle := Finset.card_le_card hsubset
  rw [hcardUnion, hcardT] at hle
  change 2 * S.card ≤ m - q + 2
  calc
    2 * S.card = S.card + S.card := by omega
    _ ≤ (Finset.Icc q (m + 1)).card := hle
    _ = m + 2 - q := by rw [Nat.card_Icc]
    _ ≤ m - q + 2 := by omega

/-- The same packing bound applies to the observed interval of an open excursion. -/
theorem CanonicalOpenPositiveQueueExcursion.two_mul_card_saturated_le
    {n : OddNat} {q m : ℕ}
    (_hopen : CanonicalOpenPositiveQueueExcursion n q m) :
    2 * (canonicalSaturatedBlockIndices n q m).card ≤ m - q + 2 :=
  two_mul_card_canonicalSaturatedBlockIndices_le n q m

/-- A positive-drift block in a finite interval belongs to exactly one of the
positive-pressure and saturated families. -/
theorem canonicalPositiveDrift_mem_pressure_xor_saturated
    {n : OddNat} {q m k : ℕ} (hk : k ∈ Finset.Icc q m)
    (hpos : 0 < endpointAccountingTerm n k) :
    (k ∈ canonicalPositivePressureBlockIndices n q m ∧
        k ∉ canonicalSaturatedBlockIndices n q m) ∨
      (k ∈ canonicalSaturatedBlockIndices n q m ∧
        k ∉ canonicalPositivePressureBlockIndices n q m) := by
  rcases positive_blockPressure_or_saturatedBorder_of_endpointAccountingTerm_pos
      hpos with hpressure | hsaturated
  · left
    refine ⟨mem_canonicalPositivePressureBlockIndices.mpr
      ⟨hk, hpos, hpressure⟩, ?_⟩
    intro hs
    have hsaturated := (mem_canonicalSaturatedBlockIndices.mp hs).2
    rw [hsaturated.pressure_eq_zero] at hpressure
    omega
  · right
    refine ⟨mem_canonicalSaturatedBlockIndices.mpr ⟨hk, hsaturated⟩, ?_⟩
    intro hp
    have hpressure := (mem_canonicalPositivePressureBlockIndices.mp hp).2.2
    rw [hsaturated.pressure_eq_zero] at hpressure
    omega

/-- On an open observed excursion, every positive-drift block still has the
exact pressure/saturation split; no future repayment endpoint is used. -/
theorem CanonicalOpenPositiveQueueExcursion.positive_mem_pressure_xor_saturated
    {n : OddNat} {q m k : ℕ}
    (_hopen : CanonicalOpenPositiveQueueExcursion n q m)
    (hk : k ∈ Finset.Icc q m)
    (hpos : 0 < endpointAccountingTerm n k) :
    (k ∈ canonicalPositivePressureBlockIndices n q m ∧
        k ∉ canonicalSaturatedBlockIndices n q m) ∨
      (k ∈ canonicalSaturatedBlockIndices n q m ∧
        k ∉ canonicalPositivePressureBlockIndices n q m) :=
  canonicalPositiveDrift_mem_pressure_xor_saturated hk hpos

/-- Saturated indices remain isolated inside every open observed excursion. -/
theorem CanonicalOpenPositiveQueueExcursion.saturated_not_succ_mem
    {n : OddNat} {q m k : ℕ}
    (_hopen : CanonicalOpenPositiveQueueExcursion n q m)
    (hk : k ∈ canonicalSaturatedBlockIndices n q m) :
    k + 1 ∉ canonicalSaturatedBlockIndices n q m :=
  canonicalSaturatedBlockIndices_not_succ_mem hk

/-! ## Dynamic-depth pressure accounting -/

/-- Every canonical endpoint has positive terminal two-adic valuation. -/
theorem one_le_canonicalBlockTerminalValuation (n : OddNat) (k : ℕ) :
    1 ≤ canonicalBlockTerminalValuation n k := by
  have hheight := two_le_orbitWindowHeight_paymentEndpointSeq n k
  rw [canonicalBlock_endpointHeight_eq_terminalValuation_add_one] at hheight
  omega

/-- A block-dependent pressure depth.  Saturation remains at its zero-pressure
terminal depth so that its exceptional unit is visible; ordinary blocks use
the quantitatively stronger predecessor depth whenever available. -/
noncomputable def canonicalDynamicPressureDepth
    (n : OddNat) (k : ℕ) : ℕ := by
  classical
  exact if CanonicalSaturatedBorderBlock n k then
      canonicalBlockTerminalValuation n k
    else if 2 ≤ canonicalBlockTerminalValuation n k then
      canonicalBlockTerminalValuation n k - 1
    else 0

/-- Dependent-pair presentation of a block and its selected pressure depth. -/
noncomputable def canonicalDynamicPressureWitness
    (n : OddNat) (k : ℕ) : Σ _block : ℕ, ℕ :=
  ⟨k, canonicalDynamicPressureDepth n k⟩

/-- Indicator charge carried by a saturated canonical block. -/
noncomputable def canonicalSaturatedUnit (n : OddNat) (k : ℕ) : ℤ := by
  classical
  exact if CanonicalSaturatedBorderBlock n k then 1 else 0

/-- Pointwise dynamic-depth domination.  Exactly saturated blocks consume the
explicit unit surcharge; every nonsaturated positive block is paid by its
selected local pressure contribution. -/
theorem endpointAccountingTerm_le_dynamicPressure_add_saturatedUnit
    {n : OddNat} {k : ℕ} (hpos : 0 < endpointAccountingTerm n k) :
    endpointAccountingTerm n k ≤
      blockPressureContributionInt n k (canonicalDynamicPressureDepth n k) +
        canonicalSaturatedUnit n k := by
  classical
  by_cases hs : CanonicalSaturatedBorderBlock n k
  · simp only [canonicalDynamicPressureDepth, hs, ↓reduceIte, canonicalSaturatedUnit]
    rw [hs.pressure_eq_zero, hs.2.2]
    norm_num
  · simp only [canonicalDynamicPressureDepth, canonicalSaturatedUnit, if_neg hs,
      add_zero]
    by_cases hv : 2 ≤ canonicalBlockTerminalValuation n k
    · rw [if_pos hv]
      exact endpointAccountingTerm_le_blockPressure_pred_terminal hpos hv
    · rw [if_neg hv]
      rw [blockPressureContributionInt_zero]
      have hdrift := endpointAccountingTerm_le_length_sub_capacity n k
      rw [canonicalBlockCapacityCount_eq_terminalValuation] at hdrift
      have hvone := one_le_canonicalBlockTerminalValuation n k
      have hLen : canonicalPaymentBlockLength n k = canonicalBlockLength n k := rfl
      rw [hLen]
      omega

/-- Actual positive-drift indices in a closed finite interval. -/
noncomputable def canonicalPositiveDriftBlockIndices
    (n : OddNat) (q m : ℕ) : Finset ℕ :=
  (Finset.Icc q m).filter fun k => 0 < endpointAccountingTerm n k

/-- Finite dynamic-depth aggregation with isolated saturation retained as an
explicit unit charge. -/
theorem sum_positiveDrift_le_dynamicPressure_add_saturatedUnits
    (n : OddNat) (q m : ℕ) :
    (∑ k ∈ canonicalPositiveDriftBlockIndices n q m,
        endpointAccountingTerm n k) ≤
      (∑ k ∈ canonicalPositiveDriftBlockIndices n q m,
        (blockPressureContributionInt n k (canonicalDynamicPressureDepth n k) +
          canonicalSaturatedUnit n k)) := by
  classical
  refine Finset.sum_le_sum
    (s := canonicalPositiveDriftBlockIndices n q m)
    (f := fun k => endpointAccountingTerm n k)
    (g := fun k => blockPressureContributionInt n k
      (canonicalDynamicPressureDepth n k) + canonicalSaturatedUnit n k)
    (fun k hk => ?_)
  have hpos : 0 < endpointAccountingTerm n k := by
    change k ∈ (Finset.Icc q m).filter
      (fun j => 0 < endpointAccountingTerm n j) at hk
    exact (Finset.mem_filter.mp hk).2
  exact endpointAccountingTerm_le_dynamicPressure_add_saturatedUnit hpos

/-- The finite surcharge sum is exactly the number of saturated indices. -/
theorem sum_saturatedUnit_positiveIndices_eq_card
    (n : OddNat) (q m : ℕ) :
    (∑ k ∈ canonicalPositiveDriftBlockIndices n q m,
      canonicalSaturatedUnit n k) =
      (canonicalSaturatedBlockIndices n q m).card := by
  classical
  simp only [canonicalPositiveDriftBlockIndices, canonicalSaturatedUnit, Finset.sum_boole,
    canonicalSaturatedBlockIndices, Nat.cast_inj]
  congr 1
  ext k
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨⟨hk, _hpos⟩, hs⟩
    exact ⟨hk, hs⟩
  · rintro ⟨hk, hs⟩
    exact ⟨⟨hk, hs.drift_pos⟩, hs⟩

/-- Accounting shape with dynamic pressure mass and the cardinality of the
isolated saturated family displayed as separate terms. -/
theorem sum_positiveDrift_le_dynamicPressureMass_add_saturatedCard
    (n : OddNat) (q m : ℕ) :
    (∑ k ∈ canonicalPositiveDriftBlockIndices n q m,
        endpointAccountingTerm n k) ≤
      (∑ k ∈ canonicalPositiveDriftBlockIndices n q m,
        blockPressureContributionInt n k (canonicalDynamicPressureDepth n k)) +
          (canonicalSaturatedBlockIndices n q m).card := by
  have h := sum_positiveDrift_le_dynamicPressure_add_saturatedUnits n q m
  rw [Finset.sum_add_distrib,
    sum_saturatedUnit_positiveIndices_eq_card] at h
  exact h

/-! ## Exact successor grammar -/

/-- After a saturated block, the next start plus one is half of `9*u+1`. -/
theorem CanonicalSaturatedBorderBlock.nextStartState_add_one_eq
    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k) :
    canonicalBlockNextStartState n k + 1 =
      (9 * canonicalBlockOddCore n k + 1) / 2 := by
  let u := canonicalBlockOddCore n k
  have huodd := canonicalBlockOddCore_mod_two_eq_one n k
  have hdvdMinus : 2 ∣ 9 * u - 1 := by
    rw [Nat.dvd_iff_mod_eq_zero]
    omega
  have hdvdPlus : 2 ∣ 9 * u + 1 := by
    rw [Nat.dvd_iff_mod_eq_zero]
    omega
  rw [h.nextStartState_eq]
  have hminus := Nat.div_mul_cancel hdvdMinus
  have hplus := Nat.div_mul_cancel hdvdPlus
  omega

/-- The next canonical length is the valuation of the exact successor word. -/
theorem CanonicalSaturatedBorderBlock.nextBlockLength_eq_v2_half_nine_core_add_one
    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k) :
    canonicalBlockLength n (k + 1) =
      v2 ((9 * canonicalBlockOddCore n k + 1) / 2) := by
  rw [canonicalBlockLength_eq_v2_startState_add_one,
    canonicalBlockStartState_succ_eq_nextStartState, h.nextStartState_add_one_eq]

/-- Residue class three modulo eight produces a next block of length one. -/
theorem CanonicalSaturatedBorderBlock.nextBlockLength_eq_one_of_core_mod_eight_eq_three
    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k)
    (hu : canonicalBlockOddCore n k % 8 = 3) :
    canonicalBlockLength n (k + 1) = 1 := by
  let u := canonicalBlockOddCore n k
  let y := (9 * u + 1) / 2
  have hdecomp : u = 8 * (u / 8) + 3 := by
    have := Nat.mod_add_div u 8
    omega
  have hy : y = 36 * (u / 8) + 14 := by
    dsimp [y]
    omega
  have hyeven : y % 2 = 0 := by rw [hy]; omega
  have hypos : 0 < y := by rw [hy]; omega
  have hyhalfodd : (y / 2) % 2 = 1 := by rw [hy]; omega
  rw [h.nextBlockLength_eq_v2_half_nine_core_add_one]
  change v2 y = 1
  rw [v2_step_of_even y hyeven hypos, v2_odd _ hyhalfodd]

/-- Residue class seven modulo eight produces a next block of length at least two. -/
theorem CanonicalSaturatedBorderBlock.two_le_nextBlockLength_of_core_mod_eight_eq_seven
    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k)
    (hu : canonicalBlockOddCore n k % 8 = 7) :
    2 ≤ canonicalBlockLength n (k + 1) := by
  let u := canonicalBlockOddCore n k
  let y := (9 * u + 1) / 2
  have hdecomp : u = 8 * (u / 8) + 7 := by
    have := Nat.mod_add_div u 8
    omega
  have hy : y = 36 * (u / 8) + 32 := by
    dsimp [y]
    omega
  have hypos : 0 < y := by rw [hy]; omega
  have hfour : 4 ∣ y := by
    rw [hy]
    exact ⟨9 * (u / 8) + 8, by ring⟩
  rw [h.nextBlockLength_eq_v2_half_nine_core_add_one]
  change 2 ≤ v2 y
  exact (two_le_v2_iff_four_dvd hypos.ne').2 hfour

end DkMath.Collatz
