/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentSaturatedSuccessor

#print "file: DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentSelectedCarrier"

namespace DkMath.Collatz

/-!
# Positive-depth pressure carriers

This module removes the coarse depth-zero branch from the cp-319 dynamic
pressure surface.  It keeps source incidences inside their canonical blocks;
global resource transport is deliberately a later layer.
-/

/-! ## Full claims force saturation -/

/-- Strengthened dyadic comparison used when every source claims carry two. -/
theorem three_pow_add_two_pow_pred_le_two_pow_two_mul_sub_one
    {L : ℕ} (hL : 3 ≤ L) :
    3 ^ L + 2 ^ (L - 1) ≤ 2 ^ (2 * L - 1) := by
  induction L, hL using Nat.le_induction with
  | base => norm_num
  | succ L hL ih =>
      have hexp : 2 * (L + 1) - 1 = (2 * L - 1) + 2 := by omega
      have htwo : 2 ^ L = 2 * 2 ^ (L - 1) := by
        have heq : L = (L - 1) + 1 := by omega
        calc
          2 ^ L = 2 ^ ((L - 1) + 1) := congrArg (fun e => 2 ^ e) heq
          _ = 2 ^ (L - 1) * 2 := by rw [pow_succ]
          _ = 2 * 2 ^ (L - 1) := by omega
      have hright : 0 < 2 ^ (2 * L - 1) := pow_pos (by norm_num) _
      calc
        3 ^ (L + 1) + 2 ^ (L + 1 - 1) =
            3 * 3 ^ L + 2 * 2 ^ (L - 1) := by
              rw [pow_succ]
              have hpred : L + 1 - 1 = L := by omega
              rw [hpred, htwo]
              ring
        _ ≤ 3 * (3 ^ L + 2 ^ (L - 1)) := by omega
        _ ≤ 3 * 2 ^ (2 * L - 1) :=
          Nat.mul_le_mul_left 3 ih
        _ ≤ 4 * 2 ^ (2 * L - 1) := by omega
        _ = 2 ^ (2 * (L + 1) - 1) := by
          rw [hexp, pow_add]
          norm_num
          ring

/-- Positive drift together with complete claims is rigid saturation. -/
theorem canonicalSaturatedBorderBlock_of_pos_of_claimCount_eq_length
    {n : OddNat} {k : ℕ}
    (hpos : 0 < endpointAccountingTerm n k)
    (hclaims : canonicalBlockClaimCount n k = canonicalBlockLength n k) :
    CanonicalSaturatedBorderBlock n k := by
  let L := canonicalBlockLength n k
  let v := canonicalBlockTerminalValuation n k
  let u := canonicalBlockOddCore n k
  let x := canonicalBlockStartState n k
  let x' := canonicalBlockNextStartState n k
  have hvpos : 1 ≤ v := one_le_canonicalBlockTerminalValuation n k
  have hvlt : v < L :=
    canonicalBlockTerminalValuation_lt_length_of_endpointAccountingTerm_pos hpos
  have hdrift := endpointAccountingTerm_eq_blockClaimCount_sub_capacityCount n k
  rw [canonicalBlockCapacityCount_eq_terminalValuation, hclaims] at hdrift
  have hwidthRaw := universalPaymentBlockSignedDriftAt_eq_bitWidth_sub n
    (paymentEndpointSeq n k)
    (orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n k)
  rw [← endpointAccountingTerm_eq_universalPaymentBlockSignedDriftAt] at hwidthRaw
  have hwidth : bitWidth x' = bitWidth x + (L - v) := by
    unfold x' x canonicalBlockNextStartState canonicalBlockStartState
    rw [canonicalBlockStartTime_eq_universalPaymentBlockStart]
    omega
  have hLtwo : 2 ≤ L := by omega
  by_cases hL : L = 2
  · apply (canonicalSaturatedBorderBlock_iff_length_and_claims n k).2
    constructor
    · change L = v + 1
      omega
    · exact hclaims
  · have hLthree : 3 ≤ L := by omega
    have hu : 0 < u := canonicalBlockOddCore_pos n k
    have hxpos : 0 < x := by
      unfold x canonicalBlockStartState
      have hodd := (iterateT (canonicalBlockStartTime n k) n).2
      omega
    have hx'pos : 0 < x' := by
      unfold x' canonicalBlockNextStartState
      have hodd := (iterateT (paymentEndpointSeq n k + 1) n).2
      omega
    have hnormal : x + 1 = 2 ^ L * u := by
      exact canonicalBlockStartState_add_one_eq_pow_mul_oddCore n k
    have hterminal : canonicalBlockTerminalCarrier n k = 3 ^ L * u - 1 := by
      rfl
    have hscale : 0 < 2 ^ (L - v) := pow_pos (by norm_num) _
    have hupperScaled :
        3 ^ L * u + 2 ^ (L - 1) ≤ 2 ^ (2 * L - 1) * u := by
      have hbase := three_pow_add_two_pow_pred_le_two_pow_two_mul_sub_one hLthree
      have hmul := Nat.mul_le_mul_right u hbase
      have hone : 1 ≤ u := hu
      nlinarith [Nat.mul_le_mul_left (2 ^ (L - 1)) hone]
    have hpowSplit :
        2 ^ (2 * L - 1) = 2 ^ (L - 1) * 2 ^ L := by
      have hexp : 2 * L - 1 = (L - 1) + L := by omega
      rw [hexp, pow_add]
    rw [hpowSplit] at hupperScaled
    have hterminalLt :
        canonicalBlockTerminalCarrier n k < 2 ^ (L - 1) * x := by
      rw [hterminal]
      have hprodpos : 0 < 3 ^ L * u :=
        Nat.mul_pos (pow_pos (by norm_num) _) hu
      have hsubeq : (3 ^ L * u - 1) + 1 = 3 ^ L * u := by omega
      nlinarith
    have hdivisor : 0 < 2 ^ v := pow_pos (by norm_num) _
    have hnextFormula : x' = canonicalBlockTerminalCarrier n k / 2 ^ v :=
      canonicalBlockNextStartState_eq_terminalCarrier_div_pow_valuation n k
    have hupper : x' < 2 ^ (L - v - 1) * x := by
      rw [hnextFormula]
      apply (Nat.div_lt_iff_lt_mul hdivisor).2
      have hexp : L - 1 = (L - v - 1) + v := by omega
      rw [hexp, pow_add] at hterminalLt
      nlinarith
    have hlowerPow := pow_bitWidth_sub_one_le hx'pos
    have hxlt := lt_pow_bitWidth hxpos
    have hlower : 2 ^ (L - v - 1) * x < x' := by
      have hD : 1 ≤ L - v := by omega
      calc
        2 ^ (L - v - 1) * x <
            2 ^ (L - v - 1) * 2 ^ bitWidth x :=
          (Nat.mul_lt_mul_left (pow_pos (by norm_num) _)).2 hxlt
        _ = 2 ^ (bitWidth x' - 1) := by
          rw [← pow_add]
          congr 1
          omega
        _ ≤ x' := hlowerPow
    omega

/-- Saturation is exactly positive drift with all canonical sources claiming. -/
theorem canonicalSaturatedBorderBlock_iff_pos_and_claimCount_eq_length
    (n : OddNat) (k : ℕ) :
    CanonicalSaturatedBorderBlock n k ↔
      0 < endpointAccountingTerm n k ∧
        canonicalBlockClaimCount n k = canonicalBlockLength n k := by
  constructor
  · intro h
    exact ⟨h.drift_pos, h.2.1⟩
  · rintro ⟨hpos, hclaims⟩
    exact canonicalSaturatedBorderBlock_of_pos_of_claimCount_eq_length hpos hclaims

/-! ## Positive selected depth -/

/-- Refined pressure depth; unlike the compatibility surface from cp-319 this
is always positive and never falls back to depth zero. -/
noncomputable def canonicalSelectedPositivePressureDepth
    (n : OddNat) (k : ℕ) : ℕ :=
  if canonicalBlockTerminalValuation n k = 1 then 1
  else canonicalBlockTerminalValuation n k - 1

/-- The refined selected pressure depth is positive. -/
theorem one_le_canonicalSelectedPositivePressureDepth
    (n : OddNat) (k : ℕ) :
    1 ≤ canonicalSelectedPositivePressureDepth n k := by
  unfold canonicalSelectedPositivePressureDepth
  split
  · omega
  · have hv := one_le_canonicalBlockTerminalValuation n k
    omega

/-- Positive nonsaturated drift is dominated at the selected positive depth. -/
theorem endpointAccountingTerm_le_selectedPositivePressure_of_not_saturated
    {n : OddNat} {k : ℕ}
    (hpos : 0 < endpointAccountingTerm n k)
    (hnot : ¬ CanonicalSaturatedBorderBlock n k) :
    endpointAccountingTerm n k ≤
      blockPressureContributionInt n k
        (canonicalSelectedPositivePressureDepth n k) := by
  let v := canonicalBlockTerminalValuation n k
  let L := canonicalBlockLength n k
  by_cases hv : v = 1
  · have hclaimLe := canonicalBlockClaimCount_le_length n k
    have hclaimNe : canonicalBlockClaimCount n k ≠ L := by
      intro heq
      exact hnot (canonicalSaturatedBorderBlock_of_pos_of_claimCount_eq_length
        hpos heq)
    have hclaimLt : canonicalBlockClaimCount n k < L := by omega
    have hvlt :=
      canonicalBlockTerminalValuation_lt_length_of_endpointAccountingTerm_pos hpos
    have hLthree : 3 ≤ L := by
      by_contra hL
      have hLtwo : L = 2 := by omega
      have hdrift := endpointAccountingTerm_eq_blockClaimCount_sub_capacityCount n k
      rw [canonicalBlockCapacityCount_eq_terminalValuation] at hdrift
      omega
    have hpressure :=
      blockPressureContributionInt_eq_sub_sub_one_of_add_two_le_length
        (n := n) (k := k) (d := 1) (by omega) (by
          change 3 ≤ L
          exact hLthree)
    have hdrift := endpointAccountingTerm_eq_blockClaimCount_sub_capacityCount n k
    rw [canonicalBlockCapacityCount_eq_terminalValuation] at hdrift
    rw [canonicalSelectedPositivePressureDepth, ite_eq_left hv]
    rw [hpressure]
    change endpointAccountingTerm n k ≤ ((L - 1 : ℕ) : ℤ) - 1
    omega
  · have hvpos := one_le_canonicalBlockTerminalValuation n k
    have hv2 : 2 ≤ v := by omega
    rw [canonicalSelectedPositivePressureDepth, ite_eq_right hv]
    exact endpointAccountingTerm_le_blockPressure_pred_terminal hpos hv2

/-- Saturation consumes exactly one unit beyond its selected depth-one pressure. -/
theorem CanonicalSaturatedBorderBlock.drift_eq_selectedPositivePressure_add_one
    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k) :
    endpointAccountingTerm n k =
      blockPressureContributionInt n k
        (canonicalSelectedPositivePressureDepth n k) + 1 := by
  have hp := h.pressure_eq_zero
  rw [h.terminalValuation_eq_one] at hp
  rw [h.2.2, canonicalSelectedPositivePressureDepth,
    ite_eq_left h.terminalValuation_eq_one, hp]
  norm_num

/-- Refined pointwise accounting using only positive pressure depths. -/
theorem endpointAccountingTerm_le_selectedPositivePressure_add_saturatedUnit
    {n : OddNat} {k : ℕ} (hpos : 0 < endpointAccountingTerm n k) :
    endpointAccountingTerm n k ≤
      blockPressureContributionInt n k
          (canonicalSelectedPositivePressureDepth n k) +
        canonicalSaturatedUnit n k := by
  classical
  by_cases hs : CanonicalSaturatedBorderBlock n k
  · rw [hs.drift_eq_selectedPositivePressure_add_one]
    simp [canonicalSaturatedUnit, hs]
  · have hle :=
      endpointAccountingTerm_le_selectedPositivePressure_of_not_saturated hpos hs
    simpa [canonicalSaturatedUnit, hs] using hle

/-! ## Pressure as an actual source carrier -/

/-- At a positive interior depth, pressure is exactly the cardinality of the
continuation fiber one level deeper. -/
theorem blockPressureContributionInt_eq_card_continuationFiber_succ
    {n : OddNat} {k d : ℕ} (hd : 1 ≤ d)
    (hdL : d < canonicalPaymentBlockLength n k) :
    blockPressureContributionInt n k d =
      ((canonicalPaymentBlockContinuationFiber n k (d + 1)).card : ℤ) := by
  rw [blockPressureContributionInt_eq,
    canonicalPaymentBlockContinuationFiber_card]
  simp [hd, hdL.le]
  omega

/-- Source incidences carrying the selected positive pressure contribution. -/
noncomputable def canonicalSelectedPressureCarrier
    (n : OddNat) (k : ℕ) : Finset ℕ :=
  canonicalPaymentBlockContinuationFiber n k
    (canonicalSelectedPositivePressureDepth n k + 1)

/-- A positive nonsaturated selected depth lies strictly inside its block. -/
theorem selectedPositivePressureDepth_lt_length_of_pos_of_not_saturated
    {n : OddNat} {k : ℕ}
    (hpos : 0 < endpointAccountingTerm n k)
    (hnot : ¬ CanonicalSaturatedBorderBlock n k) :
    canonicalSelectedPositivePressureDepth n k <
      canonicalPaymentBlockLength n k := by
  let v := canonicalBlockTerminalValuation n k
  let L := canonicalBlockLength n k
  have hLen : canonicalPaymentBlockLength n k = L := rfl
  have hvlt :=
    canonicalBlockTerminalValuation_lt_length_of_endpointAccountingTerm_pos hpos
  by_cases hv : v = 1
  · rw [canonicalSelectedPositivePressureDepth, ite_eq_left hv]
    by_contra hL
    rw [hLen] at hL
    have hLtwo : L = 2 := by omega
    have hclaimLe := canonicalBlockClaimCount_le_length n k
    have hdrift := endpointAccountingTerm_eq_blockClaimCount_sub_capacityCount n k
    rw [canonicalBlockCapacityCount_eq_terminalValuation] at hdrift
    have hclaims : canonicalBlockClaimCount n k = L := by omega
    exact hnot (canonicalSaturatedBorderBlock_of_pos_of_claimCount_eq_length
      hpos hclaims)
  · rw [canonicalSelectedPositivePressureDepth, ite_eq_right hv]
    rw [hLen]
    omega

/-- For positive nonsaturated blocks, selected pressure is the exact cardinality
of the selected continuation carrier. -/
theorem selectedPressure_eq_card_carrier_of_pos_of_not_saturated
    {n : OddNat} {k : ℕ}
    (hpos : 0 < endpointAccountingTerm n k)
    (hnot : ¬ CanonicalSaturatedBorderBlock n k) :
    blockPressureContributionInt n k
        (canonicalSelectedPositivePressureDepth n k) =
      ((canonicalSelectedPressureCarrier n k).card : ℤ) := by
  apply blockPressureContributionInt_eq_card_continuationFiber_succ
  · exact one_le_canonicalSelectedPositivePressureDepth n k
  · exact selectedPositivePressureDepth_lt_length_of_pos_of_not_saturated hpos hnot

/-- Positive nonsaturated drift injects numerically into its selected carrier. -/
theorem endpointAccountingTerm_le_card_selectedPressureCarrier
    {n : OddNat} {k : ℕ}
    (hpos : 0 < endpointAccountingTerm n k)
    (hnot : ¬ CanonicalSaturatedBorderBlock n k) :
    endpointAccountingTerm n k ≤
      ((canonicalSelectedPressureCarrier n k).card : ℤ) := by
  rw [← selectedPressure_eq_card_carrier_of_pos_of_not_saturated hpos hnot]
  exact endpointAccountingTerm_le_selectedPositivePressure_of_not_saturated hpos hnot

/-- Saturation has no selected continuation incidence; its entire residual is
the explicit unit token. -/
theorem CanonicalSaturatedBorderBlock.selectedPressureCarrier_eq_empty
    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k) :
    canonicalSelectedPressureCarrier n k = ∅ := by
  apply Finset.card_eq_zero.mp
  unfold canonicalSelectedPressureCarrier
  rw [canonicalPaymentBlockContinuationFiber_card,
    canonicalSelectedPositivePressureDepth, ite_eq_left h.terminalValuation_eq_one]
  change canonicalBlockLength n k - 2 = 0
  rw [h.length_eq_two]

theorem CanonicalSaturatedBorderBlock.saturatedUnit_eq_one
    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k) :
    canonicalSaturatedUnit n k = 1 := by
  classical
  simp [canonicalSaturatedUnit, h]

/-! ## Disjoint global selected carrier -/

/-- Distinct canonical blocks contain disjoint orbit-time incidences. -/
theorem canonicalPaymentBlock_disjoint_of_ne
    {n : OddNat} {k l : ℕ} (hkl : k ≠ l) :
    Disjoint (canonicalPaymentBlock n k) (canonicalPaymentBlock n l) := by
  rw [Finset.disjoint_left]
  intro i hik hil
  rcases existsUnique_mem_canonicalPaymentBlock n i with ⟨j, _hij, huniq⟩
  exact hkl ((huniq k hik).trans (huniq l hil).symm)

/-- Every selected pressure incidence remains inside its own canonical block. -/
theorem canonicalSelectedPressureCarrier_subset_block
    (n : OddNat) (k : ℕ) :
    canonicalSelectedPressureCarrier n k ⊆ canonicalPaymentBlock n k := by
  intro i hi
  exact (mem_canonicalPaymentBlockContinuationFiber_iff.mp hi).1

/-- Selected pressure carriers from distinct canonical blocks are disjoint. -/
theorem canonicalSelectedPressureCarrier_disjoint_of_ne
    {n : OddNat} {k l : ℕ} (hkl : k ≠ l) :
    Disjoint (canonicalSelectedPressureCarrier n k)
      (canonicalSelectedPressureCarrier n l) := by
  rw [Finset.disjoint_left]
  intro i hik hil
  have hblocks := canonicalPaymentBlock_disjoint_of_ne (n := n) hkl
  rw [Finset.disjoint_left] at hblocks
  exact hblocks (canonicalSelectedPressureCarrier_subset_block n k hik)
    (canonicalSelectedPressureCarrier_subset_block n l hil)

/-- Positive nonsaturated block indices in the closed interval `q..m`. -/
noncomputable def canonicalNonsaturatedPositiveBlockIndices
    (n : OddNat) (q m : ℕ) : Finset ℕ := by
  classical
  exact (canonicalPositiveDriftBlockIndices n q m).filter fun k =>
    ¬ CanonicalSaturatedBorderBlock n k

@[simp] theorem mem_canonicalNonsaturatedPositiveBlockIndices
    {n : OddNat} {q m k : ℕ} :
    k ∈ canonicalNonsaturatedPositiveBlockIndices n q m ↔
      k ∈ Finset.Icc q m ∧ 0 < endpointAccountingTerm n k ∧
        ¬ CanonicalSaturatedBorderBlock n k := by
  rw [canonicalNonsaturatedPositiveBlockIndices]
  simp only [Finset.mem_filter, canonicalPositiveDriftBlockIndices,
    Finset.mem_Icc]
  tauto

/-- The finite global selected-pressure incidence carrier.  The block index is
retained in the sigma coordinate, so this is an incidence certificate rather
than an allocation of future payment slots. -/
def CanonicalGlobalSelectedPressureCarrier
    (n : OddNat) (q m : ℕ) :=
  Σ k : {k : ℕ // k ∈ canonicalPositiveDriftBlockIndices n q m},
    {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k.val}

/-- Exact cardinality of the finite global selected-pressure carrier. -/
theorem natCard_CanonicalGlobalSelectedPressureCarrier
    (n : OddNat) (q m : ℕ) :
    Nat.card (CanonicalGlobalSelectedPressureCarrier n q m) =
      ∑ k ∈ canonicalPositiveDriftBlockIndices n q m,
        (canonicalSelectedPressureCarrier n k).card := by
  unfold CanonicalGlobalSelectedPressureCarrier
  rw [Nat.card_sigma]
  simp_rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  rw [Finset.univ_eq_attach]
  exact Finset.sum_attach (canonicalPositiveDriftBlockIndices n q m)
    fun k => (canonicalSelectedPressureCarrier n k).card

/-! ## Finite positive-drift incidence embedding -/

/-- Anonymous units of positive signed drift, indexed by their canonical
block.  They carry no claim about which future event pays them. -/
def CanonicalPositiveDriftUnitCarrier
    (n : OddNat) (q m : ℕ) :=
  Σ k : {k : ℕ // k ∈ canonicalPositiveDriftBlockIndices n q m},
    Fin (Int.toNat (endpointAccountingTerm n k.val))

/-- Exact cardinality of the finite positive-drift unit carrier. -/
theorem natCard_CanonicalPositiveDriftUnitCarrier
    (n : OddNat) (q m : ℕ) :
    Nat.card (CanonicalPositiveDriftUnitCarrier n q m) =
      ∑ k ∈ canonicalPositiveDriftBlockIndices n q m,
        Int.toNat (endpointAccountingTerm n k) := by
  unfold CanonicalPositiveDriftUnitCarrier
  rw [Nat.card_sigma]
  simp_rw [Nat.card_eq_fintype_card, Fintype.card_fin]
  rw [Finset.univ_eq_attach]
  exact Finset.sum_attach (canonicalPositiveDriftBlockIndices n q m)
    fun k => Int.toNat (endpointAccountingTerm n k)

/-- The natural-number token carried by a saturated block. -/
noncomputable def canonicalSaturatedTokenNat
    (n : OddNat) (k : ℕ) : ℕ :=
  Int.toNat (canonicalSaturatedUnit n k)

/-- Pointwise cardinality budget for one positive block. -/
theorem intToNat_endpointAccountingTerm_le_selectedCarrier_add_saturated
    {n : OddNat} {k : ℕ} (hpos : 0 < endpointAccountingTerm n k) :
    Int.toNat (endpointAccountingTerm n k) ≤
      (canonicalSelectedPressureCarrier n k).card +
        canonicalSaturatedTokenNat n k := by
  classical
  by_cases hs : CanonicalSaturatedBorderBlock n k
  · rw [canonicalSaturatedTokenNat, hs.saturatedUnit_eq_one,
      hs.netDrift_eq_one]
    norm_num
  · rw [canonicalSaturatedTokenNat]
    simp only [canonicalSaturatedUnit, hs, ↓reduceIte, Int.toNat_zero, add_zero]
    have hle := endpointAccountingTerm_le_card_selectedPressureCarrier hpos hs
    have hnat := Int.toNat_le_toNat hle
    simpa using hnat

/-- The sum of local cardinality budgets is exactly the global incidence
carrier plus the isolated saturated-token carrier. -/
theorem sum_selectedCarrier_add_saturated_eq_global
    (n : OddNat) (q m : ℕ) :
    (∑ k ∈ canonicalPositiveDriftBlockIndices n q m,
        ((canonicalSelectedPressureCarrier n k).card +
          canonicalSaturatedTokenNat n k)) =
      Nat.card (CanonicalGlobalSelectedPressureCarrier n q m) +
        (canonicalSaturatedBlockIndices n q m).card := by
  classical
  rw [Finset.sum_add_distrib,
    natCard_CanonicalGlobalSelectedPressureCarrier]
  congr 1
  simp only [canonicalSaturatedTokenNat, canonicalSaturatedUnit]
  have htoken (k : ℕ) :
      (if CanonicalSaturatedBorderBlock n k then (1 : ℤ) else 0).toNat =
        if CanonicalSaturatedBorderBlock n k then 1 else 0 := by
    by_cases hs : CanonicalSaturatedBorderBlock n k <;> simp [hs]
  simp_rw [htoken]
  rw [Finset.sum_boole]
  have hsets :
      (canonicalPositiveDriftBlockIndices n q m).filter
          (CanonicalSaturatedBorderBlock n) =
        canonicalSaturatedBlockIndices n q m := by
    ext k
    simp only [canonicalPositiveDriftBlockIndices,
      canonicalSaturatedBlockIndices, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hk, _⟩, hs⟩
      exact ⟨hk, hs⟩
    · rintro ⟨hk, hs⟩
      exact ⟨⟨hk, hs.drift_pos⟩, hs⟩
  rw [hsets]
  exact_mod_cast rfl

/-- Finite cardinality form of the positive-drift incidence certificate. -/
theorem natCard_positiveDriftUnitCarrier_le_global_add_saturated
    (n : OddNat) (q m : ℕ) :
    Nat.card (CanonicalPositiveDriftUnitCarrier n q m) ≤
      Nat.card (CanonicalGlobalSelectedPressureCarrier n q m) +
        Nat.card {k : ℕ // k ∈ canonicalSaturatedBlockIndices n q m} := by
  have hsatCard :
      Nat.card {k : ℕ // k ∈ canonicalSaturatedBlockIndices n q m} =
        (canonicalSaturatedBlockIndices n q m).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  rw [natCard_CanonicalPositiveDriftUnitCarrier, hsatCard,
    ← sum_selectedCarrier_add_saturated_eq_global]
  exact Finset.sum_le_sum fun k hk =>
    intToNat_endpointAccountingTerm_le_selectedCarrier_add_saturated
      ((Finset.mem_filter.mp hk).2)

/-- Existence of a finite injection from positive-drift units into disjoint
selected incidences plus saturated tokens.  This is only an incidence
certificate; it is intentionally not presented as a future payment map. -/
theorem exists_positiveDriftUnitEmbedding_global_add_saturated
    (n : OddNat) (q m : ℕ) :
    Nonempty (CanonicalPositiveDriftUnitCarrier n q m ↪
      (CanonicalGlobalSelectedPressureCarrier n q m ⊕
        {k : ℕ // k ∈ canonicalSaturatedBlockIndices n q m})) := by
  classical
  let : Fintype {k : ℕ // k ∈ canonicalPositiveDriftBlockIndices n q m} :=
    Fintype.ofFinset (canonicalPositiveDriftBlockIndices n q m) (by simp)
  let : Fintype (CanonicalPositiveDriftUnitCarrier n q m) := by
    unfold CanonicalPositiveDriftUnitCarrier
    infer_instance
  let : Fintype {k : ℕ // k ∈ canonicalSaturatedBlockIndices n q m} :=
    Fintype.ofFinset (canonicalSaturatedBlockIndices n q m) (by simp)
  let (k : {k : ℕ // k ∈ canonicalPositiveDriftBlockIndices n q m}) :
      Fintype {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k.val} :=
    Fintype.ofFinset (canonicalSelectedPressureCarrier n k.val) (by simp)
  let : Fintype (CanonicalGlobalSelectedPressureCarrier n q m) := by
    unfold CanonicalGlobalSelectedPressureCarrier
    infer_instance
  apply Function.Embedding.nonempty_iff_card_le.mpr
  simpa only [← Nat.card_eq_fintype_card, Nat.card_sum] using
    natCard_positiveDriftUnitCarrier_le_global_add_saturated n q m

/-! ## Open-excursion carrier bounds -/

/-- Positive drift, reflected into naturals, is bounded by the finite incidence
certificate and isolated saturation tokens on any closed block interval. -/
theorem sum_intToNat_positiveDrift_le_globalCarrier_add_saturatedCard
    (n : OddNat) (q m : ℕ) :
    (∑ k ∈ canonicalPositiveDriftBlockIndices n q m,
        Int.toNat (endpointAccountingTerm n k)) ≤
      Nat.card (CanonicalGlobalSelectedPressureCarrier n q m) +
        (canonicalSaturatedBlockIndices n q m).card := by
  rw [← natCard_CanonicalPositiveDriftUnitCarrier]
  have h := natCard_positiveDriftUnitCarrier_le_global_add_saturated n q m
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using h

/-- Isolated saturated tokens occupy at most half of the enlarged interval. -/
theorem card_canonicalSaturatedBlockIndices_le_half
    (n : OddNat) (q m : ℕ) :
    (canonicalSaturatedBlockIndices n q m).card ≤ (m - q + 2) / 2 := by
  apply (Nat.le_div_iff_mul_le Nat.two_pos).2
  simpa [Nat.mul_comm] using
    two_mul_card_canonicalSaturatedBlockIndices_le n q m

/-- Carrier bound with the isolated-token term replaced by its packing bound.
It is finite-window accounting, not a uniform bound in `m`. -/
theorem sum_intToNat_positiveDrift_le_globalCarrier_add_half
    (n : OddNat) (q m : ℕ) :
    (∑ k ∈ canonicalPositiveDriftBlockIndices n q m,
        Int.toNat (endpointAccountingTerm n k)) ≤
      Nat.card (CanonicalGlobalSelectedPressureCarrier n q m) +
        (m - q + 2) / 2 := by
  exact (sum_intToNat_positiveDrift_le_globalCarrier_add_saturatedCard n q m).trans
    (Nat.add_le_add_left (card_canonicalSaturatedBlockIndices_le_half n q m) _)

/-- Open-excursion-facing form of the finite carrier bound.  The excursion
hypothesis identifies the intended window; the inequality itself holds on every
closed canonical block interval. -/
theorem CanonicalOpenPositiveQueueExcursion.positiveDrift_le_globalCarrier_add_half
    {n : OddNat} {q m : ℕ} (_h : CanonicalOpenPositiveQueueExcursion n q m) :
    (∑ k ∈ canonicalPositiveDriftBlockIndices n q m,
        Int.toNat (endpointAccountingTerm n k)) ≤
      Nat.card (CanonicalGlobalSelectedPressureCarrier n q m) +
        (m - q + 2) / 2 :=
  sum_intToNat_positiveDrift_le_globalCarrier_add_half n q m

/-! ## Selected-depth buckets -/

/-- Positive blocks whose refined selected pressure depth is exactly `d`. -/
noncomputable def canonicalSelectedPressureBlocksAtDepth
    (n : OddNat) (q m d : ℕ) : Finset ℕ := by
  classical
  exact (canonicalPositiveDriftBlockIndices n q m).filter fun k =>
    canonicalSelectedPositivePressureDepth n k = d

/-- The finite support of selected pressure depths in `q..m`. -/
noncomputable def canonicalSelectedPressureDepthSupport
    (n : OddNat) (q m : ℕ) : Finset ℕ :=
  (canonicalPositiveDriftBlockIndices n q m).image fun k =>
    canonicalSelectedPositivePressureDepth n k

@[simp] theorem mem_canonicalSelectedPressureBlocksAtDepth
    {n : OddNat} {q m d k : ℕ} :
    k ∈ canonicalSelectedPressureBlocksAtDepth n q m d ↔
      k ∈ canonicalPositiveDriftBlockIndices n q m ∧
        canonicalSelectedPositivePressureDepth n k = d := by
  simp [canonicalSelectedPressureBlocksAtDepth]

/-- Selected incidences at one fixed selected depth. -/
def CanonicalSelectedPressureBucketCarrier
    (n : OddNat) (q m d : ℕ) :=
  Σ k : {k : ℕ // k ∈ canonicalSelectedPressureBlocksAtDepth n q m d},
    {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k.val}

/-- Exact cardinality of one selected-depth bucket. -/
theorem natCard_CanonicalSelectedPressureBucketCarrier
    (n : OddNat) (q m d : ℕ) :
    Nat.card (CanonicalSelectedPressureBucketCarrier n q m d) =
      ∑ k ∈ canonicalSelectedPressureBlocksAtDepth n q m d,
        (canonicalSelectedPressureCarrier n k).card := by
  unfold CanonicalSelectedPressureBucketCarrier
  rw [Nat.card_sigma]
  simp_rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  rw [Finset.univ_eq_attach]
  exact Finset.sum_attach (canonicalSelectedPressureBlocksAtDepth n q m d)
    fun k => (canonicalSelectedPressureCarrier n k).card

/-- Finite Fubini decomposition of the global selected carrier by its dynamic
selected depth. -/
theorem natCard_globalSelectedPressureCarrier_eq_sum_depthBuckets
    (n : OddNat) (q m : ℕ) :
    Nat.card (CanonicalGlobalSelectedPressureCarrier n q m) =
      ∑ d ∈ canonicalSelectedPressureDepthSupport n q m,
        Nat.card (CanonicalSelectedPressureBucketCarrier n q m d) := by
  rw [natCard_CanonicalGlobalSelectedPressureCarrier]
  simp_rw [natCard_CanonicalSelectedPressureBucketCarrier]
  symm
  apply Finset.sum_fiberwise_of_maps_to
  intro k hk
  exact Finset.mem_image.mpr ⟨k, hk, rfl⟩

/-- A selected incidence in depth bucket `d` is an incidence of the existing
fixed-depth continuation fiber at depth `d + 1`. -/
theorem CanonicalSelectedPressureBucketCarrier.mem_fixedDepthContinuationFiber
    {n : OddNat} {q m d : ℕ}
    (x : CanonicalSelectedPressureBucketCarrier n q m d) :
    x.2.val ∈ canonicalPaymentBlockContinuationFiber n x.1.val (d + 1) := by
  rcases x with ⟨k, i⟩
  have hkdepth := (mem_canonicalSelectedPressureBlocksAtDepth.mp k.property).2
  change i.val ∈ canonicalPaymentBlockContinuationFiber n k.val (d + 1)
  unfold canonicalSelectedPressureCarrier at i
  simpa [hkdepth] using i.property

/-!
## Pressure infrastructure audit and the genuine remaining obstruction

The dynamic-to-fixed-depth conversion is now exact: the global incidence
carrier is a finite sum of bucket carriers, and every bucket incidence belongs
to the already existing canonical continuation fiber at `d + 1`.  Therefore
`orbitDepthContinuationFiberCount_paymentEndpointSeq_eq_sum` can count each
fixed bucket after extending the block interval to an endpoint prefix.

The existing `PressureFrontier`, `PressureAccounting`, `PressureBeam`, and
finite-window packing APIs constrain fixed-depth continuation/recovery counts
and separated pulse witnesses.  They do not currently provide a
contribution-preserving injection from every continuation incidence into a
finite boundary resource, nor a theorem saying that an unbounded bucket must
produce a separator or a `NoLift` obstruction.  Crossing that gap would be a
new global transport theorem, not a consequence of source disjointness.

Saturated tokens remain separate for the same reason.  A nonpositive successor
does not repay a token when its drift is zero.  The next sound branch must
identify an injective charge to a later negative unit, a selected incidence, or
an upper-zero boundary unit, with exact preservation of bit position.  No such
charge is asserted here.
-/

end DkMath.Collatz
