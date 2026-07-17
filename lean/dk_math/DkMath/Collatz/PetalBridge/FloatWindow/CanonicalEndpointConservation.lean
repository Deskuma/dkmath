/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalEndpointDrift

#print "file: DkMath.Collatz.PetalBridge.FloatWindow.CanonicalEndpointConservation"

namespace DkMath.Collatz

/-!
# Cumulative canonical endpoint conservation

The block identity

`drift + claim holes + terminal valuation = block length`

is summed here over half-open block windows `[q, q + M)`.  The half-open
convention makes the empty and singleton windows definitional and aligns the
drift sum with the width difference between block starts `q` and `q + M`.
-/

/-! ## Window ledgers -/

/-- Total signed endpoint drift over blocks `[q, q + M)`. -/
noncomputable def canonicalEndpointDriftWindowSum
    (n : OddNat) (q M : ℕ) : ℤ :=
  ∑ i ∈ Finset.range M, endpointAccountingTerm n (q + i)

/-- Total claim-hole absorption over blocks `[q, q + M)`. -/
noncomputable def canonicalClaimHolesWindowSum
    (n : OddNat) (q M : ℕ) : ℤ :=
  ∑ i ∈ Finset.range M, ((canonicalBlockClaimHoles n (q + i)).card : ℤ)

/-- Total terminal-valuation absorption over blocks `[q, q + M)`. -/
noncomputable def canonicalTerminalValuationWindowSum
    (n : OddNat) (q M : ℕ) : ℤ :=
  ∑ i ∈ Finset.range M, (canonicalBlockTerminalValuation n (q + i) : ℤ)

/-- Total block-length budget over blocks `[q, q + M)`. -/
noncomputable def canonicalBlockLengthWindowSum
    (n : OddNat) (q M : ℕ) : ℤ :=
  ∑ i ∈ Finset.range M, (canonicalBlockLength n (q + i) : ℤ)

@[simp] theorem canonicalEndpointDriftWindowSum_zero
    (n : OddNat) (q : ℕ) :
    canonicalEndpointDriftWindowSum n q 0 = 0 := by
  simp [canonicalEndpointDriftWindowSum]

@[simp] theorem canonicalClaimHolesWindowSum_zero
    (n : OddNat) (q : ℕ) :
    canonicalClaimHolesWindowSum n q 0 = 0 := by
  simp [canonicalClaimHolesWindowSum]

@[simp] theorem canonicalTerminalValuationWindowSum_zero
    (n : OddNat) (q : ℕ) :
    canonicalTerminalValuationWindowSum n q 0 = 0 := by
  simp [canonicalTerminalValuationWindowSum]

@[simp] theorem canonicalBlockLengthWindowSum_zero
    (n : OddNat) (q : ℕ) :
    canonicalBlockLengthWindowSum n q 0 = 0 := by
  simp [canonicalBlockLengthWindowSum]

@[simp] theorem canonicalEndpointDriftWindowSum_one
    (n : OddNat) (q : ℕ) :
    canonicalEndpointDriftWindowSum n q 1 = endpointAccountingTerm n q := by
  simp [canonicalEndpointDriftWindowSum]

@[simp] theorem canonicalClaimHolesWindowSum_one
    (n : OddNat) (q : ℕ) :
    canonicalClaimHolesWindowSum n q 1 =
      ((canonicalBlockClaimHoles n q).card : ℤ) := by
  simp [canonicalClaimHolesWindowSum]

@[simp] theorem canonicalTerminalValuationWindowSum_one
    (n : OddNat) (q : ℕ) :
    canonicalTerminalValuationWindowSum n q 1 =
      (canonicalBlockTerminalValuation n q : ℤ) := by
  simp [canonicalTerminalValuationWindowSum]

@[simp] theorem canonicalBlockLengthWindowSum_one
    (n : OddNat) (q : ℕ) :
    canonicalBlockLengthWindowSum n q 1 =
      (canonicalBlockLength n q : ℤ) := by
  simp [canonicalBlockLengthWindowSum]

/-! ## Exact window conservation -/

/-- Every finite block window conserves its complete length budget. -/
theorem canonicalEndpointBudgetWindow_conservation
    (n : OddNat) (q M : ℕ) :
    canonicalEndpointDriftWindowSum n q M +
          canonicalClaimHolesWindowSum n q M +
        canonicalTerminalValuationWindowSum n q M =
      canonicalBlockLengthWindowSum n q M := by
  unfold canonicalEndpointDriftWindowSum canonicalClaimHolesWindowSum
    canonicalTerminalValuationWindowSum canonicalBlockLengthWindowSum
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  exact
    endpointAccountingTerm_add_claimHoles_add_terminalValuation_eq_blockLength
      n (q + i)

/-- The empty window is the zero instance of the conservation law. -/
theorem canonicalEndpointBudgetWindow_conservation_empty
    (n : OddNat) (q : ℕ) :
    canonicalEndpointDriftWindowSum n q 0 +
          canonicalClaimHolesWindowSum n q 0 +
        canonicalTerminalValuationWindowSum n q 0 =
      canonicalBlockLengthWindowSum n q 0 := by
  simp

/-- The singleton window recovers the primary block conservation law. -/
theorem canonicalEndpointBudgetWindow_conservation_singleton
    (n : OddNat) (q : ℕ) :
    canonicalEndpointDriftWindowSum n q 1 +
          canonicalClaimHolesWindowSum n q 1 +
        canonicalTerminalValuationWindowSum n q 1 =
      canonicalBlockLengthWindowSum n q 1 := by
  simpa using
    endpointAccountingTerm_add_claimHoles_add_terminalValuation_eq_blockLength
      n q

/-- Shifted endpoint telescope: drift on `[q, q + M)` is exactly the width
change between the two canonical block starts. -/
theorem canonicalEndpointDriftWindowSum_eq_startState_bitWidth_sub
    (n : OddNat) (q M : ℕ) :
    canonicalEndpointDriftWindowSum n q M =
      (bitWidth (canonicalBlockStartState n (q + M)) : ℤ) -
        bitWidth (canonicalBlockStartState n q) := by
  unfold canonicalEndpointDriftWindowSum
  induction M with
  | zero => simp
  | succ M ih =>
      rw [Finset.sum_range_succ, ih,
        endpointAccountingTerm_eq_canonicalBlock_bitWidth_sub]
      rw [show q + (M + 1) = (q + M) + 1 by omega,
        canonicalBlockStartState_succ_eq_nextStartState]
      ring

/-- Prefix telescope ending at the start of block `M`. -/
theorem canonicalEndpointDriftPrefixSum_eq_startState_bitWidth_sub
    (n : OddNat) (M : ℕ) :
    canonicalEndpointDriftWindowSum n 0 M =
      (bitWidth (canonicalBlockStartState n M) : ℤ) - bitWidth n.1 := by
  simpa using
    canonicalEndpointDriftWindowSum_eq_startState_bitWidth_sub n 0 M

/-- Width growth plus the two cumulative absorption channels equals the
cumulative block-length budget on every shifted window. -/
theorem canonicalEndpointWidthBudgetWindow_conservation
    (n : OddNat) (q M : ℕ) :
    ((bitWidth (canonicalBlockStartState n (q + M)) : ℤ) -
          bitWidth (canonicalBlockStartState n q)) +
          canonicalClaimHolesWindowSum n q M +
        canonicalTerminalValuationWindowSum n q M =
      canonicalBlockLengthWindowSum n q M := by
  rw [← canonicalEndpointDriftWindowSum_eq_startState_bitWidth_sub]
  exact canonicalEndpointBudgetWindow_conservation n q M

/-- Prefix form of cumulative endpoint conservation. -/
theorem canonicalEndpointWidthBudgetPrefix_conservation
    (n : OddNat) (M : ℕ) :
    ((bitWidth (canonicalBlockStartState n M) : ℤ) - bitWidth n.1) +
          canonicalClaimHolesWindowSum n 0 M +
        canonicalTerminalValuationWindowSum n 0 M =
      canonicalBlockLengthWindowSum n 0 M := by
  simpa using canonicalEndpointWidthBudgetWindow_conservation n 0 M

/-! ## Exact high-drift thresholds -/

/-- A natural drift threshold is met exactly when block length covers that
threshold together with both absorption channels. -/
theorem natCast_le_endpointAccountingTerm_iff
    (n : OddNat) (m K : ℕ) :
    (K : ℤ) ≤ endpointAccountingTerm n m ↔
      (K : ℤ) + ((canonicalBlockClaimHoles n m).card : ℤ) +
          (canonicalBlockTerminalValuation n m : ℤ) ≤
        (canonicalBlockLength n m : ℤ) := by
  have hbudget :=
    endpointAccountingTerm_add_claimHoles_add_terminalValuation_eq_blockLength
      n m
  constructor <;> intro h <;> omega

/-- High realized drift requires a block at least as long as the threshold. -/
theorem blockLength_ge_of_endpointAccountingTerm_ge
    {n : OddNat} {m K : ℕ}
    (h : (K : ℤ) ≤ endpointAccountingTerm n m) :
    K ≤ canonicalBlockLength n m := by
  have hthreshold := (natCast_le_endpointAccountingTerm_iff n m K).mp h
  omega

/-- High realized drift leaves at most `length - K` for the combined exact
absorption.  The conclusion remains in `Int` to avoid truncated subtraction. -/
theorem combinedAbsorption_le_length_sub_of_endpointAccountingTerm_ge
    {n : OddNat} {m K : ℕ}
    (h : (K : ℤ) ≤ endpointAccountingTerm n m) :
    ((canonicalBlockClaimHoles n m).card : ℤ) +
        (canonicalBlockTerminalValuation n m : ℤ) ≤
      (canonicalBlockLength n m : ℤ) - K := by
  have hthreshold := (natCast_le_endpointAccountingTerm_iff n m K).mp h
  omega

/-- If one fixed root has arbitrarily high endpoint drift, its canonical
block lengths are necessarily unbounded.  No converse is asserted. -/
theorem blockLength_unbounded_of_endpointAccountingTerm_unbounded
    {n : OddNat}
    (h : ∀ K : ℕ, ∃ m, (K : ℤ) ≤ endpointAccountingTerm n m) :
    ∀ K : ℕ, ∃ m, K ≤ canonicalBlockLength n m := by
  intro K
  obtain ⟨m, hm⟩ := h K
  exact ⟨m, blockLength_ge_of_endpointAccountingTerm_ge hm⟩

/-! ## Rootwise structural restatement -/

/-- Rootwise drift boundedness is exactly a uniform additive absorption
estimate.  This theorem only reforms the fixed-root question; it does not
provide the bound. -/
theorem rootwiseEndpointDriftBound_iff_length_le_absorption_add
    (n : OddNat) :
    RootwiseEndpointDriftBound n ↔
      ∃ B : ℤ, ∀ m,
        (canonicalBlockLength n m : ℤ) ≤
          ((canonicalBlockClaimHoles n m).card : ℤ) +
            (canonicalBlockTerminalValuation n m : ℤ) + B := by
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨B, ?_⟩
    intro m
    have hbudget :=
      endpointAccountingTerm_add_claimHoles_add_terminalValuation_eq_blockLength
        n m
    have hdrift := hB m
    omega
  · rintro ⟨B, hB⟩
    refine ⟨B, ?_⟩
    intro m
    have hbudget :=
      endpointAccountingTerm_add_claimHoles_add_terminalValuation_eq_blockLength
        n m
    have habsorb := hB m
    omega

/-! ## Cumulative width boundedness

This is deliberately stronger than pointwise endpoint-drift boundedness.  It
controls every canonical width relative to the initial root width, rather than
only controlling each one-step increment.  No converse implication is claimed.
-/

/-- A specified reserve bounds every canonical block-start width above the
initial root width. -/
def CanonicalWidthWithinReserve (n : OddNat) (B : ℕ) : Prop :=
  ∀ M, bitWidth (canonicalBlockStartState n M) ≤ bitWidth n.1 + B

/-- One fixed root admits some finite cumulative width reserve. -/
def RootwiseCanonicalWidthBound (n : OddNat) : Prop :=
  ∃ B : ℕ, CanonicalWidthWithinReserve n B

/-- A cumulative width reserve gives a pointwise endpoint-drift ceiling.  The
reverse implication is not available: bounded increments need not bound their
cumulative level. -/
theorem RootwiseCanonicalWidthBound.to_endpointDriftBound
    {n : OddNat} (h : RootwiseCanonicalWidthBound n) :
    RootwiseEndpointDriftBound n := by
  rcases h with ⟨B, hB⟩
  refine ⟨(bitWidth n.1 + B : ℕ), ?_⟩
  intro m
  rw [endpointAccountingTerm_eq_canonicalBlock_bitWidth_sub]
  have hnext := hB (m + 1)
  rw [canonicalBlockStartState_succ_eq_nextStartState] at hnext
  omega

/-! ## Scaled cumulative absorption -/

/-- Scaling preserves the exact window budget over `Int`.  This is algebraic
transport of the conservation identity, not a spiral-growth coefficient
estimate. -/
theorem canonicalEndpointWidthBudgetWindow_conservation_mul
    (n : OddNat) (q M : ℕ) (A : ℤ) :
    A * ((bitWidth (canonicalBlockStartState n (q + M)) : ℤ) -
          bitWidth (canonicalBlockStartState n q)) +
          A * canonicalClaimHolesWindowSum n q M +
        A * canonicalTerminalValuationWindowSum n q M =
      A * canonicalBlockLengthWindowSum n q M := by
  have h := canonicalEndpointWidthBudgetWindow_conservation n q M
  calc
    A * ((bitWidth (canonicalBlockStartState n (q + M)) : ℤ) -
          bitWidth (canonicalBlockStartState n q)) +
          A * canonicalClaimHolesWindowSum n q M +
        A * canonicalTerminalValuationWindowSum n q M =
        A * (((bitWidth (canonicalBlockStartState n (q + M)) : ℤ) -
            bitWidth (canonicalBlockStartState n q)) +
          canonicalClaimHolesWindowSum n q M +
          canonicalTerminalValuationWindowSum n q M) := by ring
    _ = A * canonicalBlockLengthWindowSum n q M := congrArg (fun z => A * z) h

/-- If scaled absorption covers scaled length up to allowance `C`, then the
same allowance bounds scaled width growth.  No logarithmic interpretation is
needed. -/
theorem mul_widthGrowth_le_of_mul_length_le_absorption_add
    {n : OddNat} {q M : ℕ} {A C : ℤ}
    (habsorb :
      A * canonicalBlockLengthWindowSum n q M ≤
        A * canonicalClaimHolesWindowSum n q M +
          A * canonicalTerminalValuationWindowSum n q M + C) :
    A * ((bitWidth (canonicalBlockStartState n (q + M)) : ℤ) -
      bitWidth (canonicalBlockStartState n q)) ≤ C := by
  have hbudget :=
    canonicalEndpointWidthBudgetWindow_conservation_mul n q M A
  linarith

/-- Unscaled caller-facing absorption bound for cumulative width growth. -/
theorem widthGrowth_le_of_length_le_absorption_add
    {n : OddNat} {q M : ℕ} {C : ℤ}
    (habsorb :
      canonicalBlockLengthWindowSum n q M ≤
        canonicalClaimHolesWindowSum n q M +
          canonicalTerminalValuationWindowSum n q M + C) :
    (bitWidth (canonicalBlockStartState n (q + M)) : ℤ) -
        bitWidth (canonicalBlockStartState n q) ≤ C := by
  have hscaled :
      (1 : ℤ) * canonicalBlockLengthWindowSum n q M ≤
        1 * canonicalClaimHolesWindowSum n q M +
          1 * canonicalTerminalValuationWindowSum n q M + C := by
    simpa using habsorb
  simpa using (mul_widthGrowth_le_of_mul_length_le_absorption_add hscaled)

/-- Complete absorption of cumulative length forces nonpositive width growth
over the selected finite window. -/
theorem widthGrowth_nonpos_of_length_le_absorption
    {n : OddNat} {q M : ℕ}
    (habsorb :
      canonicalBlockLengthWindowSum n q M ≤
        canonicalClaimHolesWindowSum n q M +
          canonicalTerminalValuationWindowSum n q M) :
    (bitWidth (canonicalBlockStartState n (q + M)) : ℤ) -
        bitWidth (canonicalBlockStartState n q) ≤ 0 := by
  apply widthGrowth_le_of_length_le_absorption_add (C := 0)
  simpa using habsorb

/-! ## Zero-reserve diagnostic counter

The following expression has the exact counter recurrence, but it is not a
general certificate candidate.  Positive initial endpoint drift makes its
credit negative immediately.  It remains useful as the exact negative of
cumulative width growth.
-/

/-- Cumulative absorbed budget minus cumulative block length. -/
noncomputable def canonicalEndpointCounterCredit (n : OddNat) (M : ℕ) : ℤ :=
  canonicalClaimHolesWindowSum n 0 M +
    canonicalTerminalValuationWindowSum n 0 M -
      canonicalBlockLengthWindowSum n 0 M

@[simp] theorem canonicalEndpointCounterCredit_zero (n : OddNat) :
    canonicalEndpointCounterCredit n 0 = 0 := by
  simp [canonicalEndpointCounterCredit]

/-- The candidate credit is exactly the negative cumulative width growth. -/
theorem canonicalEndpointCounterCredit_eq_rootWidth_sub_startWidth
    (n : OddNat) (M : ℕ) :
    canonicalEndpointCounterCredit n M =
      (bitWidth n.1 : ℤ) - bitWidth (canonicalBlockStartState n M) := by
  have hbudget := canonicalEndpointWidthBudgetPrefix_conservation n M
  unfold canonicalEndpointCounterCredit
  linarith

/-- Candidate credit is nonnegative exactly when the current canonical width
does not exceed the initial root width.  This is diagnostic, not an
independent proof of the condition. -/
theorem canonicalEndpointCounterCredit_nonneg_iff
    (n : OddNat) (M : ℕ) :
    0 ≤ canonicalEndpointCounterCredit n M ↔
      bitWidth (canonicalBlockStartState n M) ≤ bitWidth n.1 := by
  rw [canonicalEndpointCounterCredit_eq_rootWidth_sub_startWidth]
  omega

/-- Exact one-block recurrence of the canonical counter candidate. -/
theorem canonicalEndpointCounterCredit_succ
    (n : OddNat) (M : ℕ) :
    canonicalEndpointCounterCredit n (M + 1) =
      canonicalEndpointCounterCredit n M - endpointAccountingTerm n M := by
  rw [canonicalEndpointCounterCredit_eq_rootWidth_sub_startWidth,
    canonicalEndpointCounterCredit_eq_rootWidth_sub_startWidth,
    endpointAccountingTerm_eq_canonicalBlock_bitWidth_sub]
  rw [canonicalBlockStartState_succ_eq_nextStartState]
  ring

/-- After one block, zero-reserve credit is exactly negative initial drift. -/
theorem canonicalEndpointCounterCredit_one
    (n : OddNat) :
    canonicalEndpointCounterCredit n 1 = -endpointAccountingTerm n 0 := by
  rw [show 1 = 0 + 1 by omega, canonicalEndpointCounterCredit_succ]
  simp

/-- Positive initial drift refutes nonnegativity of zero-reserve credit at the
first transition. -/
theorem canonicalEndpointCounterCredit_one_neg_of_initialDrift_pos
    {n : OddNat} (hpos : 0 < endpointAccountingTerm n 0) :
    canonicalEndpointCounterCredit n 1 < 0 := by
  rw [canonicalEndpointCounterCredit_one]
  omega

/-- The desired local guard is equivalent to nonnegativity of the next
candidate credit.  This identifies the remaining arithmetic obligation but
does not discharge it. -/
theorem endpointAccountingTerm_le_counterCredit_iff_next_nonneg
    (n : OddNat) (M : ℕ) :
    endpointAccountingTerm n M ≤ canonicalEndpointCounterCredit n M ↔
      0 ≤ canonicalEndpointCounterCredit n (M + 1) := by
  rw [canonicalEndpointCounterCredit_succ]
  omega

/-! ## Reserved endpoint credit -/

/-- Root-dependent reserve plus negative cumulative canonical width growth. -/
noncomputable def canonicalEndpointReservedCredit
    (n : OddNat) (B M : ℕ) : ℤ :=
  (B : ℤ) + bitWidth n.1 - bitWidth (canonicalBlockStartState n M)

/-- Reserved credit starts at the supplied reserve. -/
@[simp] theorem canonicalEndpointReservedCredit_zero
    (n : OddNat) (B : ℕ) :
    canonicalEndpointReservedCredit n B 0 = B := by
  simp [canonicalEndpointReservedCredit]

/-- Reserved credit has the same exact endpoint-drift recurrence as the
zero-reserve diagnostic. -/
theorem canonicalEndpointReservedCredit_succ
    (n : OddNat) (B M : ℕ) :
    canonicalEndpointReservedCredit n B (M + 1) =
      canonicalEndpointReservedCredit n B M - endpointAccountingTerm n M := by
  rw [canonicalEndpointReservedCredit, canonicalEndpointReservedCredit,
    endpointAccountingTerm_eq_canonicalBlock_bitWidth_sub,
    canonicalBlockStartState_succ_eq_nextStartState]
  ring

/-- Reserved credit is nonnegative exactly while the current canonical width
stays inside the supplied reserve. -/
theorem canonicalEndpointReservedCredit_nonneg_iff
    (n : OddNat) (B M : ℕ) :
    0 ≤ canonicalEndpointReservedCredit n B M ↔
      bitWidth (canonicalBlockStartState n M) ≤ bitWidth n.1 + B := by
  rw [canonicalEndpointReservedCredit]
  omega

/-- All-time nonnegativity of reserved credit is exactly the corresponding
cumulative width bound. -/
theorem canonicalEndpointReservedCredit_all_nonneg_iff
    (n : OddNat) (B : ℕ) :
    (∀ M, 0 ≤ canonicalEndpointReservedCredit n B M) ↔
      CanonicalWidthWithinReserve n B := by
  constructor <;> intro h M
  · exact (canonicalEndpointReservedCredit_nonneg_iff n B M).mp (h M)
  · exact (canonicalEndpointReservedCredit_nonneg_iff n B M).mpr (h M)

/-- Existence of a finite cumulative width reserve is equivalent to existence
of a reserve whose endpoint credit stays nonnegative for all canonical time. -/
theorem rootwiseCanonicalWidthBound_iff_exists_reservedCredit_nonneg
    (n : OddNat) :
    RootwiseCanonicalWidthBound n ↔
      ∃ B : ℕ, ∀ M, 0 ≤ canonicalEndpointReservedCredit n B M := by
  constructor
  · rintro ⟨B, hB⟩
    exact ⟨B, (canonicalEndpointReservedCredit_all_nonneg_iff n B).mpr hB⟩
  · rintro ⟨B, hB⟩
    exact ⟨B, (canonicalEndpointReservedCredit_all_nonneg_iff n B).mp hB⟩

end DkMath.Collatz
