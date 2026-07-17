/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalEndpointConservation
import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalAllOnesDrift
import DkMath.Collatz.PetalBridge.FloatWindow.FiniteControlCounter
import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentScalarQueue

#print "file: DkMath.Collatz.PetalBridge.FloatWindow.CanonicalEndpointReserve"

namespace DkMath.Collatz

/-!
# Canonical endpoint reserves

Zero-reserve endpoint credit is an exact diagnostic, but positive initial
drift makes it negative after one block.  A valid signed-counter certificate
therefore needs an explicit root-dependent reserve together with an
independently supplied cumulative width bound.

This module keeps three statements separate:

* no finite reserve works uniformly across every root;
* a fixed root may or may not admit a cumulative width reserve;
* a fixed root may or may not have bounded pointwise endpoint drift.

Only the first statement is refuted here.  The second conditionally supplies a
counter certificate and implies the third.
-/

/-! ## Zero-reserve obstruction -/

/-- Odd all-ones roots make zero-reserve credit at most the negative of the
family parameter. -/
theorem canonicalEndpointCounterCredit_allOnesOdd_odd_one_le_neg
    (r : ℕ) :
    canonicalEndpointCounterCredit
        (allOnesOdd (2 * r + 1) (by omega)) 1 ≤ -(r : ℤ) := by
  rw [canonicalEndpointCounterCredit_one]
  have hdrift := le_endpointAccountingTerm_allOnesOdd_odd_zero r
  omega

/-- Choosing the positive parameter `r + 1` makes zero-reserve credit strictly
negative after the first all-ones block. -/
theorem canonicalEndpointCounterCredit_allOnesOdd_odd_succ_one_neg
    (r : ℕ) :
    canonicalEndpointCounterCredit
        (allOnesOdd (2 * (r + 1) + 1) (by omega)) 1 < 0 := by
  apply canonicalEndpointCounterCredit_one_neg_of_initialDrift_pos
  have hdrift := le_endpointAccountingTerm_allOnesOdd_odd_zero (r + 1)
  omega

/-- Positive initial drift excludes every core counter certificate whose
weight and credit are definitionally the zero-reserve endpoint functions. -/
theorem not_exists_signedCounterCertificate_zeroReserve_of_initialDrift_pos
    {n : OddNat} (hpos : 0 < endpointAccountingTerm n 0) :
    ¬ ∃ C : SignedCounterCertificate,
      C.weight = (fun m => endpointAccountingTerm n m) ∧
        C.credit = canonicalEndpointCounterCredit n := by
  rintro ⟨C, _, hcredit⟩
  have hnonneg := C.credit_nonneg 1
  rw [hcredit] at hnonneg
  have hneg := canonicalEndpointCounterCredit_one_neg_of_initialDrift_pos hpos
  omega

/-- The positive all-ones subfamily gives an explicit symbolic obstruction to
the zero-reserve certificate. -/
theorem not_exists_signedCounterCertificate_zeroReserve_allOnesOdd
    (r : ℕ) :
    ¬ ∃ C : SignedCounterCertificate,
      C.weight = (fun m => endpointAccountingTerm
        (allOnesOdd (2 * (r + 1) + 1) (by omega)) m) ∧
      C.credit = canonicalEndpointCounterCredit
        (allOnesOdd (2 * (r + 1) + 1) (by omega)) := by
  apply not_exists_signedCounterCertificate_zeroReserve_of_initialDrift_pos
  have hdrift := le_endpointAccountingTerm_allOnesOdd_odd_zero (r + 1)
  omega

/-! ## Conditional reserved certificate -/

/-- An independently supplied cumulative width reserve instantiates the core
signed-counter API.  This definition does not prove that such a reserve exists
for any particular root. -/
noncomputable def canonicalEndpointReservedCounterCertificate
    (n : OddNat) (B : ℕ) (hB : CanonicalWidthWithinReserve n B) :
    SignedCounterCertificate where
  weight := endpointAccountingTerm n
  credit := canonicalEndpointReservedCredit n B
  initial_credit_nonneg := by simp
  credit_succ := canonicalEndpointReservedCredit_succ n B
  preserves_nonneg := by
    intro m _
    have hnext : 0 ≤ canonicalEndpointReservedCredit n B (m + 1) :=
      (canonicalEndpointReservedCredit_nonneg_iff n B (m + 1)).mpr (hB (m + 1))
    rw [canonicalEndpointReservedCredit_succ] at hnext
    omega

/-- Conditional counter soundness: a supplied width reserve bounds every
prefix sum of endpoint drift by the initial reserve. -/
theorem sum_endpointAccountingTerm_le_reserve
    {n : OddNat} {B : ℕ} (hB : CanonicalWidthWithinReserve n B) (M : ℕ) :
    (∑ m ∈ Finset.range M, endpointAccountingTerm n m) ≤ B := by
  have h :=
    (canonicalEndpointReservedCounterCertificate n B hB).sum_weight_range_le_initial_credit M
  change (∑ m ∈ Finset.range M, endpointAccountingTerm n m) ≤
    canonicalEndpointReservedCredit n B 0 at h
  simpa using h

/-! ## Reflected-queue audit

The existing scalar queue is the maximum positive suffix drift.  Its uniform
boundedness is therefore not an independent absorption theorem: it is another
exact presentation of the cumulative width question.  The bridges below make
that equivalence explicit and prevent a queue bound from being cited as though
it had already supplied the missing arithmetic estimate.
-/

/-- Completed endpoint width of block `m` is the width at the next canonical
block start. -/
theorem canonicalEndpointWidth_eq_blockStartState_succ
    (n : OddNat) (m : ℕ) :
    canonicalEndpointWidth n m =
      bitWidth (canonicalBlockStartState n (m + 1)) := by
  rw [canonicalBlockStartState_succ_eq_nextStartState]
  rfl

/-- A fixed-root cumulative width reserve exists exactly when the existing
reflected scalar queue has some uniform ceiling.  This is an equivalence of
targets, not an independent proof that either target holds. -/
theorem rootwiseCanonicalWidthBound_iff_exists_queueUniformUpperBound
    (n : OddNat) :
    RootwiseCanonicalWidthBound n ↔
      ∃ C : ℕ, CanonicalOutstandingClaimQueueUniformUpperBound n C := by
  constructor
  · rintro ⟨B, hB⟩
    have hendpoint :
        CanonicalEndpointWidthUniformUpperBound n (bitWidth n.1 + B) := by
      intro m
      rw [canonicalEndpointWidth_eq_blockStartState_succ]
      exact hB (m + 1)
    exact ⟨bitWidth n.1 + B,
      hendpoint.to_outstandingClaimQueueUniformUpperBound⟩
  · rintro ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro M
    cases M with
    | zero => simp
    | succ m =>
        rw [← canonicalEndpointWidth_eq_blockStartState_succ]
        exact hC.to_endpointWidthUniformUpperBound m

/-! ## Global reserve obstruction -/

/-- One natural reserve bounds every canonical width of every odd root. -/
def GlobalCanonicalWidthReserveBound : Prop :=
  ∃ B : ℕ, ∀ n : OddNat, CanonicalWidthWithinReserve n B

/-- The odd all-ones initial-drift family excludes a finite reserve shared by
all roots.  This does not address existence of a reserve for one fixed root. -/
theorem not_globalCanonicalWidthReserveBound :
    ¬ GlobalCanonicalWidthReserveBound := by
  rintro ⟨B, hB⟩
  obtain ⟨n, hdrift⟩ := exists_endpointAccountingTerm_gt (B : ℤ)
  have hwidth := hB n 1
  have hstart : canonicalBlockStartState n 1 =
      canonicalBlockNextStartState n 0 := by
    simpa using canonicalBlockStartState_succ_eq_nextStartState n 0
  rw [hstart] at hwidth
  have hledger := endpointAccountingTerm_eq_canonicalBlock_bitWidth_sub n 0
  rw [canonicalBlockStartState_zero_eq_root] at hledger
  omega

end DkMath.Collatz
