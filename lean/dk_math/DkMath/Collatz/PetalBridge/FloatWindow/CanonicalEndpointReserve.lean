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
credit is the zero-reserve endpoint function.  No weight hypothesis is needed:
every certificate requires all credit values to be nonnegative. -/
theorem not_exists_signedCounterCertificate_credit_eq_zeroReserve_of_initialDrift_pos
    {n : OddNat} (hpos : 0 < endpointAccountingTerm n 0) :
    ¬ ∃ C : SignedCounterCertificate,
      C.credit = canonicalEndpointCounterCredit n := by
  rintro ⟨C, hcredit⟩
  have hnonneg := C.credit_nonneg 1
  rw [hcredit] at hnonneg
  have hneg := canonicalEndpointCounterCredit_one_neg_of_initialDrift_pos hpos
  omega

/-- If a certificate did use zero-reserve credit, its exact recurrence would
force its weight to be canonical endpoint drift. -/
theorem SignedCounterCertificate.weight_eq_endpointAccountingTerm_of_credit_eq
    {n : OddNat} (C : SignedCounterCertificate)
    (hcredit : C.credit = canonicalEndpointCounterCredit n) :
    C.weight = endpointAccountingTerm n := by
  funext m
  have hrec := C.credit_succ m
  rw [hcredit] at hrec
  have hcanonical := canonicalEndpointCounterCredit_succ n m
  omega

/-- Compatibility form retaining the previously exposed weight equality. -/
theorem not_exists_signedCounterCertificate_zeroReserve_of_initialDrift_pos
    {n : OddNat} (hpos : 0 < endpointAccountingTerm n 0) :
    ¬ ∃ C : SignedCounterCertificate,
      C.weight = (fun m => endpointAccountingTerm n m) ∧
        C.credit = canonicalEndpointCounterCredit n := by
  rintro ⟨C, _, hcredit⟩
  exact
    not_exists_signedCounterCertificate_credit_eq_zeroReserve_of_initialDrift_pos
      hpos ⟨C, hcredit⟩

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

/-- A width reserve `B` gives the explicit reflected-queue ceiling
`root width + B`. -/
theorem CanonicalWidthWithinReserve.to_queueUniformUpperBound
    {n : OddNat} {B : ℕ} (hB : CanonicalWidthWithinReserve n B) :
    CanonicalOutstandingClaimQueueUniformUpperBound n (bitWidth n.1 + B) := by
  have hendpoint :
      CanonicalEndpointWidthUniformUpperBound n (bitWidth n.1 + B) := by
    intro m
    rw [canonicalEndpointWidth_eq_blockStartState_succ]
    exact hB (m + 1)
  exact hendpoint.to_outstandingClaimQueueUniformUpperBound

/-- A reflected-queue ceiling `C` gives a cumulative width reserve with the
same reserve parameter `C`. -/
theorem CanonicalOutstandingClaimQueueUniformUpperBound.to_widthWithinReserve
    {n : OddNat} {C : ℕ}
    (hC : CanonicalOutstandingClaimQueueUniformUpperBound n C) :
    CanonicalWidthWithinReserve n C := by
  intro M
  cases M with
  | zero => simp
  | succ m =>
      rw [← canonicalEndpointWidth_eq_blockStartState_succ]
      exact hC.to_endpointWidthUniformUpperBound m

/-- A fixed-root cumulative width reserve exists exactly when the existing
reflected scalar queue has some uniform ceiling.  This is an equivalence of
targets, not an independent proof that either target holds. -/
theorem rootwiseCanonicalWidthBound_iff_exists_queueUniformUpperBound
    (n : OddNat) :
    RootwiseCanonicalWidthBound n ↔
      ∃ C : ℕ, CanonicalOutstandingClaimQueueUniformUpperBound n C := by
  constructor
  · rintro ⟨B, hB⟩
    exact ⟨bitWidth n.1 + B, hB.to_queueUniformUpperBound⟩
  · rintro ⟨C, hC⟩
    exact ⟨C, hC.to_widthWithinReserve⟩

/-! ## Queue as maximum absorption deficit -/

/-- Every positive reflected queue is attained by one inclusive suffix, and
exact conservation identifies that suffix with a half-open absorption deficit.
-/
theorem exists_absorptionDeficitWindow_eq_outstandingClaimQueue_of_pos
    {n : OddNat} {m : ℕ} (hpos : 0 < canonicalOutstandingClaimQueue n m) :
    ∃ q, q ≤ m ∧
      (canonicalOutstandingClaimQueue n m : ℤ) =
        canonicalAbsorptionDeficitWindow n q (m - q + 1) := by
  rcases outstandingClaimQueue_eq_zero_or_exists_windowDrift n m with
    hzero | ⟨_, q, hqm, hq⟩
  · omega
  · refine ⟨q, hqm, ?_⟩
    have hnonneg : 0 ≤ canonicalWindowDriftInt n q m := by
      by_contra hneg
      have htoNat : Int.toNat (canonicalWindowDriftInt n q m) = 0 :=
        Int.toNat_of_nonpos (by omega)
      rw [htoNat] at hq
      omega
    calc
      (canonicalOutstandingClaimQueue n m : ℤ) =
          (Int.toNat (canonicalWindowDriftInt n q m) : ℕ) := by
            exact_mod_cast hq
      _ = canonicalWindowDriftInt n q m := by
        rw [Int.ofNat_toNat, max_eq_left hnonneg]
      _ = canonicalAbsorptionDeficitWindow n q (m - q + 1) :=
        (canonicalAbsorptionDeficitWindow_eq_canonicalWindowDriftInt
          n hqm).symm

/-! ## All-window cumulative absorption target -/

/-- Every finite half-open canonical block window has absorption deficit at
most `C`. -/
def CanonicalAbsorptionDeficitWindowUniformUpperBound
    (n : OddNat) (C : ℕ) : Prop :=
  ∀ q M, canonicalAbsorptionDeficitWindow n q M ≤ C

/-- A rootwise width reserve `B` bounds every shifted absorption deficit by
`root width + B`. -/
theorem CanonicalWidthWithinReserve.to_absorptionDeficitWindowUniformUpperBound
    {n : OddNat} {B : ℕ} (hB : CanonicalWidthWithinReserve n B) :
    CanonicalAbsorptionDeficitWindowUniformUpperBound n (bitWidth n.1 + B) := by
  intro q M
  rw [canonicalAbsorptionDeficitWindow_eq_startState_bitWidth_sub]
  have hend := hB (q + M)
  omega

/-- An all-window deficit ceiling `C`, specialized to prefixes, gives a width
reserve with parameter `C`. -/
theorem CanonicalAbsorptionDeficitWindowUniformUpperBound.to_widthWithinReserve
    {n : OddNat} {C : ℕ}
    (hC : CanonicalAbsorptionDeficitWindowUniformUpperBound n C) :
    CanonicalWidthWithinReserve n C := by
  intro M
  have hprefix := hC 0 M
  rw [canonicalAbsorptionDeficitWindow_eq_startState_bitWidth_sub] at hprefix
  rw [zero_add, canonicalBlockStartState_zero_eq_root] at hprefix
  omega

/-- Fixed-root cumulative width boundedness is existentially equivalent to a
uniform upper bound on every finite absorption-deficit window. -/
theorem rootwiseCanonicalWidthBound_iff_exists_absorptionDeficitWindowUniformUpperBound
    (n : OddNat) :
    RootwiseCanonicalWidthBound n ↔
      ∃ C : ℕ, CanonicalAbsorptionDeficitWindowUniformUpperBound n C := by
  constructor
  · rintro ⟨B, hB⟩
    exact ⟨bitWidth n.1 + B,
      hB.to_absorptionDeficitWindowUniformUpperBound⟩
  · rintro ⟨C, hC⟩
    exact ⟨C, hC.to_widthWithinReserve⟩

/-- A window deficit ceiling is exactly the cumulative absorption estimate
needed to cover block length on that window. -/
theorem canonicalAbsorptionDeficitWindow_le_iff_length_le_absorption_add
    (n : OddNat) (q M C : ℕ) :
    canonicalAbsorptionDeficitWindow n q M ≤ C ↔
      canonicalBlockLengthWindowSum n q M ≤
        canonicalClaimHolesWindowSum n q M +
          canonicalTerminalValuationWindowSum n q M + C := by
  rw [canonicalAbsorptionDeficitWindow]
  constructor <;> intro h <;> omega

/-- Public cumulative target in block-budget form.  Unlike the one-block
pointwise target, this controls every finite shifted window. -/
theorem canonicalAbsorptionDeficitWindowUniformUpperBound_iff_length_le_absorption_add
    (n : OddNat) (C : ℕ) :
    CanonicalAbsorptionDeficitWindowUniformUpperBound n C ↔
      ∀ q M,
        canonicalBlockLengthWindowSum n q M ≤
          canonicalClaimHolesWindowSum n q M +
            canonicalTerminalValuationWindowSum n q M + C := by
  constructor <;> intro h q M
  · exact (canonicalAbsorptionDeficitWindow_le_iff_length_le_absorption_add
      n q M C).mp (h q M)
  · exact (canonicalAbsorptionDeficitWindow_le_iff_length_le_absorption_add
      n q M C).mpr (h q M)

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
