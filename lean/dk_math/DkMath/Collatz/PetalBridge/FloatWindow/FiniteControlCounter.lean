/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Collatz.PetalBridge.FloatWindow.FinitePotentialIncompleteness

#print "file: DkMath.Collatz.PetalBridge.FloatWindow.FiniteControlCounter"

namespace DkMath.Collatz

/-!
# Finite control with an unbounded counter

A finite control projection need not store the full arithmetic resource.  This
certificate keeps a separate signed counter, requires its exact recurrence,
and requires a local guard that proves each realized transition preserves
counter nonnegativity.  The soundness proof then derives all prefix
inequalities by induction.

This module intentionally does not instantiate the certificate with the
canonical source-age deficit.  Such an instance is valid only after its local
guard has been proved independently from canonical block arithmetic; using
the desired prefix invariant itself as that guard would be circular.
-/

/-- Core signed-counter certificate.  No finite control state is needed for
the recurrence or invariant induction. -/
structure SignedCounterCertificate where
  weight : ℕ → ℤ
  credit : ℕ → ℤ
  initial_credit_nonneg : 0 ≤ credit 0
  credit_succ : ∀ m, credit (m + 1) = credit m - weight m
  preserves_nonneg : ∀ m, 0 ≤ credit m → weight m ≤ credit m

namespace SignedCounterCertificate

/-- Exact recurrence and the local guard preserve credit nonnegativity. -/
theorem credit_nonneg (C : SignedCounterCertificate) (M : ℕ) :
    0 ≤ C.credit M := by
  induction M with
  | zero => exact C.initial_credit_nonneg
  | succ M ih =>
      rw [C.credit_succ]
      exact sub_nonneg.mpr (C.preserves_nonneg M ih)

/-- The unrestricted counter recurrence telescopes exactly. -/
theorem sum_weight_range_eq_credit_zero_sub
    (C : SignedCounterCertificate) (M : ℕ) :
    (∑ m ∈ Finset.range M, C.weight m) = C.credit 0 - C.credit M := by
  induction M with
  | zero => simp
  | succ M ih =>
      rw [Finset.sum_range_succ, ih, C.credit_succ]
      ring

/-- General soundness with arbitrary nonnegative initial credit. -/
theorem sum_weight_range_le_initial_credit
    (C : SignedCounterCertificate) (M : ℕ) :
    (∑ m ∈ Finset.range M, C.weight m) ≤ C.credit 0 := by
  rw [C.sum_weight_range_eq_credit_zero_sub]
  exact sub_le_self _ (C.credit_nonneg M)

/-- Zero initial credit recovers nonpositive prefixes. -/
theorem sum_weight_range_nonpos_of_initial_credit_eq_zero
    (C : SignedCounterCertificate) (hzero : C.credit 0 = 0) (M : ℕ) :
    (∑ m ∈ Finset.range M, C.weight m) ≤ 0 := by
  simpa [hzero] using C.sum_weight_range_le_initial_credit M

end SignedCounterCertificate

/-- A finite control sequence accompanied by an unrestricted integer counter.
The finite signature is observational; soundness is delegated to the core
signed-counter certificate. -/
structure FiniteControlSignedCounterCertificate
    (Signature : Type*) [Finite Signature] where
  signature : ℕ → Signature
  weight : ℕ → ℤ
  credit : ℕ → ℤ
  initial_credit_eq_zero : credit 0 = 0
  credit_succ : ∀ m, credit (m + 1) = credit m - weight m
  preserves_nonneg : ∀ m, 0 ≤ credit m → weight m ≤ credit m

namespace FiniteControlSignedCounterCertificate

variable {Signature : Type*} [Finite Signature]

/-- Forget the finite diagnostic control and retain the arithmetic counter
certificate used by the soundness proof. -/
def toSignedCounterCertificate
    (C : FiniteControlSignedCounterCertificate Signature) :
    SignedCounterCertificate where
  weight := C.weight
  credit := C.credit
  initial_credit_nonneg := by rw [C.initial_credit_eq_zero]
  credit_succ := C.credit_succ
  preserves_nonneg := C.preserves_nonneg

/-- Exact counter recurrence and the local guard preserve nonnegative credit
at every realized transition. -/
theorem credit_nonneg
    (C : FiniteControlSignedCounterCertificate Signature) (M : ℕ) :
    0 ≤ C.credit M :=
  C.toSignedCounterCertificate.credit_nonneg M

/-- Counter recurrence telescopes exactly: accumulated weight is initial
credit minus final credit. -/
theorem sum_weight_range_eq_credit_zero_sub
    (C : FiniteControlSignedCounterCertificate Signature) (M : ℕ) :
    (∑ m ∈ Finset.range M, C.weight m) = C.credit 0 - C.credit M :=
  C.toSignedCounterCertificate.sum_weight_range_eq_credit_zero_sub M

/-- Finite-control wrapper of the general initial-credit bound. -/
theorem sum_weight_range_le_initial_credit
    (C : FiniteControlSignedCounterCertificate Signature) (M : ℕ) :
    (∑ m ∈ Finset.range M, C.weight m) ≤ C.credit 0 :=
  C.toSignedCounterCertificate.sum_weight_range_le_initial_credit M

/-- Soundness: every prefix weight is nonpositive. -/
theorem sum_weight_range_nonpos
    (C : FiniteControlSignedCounterCertificate Signature) (M : ℕ) :
    (∑ m ∈ Finset.range M, C.weight m) ≤ 0 := by
  exact C.toSignedCounterCertificate.sum_weight_range_nonpos_of_initial_credit_eq_zero
    C.initial_credit_eq_zero M

end FiniteControlSignedCounterCertificate

/-! ## Concrete realization on the incompleteness witness -/

/-- Unbounded credit needed by the alternating sequence: zero after complete
pairs and `k+1` after the negative term of pair `k`. -/
def alternatingUnboundedCredit (M : ℕ) : ℤ :=
  if M % 2 = 0 then 0 else ((M / 2 + 1 : ℕ) : ℤ)

@[simp] theorem alternatingUnboundedCredit_even (k : ℕ) :
    alternatingUnboundedCredit (2 * k) = 0 := by
  simp [alternatingUnboundedCredit]

@[simp] theorem alternatingUnboundedCredit_odd (k : ℕ) :
    alternatingUnboundedCredit (2 * k + 1) = ((k + 1 : ℕ) : ℤ) := by
  have hmod : (2 * k + 1) % 2 = 1 := by omega
  have hdiv : (2 * k + 1) / 2 = k := by omega
  simp [alternatingUnboundedCredit, hmod, hdiv]

/-- Exact credit recurrence for the alternating witness. -/
theorem alternatingUnboundedCredit_succ (M : ℕ) :
    alternatingUnboundedCredit (M + 1) =
      alternatingUnboundedCredit M - alternatingUnboundedWeight M := by
  rcases Nat.even_or_odd M with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · have hpair : alternatingUnboundedCredit (2 * k + 1) =
        alternatingUnboundedCredit (2 * k) -
          alternatingUnboundedWeight (2 * k) := by simp
    simpa [two_mul] using hpair
  · have hpair : alternatingUnboundedCredit (2 * k + 1 + 1) =
        alternatingUnboundedCredit (2 * k + 1) -
          alternatingUnboundedWeight (2 * k + 1) := by
      rw [show 2 * k + 1 + 1 = 2 * (k + 1) by omega]
      simp
    simpa [two_mul] using hpair

/-- The explicit transition guard is checked locally from the parity branch,
not inferred from a prefix theorem. -/
theorem alternatingUnboundedWeight_le_credit
    (M : ℕ) (hcredit : 0 ≤ alternatingUnboundedCredit M) :
    alternatingUnboundedWeight M ≤ alternatingUnboundedCredit M := by
  rcases Nat.even_or_odd M with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · have hpair : alternatingUnboundedWeight (2 * k) ≤
        alternatingUnboundedCredit (2 * k) := by simp
    simpa [two_mul] using hpair
  · have hpair : alternatingUnboundedWeight (2 * k + 1) ≤
        alternatingUnboundedCredit (2 * k + 1) := by simp
    simpa [two_mul] using hpair

/-- A one-state finite control with an unbounded arithmetic credit certifies
the alternating sequence. -/
def alternatingUnboundedCounterCertificate :
    FiniteControlSignedCounterCertificate Unit where
  signature := fun _ => ()
  weight := alternatingUnboundedWeight
  credit := alternatingUnboundedCredit
  initial_credit_eq_zero := by simp [alternatingUnboundedCredit]
  credit_succ := alternatingUnboundedCredit_succ
  preserves_nonneg := alternatingUnboundedWeight_le_credit

/-- Counter-certificate proof of the nonpositive-prefix property.  Together
with the finite-table impossibility theorem, this is an explicit separation
between finite potential and finite control with unbounded credit. -/
theorem alternatingUnboundedCounterCertificate_sound (M : ℕ) :
    (∑ m ∈ Finset.range M, alternatingUnboundedWeight m) ≤ 0 :=
  alternatingUnboundedCounterCertificate.sum_weight_range_nonpos M

end DkMath.Collatz
