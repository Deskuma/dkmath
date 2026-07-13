/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentBlockNormalForm

#print "file: DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentPrimitiveExcursion"

namespace DkMath.Collatz

/-!
# Primitive positive excursions of the canonical scalar queue

This module packages a *finite, repaid* positive excursion.  It does not assume
or assert that every positive queue position has a future zero.  That future
repayment statement is the global obstruction left after the finite accounting
and block-normal-form layers.
-/

/-- Queue value immediately before canonical block `q` is processed. -/
noncomputable def canonicalOutstandingClaimQueueBefore
    (n : OddNat) : ℕ → ℕ
  | 0 => 0
  | q + 1 => canonicalOutstandingClaimQueue n q

/--
A primitive positive excursion starts from an empty queue, stays positive after
every proper block, and is first empty again after block `r`.
-/
def CanonicalPrimitivePositiveQueueExcursion
    (n : OddNat) (q r : ℕ) : Prop :=
  q < r ∧
    canonicalOutstandingClaimQueueBefore n q = 0 ∧
      (∀ m ∈ Finset.Ico q r, 0 < canonicalOutstandingClaimQueue n m) ∧
        canonicalOutstandingClaimQueue n r = 0

/-- Signed partial-sum presentation of a primitive positive excursion. -/
def CanonicalPrimitivePositiveDriftExcursion
    (n : OddNat) (q r : ℕ) : Prop :=
  q < r ∧
    canonicalOutstandingClaimQueueBefore n q = 0 ∧
      (∀ m ∈ Finset.Ico q r, 0 < canonicalWindowDriftInt n q m) ∧
        canonicalWindowDriftInt n q r ≤ 0

/-- Number of canonical blocks in the closed excursion interval `q..r`. -/
def canonicalPrimitiveQueueExcursionLength (q r : ℕ) : ℕ :=
  r - q + 1

/-- Maximum queue height attained on the closed excursion interval. -/
noncomputable def canonicalPrimitiveQueueExcursionMaximum
    (n : OddNat) (q r : ℕ) : ℕ :=
  (Finset.Icc q r).sup (canonicalOutstandingClaimQueue n)

/-- Exact signed block word carried by the closed excursion interval. -/
noncomputable def canonicalPrimitiveQueueExcursionSignature
    (n : OddNat) (q r : ℕ) : List ℤ :=
  List.ofFn fun i : Fin (canonicalPrimitiveQueueExcursionLength q r) =>
    endpointAccountingTerm n (q + i.1)

/-- Orbit time of the endpoint that performs the primitive excursion's first repayment. -/
noncomputable def canonicalPrimitiveQueueExcursionFirstRepaymentEndpoint
    (n : OddNat) (r : ℕ) : ℕ :=
  paymentEndpointSeq n r

/-- The queue-before coordinate unfolds to the preceding queue at positive indices. -/
theorem canonicalOutstandingClaimQueueBefore_succ (n : OddNat) (q : ℕ) :
    canonicalOutstandingClaimQueueBefore n (q + 1) =
      canonicalOutstandingClaimQueue n q := rfl

/-- Starting empty makes the first block queue the positive part of its own drift. -/
private theorem queue_eq_intToNat_windowDrift_self_of_before_eq_zero
    {n : OddNat} {q : ℕ}
    (hbefore : canonicalOutstandingClaimQueueBefore n q = 0) :
    canonicalOutstandingClaimQueue n q =
      Int.toNat (canonicalWindowDriftInt n q q) := by
  cases q with
  | zero =>
      rw [canonicalOutstandingClaimQueue_zero_eq_intToNat,
        canonicalWindowDriftInt_self]
  | succ q =>
      rw [canonicalOutstandingClaimQueueBefore_succ] at hbefore
      rw [canonicalOutstandingClaimQueue_succ_eq_intToNat, hbefore,
        canonicalWindowDriftInt_self]
      simp

/--
While every preceding partial queue is positive, reflection is inactive and
the queue equals the ordinary signed partial sum from the excursion start.
-/
private theorem queue_eq_intToNat_windowDrift_of_positive_prefix
    {n : OddNat} {q m : ℕ} (hqm : q ≤ m)
    (hbefore : canonicalOutstandingClaimQueueBefore n q = 0)
    (hpositive : ∀ t ∈ Finset.Ico q m,
      0 < canonicalOutstandingClaimQueue n t) :
    canonicalOutstandingClaimQueue n m =
      Int.toNat (canonicalWindowDriftInt n q m) := by
  induction m, hqm using Nat.le_induction with
  | base => exact queue_eq_intToNat_windowDrift_self_of_before_eq_zero hbefore
  | succ m hqm ih =>
      rw [canonicalOutstandingClaimQueue_succ_eq_intToNat]
      rw [canonicalWindowDriftInt_succ n (by omega), if_pos hqm]
      have hmPos : 0 < canonicalOutstandingClaimQueue n m :=
        hpositive m (Finset.mem_Ico.mpr ⟨hqm, by omega⟩)
      have hsumPos : 0 < canonicalWindowDriftInt n q m := by
        have hEq := ih (fun t ht => hpositive t (by
          exact Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp ht).1,
            (Finset.mem_Ico.mp ht).2.trans_le (by omega)⟩))
        have hnonneg : 0 ≤ canonicalWindowDriftInt n q m := by
          by_contra hneg
          have : Int.toNat (canonicalWindowDriftInt n q m) = 0 :=
            Int.toNat_of_nonpos (by omega)
          omega
        omega
      have hcast : (Int.toNat (canonicalWindowDriftInt n q m) : ℤ) =
          canonicalWindowDriftInt n q m := by
        rw [Int.ofNat_toNat, max_eq_left (le_of_lt hsumPos)]
      rw [ih (fun t ht => hpositive t (by
        exact Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp ht).1,
          (Finset.mem_Ico.mp ht).2.trans_le (by omega)⟩)), hcast]

/-- Positive signed proper prefixes likewise keep reflection inactive. -/
private theorem queue_eq_intToNat_windowDrift_of_positive_drift_prefix
    {n : OddNat} {q m : ℕ} (hqm : q ≤ m)
    (hbefore : canonicalOutstandingClaimQueueBefore n q = 0)
    (hpositive : ∀ t ∈ Finset.Ico q m,
      0 < canonicalWindowDriftInt n q t) :
    canonicalOutstandingClaimQueue n m =
      Int.toNat (canonicalWindowDriftInt n q m) := by
  induction m, hqm using Nat.le_induction with
  | base => exact queue_eq_intToNat_windowDrift_self_of_before_eq_zero hbefore
  | succ m hqm ih =>
      have hprefix : ∀ t ∈ Finset.Ico q m,
          0 < canonicalWindowDriftInt n q t := by
        intro t ht
        exact hpositive t (Finset.mem_Ico.mpr
          ⟨(Finset.mem_Ico.mp ht).1, (Finset.mem_Ico.mp ht).2.trans (by omega)⟩)
      have hmPos : 0 < canonicalWindowDriftInt n q m :=
        hpositive m (Finset.mem_Ico.mpr ⟨hqm, by omega⟩)
      have hcast : (Int.toNat (canonicalWindowDriftInt n q m) : ℤ) =
          canonicalWindowDriftInt n q m := by
        rw [Int.ofNat_toNat, max_eq_left (le_of_lt hmPos)]
      rw [canonicalOutstandingClaimQueue_succ_eq_intToNat,
        canonicalWindowDriftInt_succ n (by omega), if_pos hqm,
        ih hprefix, hcast]

/-- Queue and signed-partial-sum presentations of a repaid primitive excursion agree. -/
theorem canonicalPrimitivePositiveQueueExcursion_iff_driftExcursion
    (n : OddNat) (q r : ℕ) :
    CanonicalPrimitivePositiveQueueExcursion n q r ↔
      CanonicalPrimitivePositiveDriftExcursion n q r := by
  constructor
  · rintro ⟨hqr, hbefore, hpositive, hzero⟩
    refine ⟨hqr, hbefore, ?_, ?_⟩
    · intro m hm
      rcases Finset.mem_Ico.mp hm with ⟨hqm, hmr⟩
      have hEq := queue_eq_intToNat_windowDrift_of_positive_prefix
        (n := n) (q := q) (m := m) hqm hbefore (fun t ht =>
          hpositive t (Finset.mem_Ico.mpr
            ⟨(Finset.mem_Ico.mp ht).1, (Finset.mem_Ico.mp ht).2.trans hmr⟩))
      have hmPos := hpositive m (Finset.mem_Ico.mpr ⟨hqm, hmr⟩)
      have hself := Int.self_le_toNat (canonicalWindowDriftInt n q m)
      omega
    · have hEq := queue_eq_intToNat_windowDrift_of_positive_prefix
        (n := n) (q := q) (m := r) (by omega) hbefore hpositive
      rw [hzero] at hEq
      exact Int.toNat_eq_zero.mp hEq.symm
  · rintro ⟨hqr, hbefore, hpositive, htotal⟩
    refine ⟨hqr, hbefore, ?_, ?_⟩
    · intro m hm
      rcases Finset.mem_Ico.mp hm with ⟨hqm, hmr⟩
      have hEq := queue_eq_intToNat_windowDrift_of_positive_drift_prefix
        (n := n) (q := q) (m := m) hqm hbefore (fun t ht =>
          hpositive t (Finset.mem_Ico.mpr
            ⟨(Finset.mem_Ico.mp ht).1, (Finset.mem_Ico.mp ht).2.trans hmr⟩))
      rw [hEq]
      have hself := Int.self_le_toNat (canonicalWindowDriftInt n q m)
      have hsum := hpositive m (Finset.mem_Ico.mpr ⟨hqm, hmr⟩)
      omega
    · have hEq := queue_eq_intToNat_windowDrift_of_positive_drift_prefix
        (n := n) (q := q) (m := r) (Nat.le_of_lt hqr) hbefore hpositive
      rw [hEq, Int.toNat_of_nonpos htotal]

/-- The signature contains exactly one entry for each block in the closed interval. -/
theorem canonicalPrimitiveQueueExcursionSignature_length
    (n : OddNat) (q r : ℕ) :
    (canonicalPrimitiveQueueExcursionSignature n q r).length =
      canonicalPrimitiveQueueExcursionLength q r := by
  simp [canonicalPrimitiveQueueExcursionSignature]

/-- The maximum surface dominates every queue value in its excursion interval. -/
theorem canonicalOutstandingClaimQueue_le_primitiveExcursionMaximum
    (n : OddNat) {q r m : ℕ} (hm : m ∈ Finset.Icc q r) :
    canonicalOutstandingClaimQueue n m ≤
      canonicalPrimitiveQueueExcursionMaximum n q r := by
  unfold canonicalPrimitiveQueueExcursionMaximum
  exact Finset.le_sup (f := canonicalOutstandingClaimQueue n) hm

/-- A primitive excursion's stated endpoint is its first zero after its positive run. -/
theorem CanonicalPrimitivePositiveQueueExcursion.first_repayment
    {n : OddNat} {q r : ℕ}
    (h : CanonicalPrimitivePositiveQueueExcursion n q r) :
    canonicalOutstandingClaimQueue n r = 0 ∧
      ∀ m ∈ Finset.Ico q r, canonicalOutstandingClaimQueue n m ≠ 0 := by
  exact ⟨h.2.2.2, fun m hm => (h.2.2.1 m hm).ne'⟩

/-- A primitive excursion has a uniquely determined repayment block for its start. -/
theorem canonicalPrimitivePositiveQueueExcursion_right_unique
    {n : OddNat} {q r r' : ℕ}
    (h : CanonicalPrimitivePositiveQueueExcursion n q r)
    (h' : CanonicalPrimitivePositiveQueueExcursion n q r') :
    r = r' := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact (h'.2.2.1 r (Finset.mem_Ico.mpr ⟨Nat.le_of_lt h.1, hlt⟩)).ne'
      h.2.2.2
  · exact (h.2.2.1 r' (Finset.mem_Ico.mpr ⟨Nat.le_of_lt h'.1, hgt⟩)).ne'
      h'.2.2.2

/-!
## Exact remaining obstruction

For a fixed start `q`, the preceding theorem makes a finite repayment endpoint
unique.  Existence is different: proving that every positive queue position is
contained in such an interval requires a future block `r` with queue zero.
Neither the reflected-walk identities nor the exact transition

`(L, u) ↦ oddPart (3^L * u - 1)`

currently supplies that future zero.  Consequently no unconditional
"every positive position belongs to a unique maximal finite excursion" theorem
is exported here.  Adding it without a repayment hypothesis would merely hide
the remaining global problem in a definition.
-/

end DkMath.Collatz
