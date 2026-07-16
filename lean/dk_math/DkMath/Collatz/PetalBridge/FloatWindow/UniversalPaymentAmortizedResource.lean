/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Collatz.PetalBridge.FloatWindow.FiniteAmortizedResource
import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentAmplitude

#print "file: DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentAmortizedResource"

namespace DkMath.Collatz

/-!
# Canonical queue audit and the owned-resource frontier

The generic telescope is in `FiniteAmortizedResource`.  This module audits its
connection to the canonical reflected queue.  The audit proves that an
arbitrary scalar potential certificate is equivalent, existentially, to the
desired queue bound: choosing `potential k = C - queue k` makes conservation
tautological.  Therefore this certificate is useful algebraically but is not a
noncircular Collatz resource construction.
-/

/-- Deprecated compatibility name for the former phantom-state structure. -/
abbrev CanonicalAmortizedResourceTransition (_n : OddNat) :=
  FiniteAmortizedResource

/-- Neutral scalar certificate connecting a finite amortized telescope to the
canonical reflected queue.  It intentionally makes no ownership claim. -/
def CanonicalAbstractAmortizationCertificate
    (n : OddNat) (P R : ℕ) : Prop :=
  ∃ A : FiniteAmortizedResource,
    (∀ m, A.queue m = canonicalOutstandingClaimQueue n m) ∧
      A.potential 0 ≤ P ∧
        ∀ m, ∑ k ∈ Finset.range m, A.replenishment k ≤ R

/-- Deprecated compatibility alias.  Despite its historical name, this
predicate is not noncircular; see
`exists_abstractAmortizationCertificate_iff_exists_queueUniformUpperBound`. -/
@[deprecated CanonicalAbstractAmortizationCertificate (since := "2026-07-16")]
abbrev CanonicalNoncircularGlobalAmortizationLaw :=
  CanonicalAbstractAmortizationCertificate

/-- A scalar certificate gives the corresponding canonical queue bound. -/
theorem CanonicalAbstractAmortizationCertificate.to_queueUniformUpperBound
    {n : OddNat} {P R : ℕ}
    (h : CanonicalAbstractAmortizationCertificate n P R) :
    CanonicalOutstandingClaimQueueUniformUpperBound n
      (canonicalOutstandingClaimQueue n 0 + P + R) := by
  rcases h with ⟨A, hqueue, hpotential, hreplenishment⟩
  intro m
  rw [← hqueue m, ← hqueue 0]
  exact A.queue_le_of_initialPotential_and_cumulativeReplenishment_bounds
    hpotential hreplenishment m

/-- Conditional challenge-facing consequence of the scalar certificate. -/
theorem CanonicalAbstractAmortizationCertificate.to_endpointWidthUniformUpperBound
    {n : OddNat} {P R : ℕ}
    (h : CanonicalAbstractAmortizationCertificate n P R) :
    CanonicalEndpointWidthUniformUpperBound n
      (bitWidth n.1 + (canonicalOutstandingClaimQueue n 0 + P + R)) :=
  h.to_queueUniformUpperBound.to_endpointWidthUniformUpperBound

/-- Reverse construction exposing the circular complement potential. -/
noncomputable def trivialAmortizedTransitionOfQueueBound
    {n : OddNat} {C : ℕ}
    (hC : CanonicalOutstandingClaimQueueUniformUpperBound n C) :
    FiniteAmortizedResource where
  queue k := canonicalOutstandingClaimQueue n k
  potential k := C - canonicalOutstandingClaimQueue n k
  consumed _ := 0
  replenishment _ := 0
  step_conservation k := by
    have hk := hC k
    have hks := hC (k + 1)
    omega

/-- Any assumed canonical queue bound manufactures the neutral certificate. -/
theorem CanonicalOutstandingClaimQueueUniformUpperBound.to_abstractAmortizationCertificate
    {n : OddNat} {C : ℕ}
    (hC : CanonicalOutstandingClaimQueueUniformUpperBound n C) :
    CanonicalAbstractAmortizationCertificate n C 0 := by
  refine ⟨trivialAmortizedTransitionOfQueueBound hC, ?_, ?_, ?_⟩
  · intro m
    rfl
  · exact Nat.sub_le _ _
  · intro m
    simp [trivialAmortizedTransitionOfQueueBound]

/-- Mandatory semantic regression: existential scalar amortization is exactly
as strong as an existential uniform queue bound. -/
theorem exists_abstractAmortizationCertificate_iff_exists_queueUniformUpperBound
    (n : OddNat) :
    (∃ P R, CanonicalAbstractAmortizationCertificate n P R) ↔
      ∃ C, CanonicalOutstandingClaimQueueUniformUpperBound n C := by
  constructor
  · rintro ⟨P, R, h⟩
    exact ⟨canonicalOutstandingClaimQueue n 0 + P + R,
      h.to_queueUniformUpperBound⟩
  · rintro ⟨C, hC⟩
    exact ⟨C, 0, hC.to_abstractAmortizationCertificate⟩

/-! ## Exact canonical reflected-queue observables -/

/-- Queue available immediately before canonical block `k` is served. -/
noncomputable def canonicalOutstandingClaimQueueBeforeBlock
    (n : OddNat) : ℕ → ℕ
  | 0 => 0
  | k + 1 => canonicalOutstandingClaimQueue n k

/-- Claims arriving at canonical block `k`. -/
noncomputable def canonicalQueueDemand (n : OddNat) (k : ℕ) : ℕ :=
  canonicalBlockClaimCount n k

/-- Anonymous capacity offered by canonical block `k`. -/
noncomputable def canonicalQueueService (n : OddNat) (k : ℕ) : ℕ :=
  canonicalBlockCapacityCount n k

/-- Service actually consumed is the minimum of available work and capacity. -/
noncomputable def canonicalQueueConsumed (n : OddNat) (k : ℕ) : ℕ :=
  min (canonicalOutstandingClaimQueueBeforeBlock n k + canonicalQueueDemand n k)
    (canonicalQueueService n k)

/-- Exact conservation for one reflected-queue block. -/
theorem canonicalOutstandingClaimQueue_add_consumed
    (n : OddNat) (k : ℕ) :
    canonicalOutstandingClaimQueue n k + canonicalQueueConsumed n k =
      canonicalOutstandingClaimQueueBeforeBlock n k + canonicalQueueDemand n k := by
  cases k with
  | zero =>
      change (canonicalBlockClaimCount n 0 - canonicalBlockCapacityCount n 0) +
          min (0 + canonicalBlockClaimCount n 0) (canonicalBlockCapacityCount n 0) =
        0 + canonicalBlockClaimCount n 0
      simp only [zero_add]
      by_cases h : canonicalBlockCapacityCount n 0 ≤ canonicalBlockClaimCount n 0
      · rw [Nat.min_eq_right h, Nat.sub_add_cancel h]
      · have hle : canonicalBlockClaimCount n 0 ≤ canonicalBlockCapacityCount n 0 :=
          Nat.le_of_not_ge h
        rw [Nat.min_eq_left hle, Nat.sub_eq_zero_of_le hle]
        simp
  | succ k =>
      change ((canonicalOutstandingClaimQueue n k + canonicalBlockClaimCount n (k + 1)) -
            canonicalBlockCapacityCount n (k + 1)) +
          min (canonicalOutstandingClaimQueue n k + canonicalBlockClaimCount n (k + 1))
            (canonicalBlockCapacityCount n (k + 1)) =
        canonicalOutstandingClaimQueue n k + canonicalBlockClaimCount n (k + 1)
      by_cases h : canonicalBlockCapacityCount n (k + 1) ≤
          canonicalOutstandingClaimQueue n k + canonicalBlockClaimCount n (k + 1)
      · rw [Nat.min_eq_right h, Nat.sub_add_cancel h]
      · have hle : canonicalOutstandingClaimQueue n k +
            canonicalBlockClaimCount n (k + 1) ≤
              canonicalBlockCapacityCount n (k + 1) := Nat.le_of_not_ge h
        rw [Nat.min_eq_left hle, Nat.sub_eq_zero_of_le hle]
        simp

/-!
## Owned-resource frontier

A genuine next layer must define a concrete finite carrier from `n`, together
with consumed and replenished subcarriers and an equivalence

`Available (k+1) ≃ (Available k \ Consumed k) ⊕ Replenished k`.

It must also prove disjoint old/new ownership, injective ownership of consumed
atoms, and temporal nonreuse.  No such carrier has yet been identified, so no
placeholder existence theorem is asserted.  Consequently
`CanonicalSaturatedSuccessorAbstractDischarge` is not yet formally connected
to this global scalar layer.
-/

end DkMath.Collatz
