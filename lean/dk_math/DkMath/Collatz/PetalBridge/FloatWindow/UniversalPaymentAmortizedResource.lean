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
  ∃ A : FiniteAmortizedBalance,
    (∀ m, A.queue m = canonicalOutstandingClaimQueue n m) ∧
      A.potential 0 ≤ P ∧
        ∀ m, ∑ k ∈ Finset.range m, A.inflow k ≤ R

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

namespace CanonicalNoncircularGlobalAmortizationLaw

/-- Deprecated fully qualified wrapper for the former public theorem. -/
@[deprecated CanonicalAbstractAmortizationCertificate.to_queueUniformUpperBound
  (since := "2026-07-16")]
theorem to_queueUniformUpperBound
    {n : OddNat} {P R : ℕ}
    (h : CanonicalAbstractAmortizationCertificate n P R) :
    CanonicalOutstandingClaimQueueUniformUpperBound n
      (canonicalOutstandingClaimQueue n 0 + P + R) :=
  CanonicalAbstractAmortizationCertificate.to_queueUniformUpperBound h

/-- Deprecated fully qualified wrapper for the former public theorem. -/
@[deprecated CanonicalAbstractAmortizationCertificate.to_endpointWidthUniformUpperBound
  (since := "2026-07-16")]
theorem to_endpointWidthUniformUpperBound
    {n : OddNat} {P R : ℕ}
    (h : CanonicalAbstractAmortizationCertificate n P R) :
    CanonicalEndpointWidthUniformUpperBound n
      (bitWidth n.1 + (canonicalOutstandingClaimQueue n 0 + P + R)) :=
  CanonicalAbstractAmortizationCertificate.to_endpointWidthUniformUpperBound h

end CanonicalNoncircularGlobalAmortizationLaw

/-- Reverse construction exposing the circular complement potential. -/
noncomputable def trivialAmortizedTransitionOfQueueBound
    {n : OddNat} {C : ℕ}
    (hC : CanonicalOutstandingClaimQueueUniformUpperBound n C) :
    FiniteAmortizedBalance where
  queue k := canonicalOutstandingClaimQueue n k
  potential k := C - canonicalOutstandingClaimQueue n k
  outflow _ := 0
  inflow _ := 0
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

/-- The queue before the initial block is empty. -/
@[simp] theorem canonicalOutstandingClaimQueueBeforeBlock_zero (n : OddNat) :
    canonicalOutstandingClaimQueueBeforeBlock n 0 = 0 := rfl

/-- Before successor block `k+1`, the queue is the queue after block `k`. -/
@[simp] theorem canonicalOutstandingClaimQueueBeforeBlock_succ
    (n : OddNat) (k : ℕ) :
    canonicalOutstandingClaimQueueBeforeBlock n (k + 1) =
      canonicalOutstandingClaimQueue n k := rfl

/-- The exact canonical reflected queue as a neutral scalar balance. -/
noncomputable def canonicalQueueFiniteAmortizedBalance
    (n : OddNat) : FiniteAmortizedBalance where
  queue := canonicalOutstandingClaimQueueBeforeBlock n
  potential _ := 0
  outflow := canonicalQueueConsumed n
  inflow := canonicalQueueDemand n
  step_conservation k := by
    simp only [canonicalOutstandingClaimQueueBeforeBlock_succ]
    exact (canonicalOutstandingClaimQueue_add_consumed n k).le

/-! ## Exact unused service -/

/-- Capacity not used by the reflected queue in canonical block `k`. -/
noncomputable def canonicalQueueUnusedService (n : OddNat) (k : ℕ) : ℕ :=
  canonicalQueueService n k - canonicalQueueConsumed n k

/-- Actual consumption never exceeds current service capacity. -/
theorem canonicalQueueConsumed_le_service (n : OddNat) (k : ℕ) :
    canonicalQueueConsumed n k ≤ canonicalQueueService n k := by
  exact min_le_right _ _

/-- Actual consumption never exceeds available old and new work. -/
theorem canonicalQueueConsumed_le_available (n : OddNat) (k : ℕ) :
    canonicalQueueConsumed n k ≤
      canonicalOutstandingClaimQueueBeforeBlock n k + canonicalQueueDemand n k := by
  exact min_le_left _ _

/-- Service partitions exactly into consumed and unused capacity. -/
theorem canonicalQueueService_eq_consumed_add_unusedService
    (n : OddNat) (k : ℕ) :
    canonicalQueueService n k =
      canonicalQueueConsumed n k + canonicalQueueUnusedService n k := by
  unfold canonicalQueueUnusedService
  exact (Nat.add_sub_of_le (canonicalQueueConsumed_le_service n k)).symm

/-- The post-block queue is available work minus actual consumption. -/
theorem canonicalOutstandingClaimQueue_eq_available_sub_consumed
    (n : OddNat) (k : ℕ) :
    canonicalOutstandingClaimQueue n k =
      canonicalOutstandingClaimQueueBeforeBlock n k + canonicalQueueDemand n k -
        canonicalQueueConsumed n k := by
  have hconserve := canonicalOutstandingClaimQueue_add_consumed n k
  have hle := canonicalQueueConsumed_le_available n k
  omega

/-! ## Exact canonical prefix balance -/

/-- Exact telescoping equality for every prefix of canonical blocks. -/
theorem canonicalQueueBefore_add_sum_consumed_eq_sum_demand
    (n : OddNat) (m : ℕ) :
    canonicalOutstandingClaimQueueBeforeBlock n m +
        ∑ k ∈ Finset.range m, canonicalQueueConsumed n k =
      ∑ k ∈ Finset.range m, canonicalQueueDemand n k := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ,
        canonicalOutstandingClaimQueueBeforeBlock_succ]
      have hstep := canonicalOutstandingClaimQueue_add_consumed n m
      omega

/-- The queue before block `m` is cumulative demand minus cumulative actual
consumption. -/
theorem canonicalQueueBefore_eq_sum_demand_sub_sum_consumed
    (n : OddNat) (m : ℕ) :
    canonicalOutstandingClaimQueueBeforeBlock n m =
      (∑ k ∈ Finset.range m, canonicalQueueDemand n k) -
        ∑ k ∈ Finset.range m, canonicalQueueConsumed n k := by
  have h := canonicalQueueBefore_add_sum_consumed_eq_sum_demand n m
  omega

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
