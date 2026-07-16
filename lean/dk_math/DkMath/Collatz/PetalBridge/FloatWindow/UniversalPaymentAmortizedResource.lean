/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentAmplitude

#print "file: DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentAmortizedResource"

namespace DkMath.Collatz

/-!
# Transition-based amortized resource interface

This module states the global resource contract without assuming a global
injection into a pre-existing finite carrier.  A resource state evolves at
each block.  The only accounting axiom is a one-step conservation inequality.

The replenishment hypothesis below is cumulative.  A merely pointwise bound
on replenishment would allow linear growth and cannot imply a uniform queue
bound.  No Collatz instance of this interface is asserted here.
-/

/-- A dynamic resource state with an explicit queue, potential, demand,
consumption, and derived replenishment stream. -/
structure CanonicalAmortizedResourceTransition (n : OddNat) where
  State : ℕ → Type
  state : (k : ℕ) → State k
  potential : ℕ → ℕ
  queue : ℕ → ℕ
  demand : ℕ → ℕ
  consumed : ℕ → ℕ
  replenishment : ℕ → ℕ
  demand_le_consumed_add_nextQueue :
    ∀ k, demand k ≤ consumed k + queue (k + 1)
  step_conservation :
    ∀ k, queue (k + 1) + potential (k + 1) + consumed k ≤
      queue k + potential k + replenishment k

namespace CanonicalAmortizedResourceTransition

/-- Iterating one-step conservation gives the exact finite-prefix resource
ceiling. -/
theorem queue_add_potential_le_initial_add_sum
    {n : OddNat} (A : CanonicalAmortizedResourceTransition n) (m : ℕ) :
    A.queue m + A.potential m ≤
      A.queue 0 + A.potential 0 + ∑ k ∈ Finset.range m, A.replenishment k := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hstep := A.step_conservation m
      rw [Finset.sum_range_succ]
      omega

/-- A uniform potential ceiling and a cumulative replenishment ceiling imply
a uniform queue ceiling. -/
theorem queue_le_of_potential_and_cumulative_replenishment_bounds
    {n : OddNat} (A : CanonicalAmortizedResourceTransition n)
    {P R : ℕ} (hpotential : ∀ k, A.potential k ≤ P)
    (hreplenishment : ∀ m,
      ∑ k ∈ Finset.range m, A.replenishment k ≤ R) (m : ℕ) :
    A.queue m ≤ A.queue 0 + P + R := by
  have hprefix := A.queue_add_potential_le_initial_add_sum m
  have hp0 := hpotential 0
  have hr := hreplenishment m
  omega

end CanonicalAmortizedResourceTransition

/--
Noncircular conditional interface for the canonical queue.  It asks for a
transition law whose queue observable is the existing canonical queue, plus
independently stated potential and cumulative-replenishment ceilings.  It does
not include the desired queue bound as a field.
-/
def CanonicalNoncircularGlobalAmortizationLaw
    (n : OddNat) (P R : ℕ) : Prop :=
  ∃ A : CanonicalAmortizedResourceTransition n,
    (∀ m, A.queue m = canonicalOutstandingClaimQueue n m) ∧
      (∀ k, A.potential k ≤ P) ∧
        ∀ m, ∑ k ∈ Finset.range m, A.replenishment k ≤ R

/-- The noncircular amortization law yields a named uniform scalar queue
bound. -/
theorem CanonicalNoncircularGlobalAmortizationLaw.to_queueUniformUpperBound
    {n : OddNat} {P R : ℕ}
    (h : CanonicalNoncircularGlobalAmortizationLaw n P R) :
    CanonicalOutstandingClaimQueueUniformUpperBound n
      (canonicalOutstandingClaimQueue n 0 + P + R) := by
  rcases h with ⟨A, hqueue, hpotential, hreplenishment⟩
  intro m
  rw [← hqueue m, ← hqueue 0]
  exact A.queue_le_of_potential_and_cumulative_replenishment_bounds
    hpotential hreplenishment m

/-- Conditional challenge-facing chain from amortization to endpoint width. -/
theorem CanonicalNoncircularGlobalAmortizationLaw.to_endpointWidthUniformUpperBound
    {n : OddNat} {P R : ℕ}
    (h : CanonicalNoncircularGlobalAmortizationLaw n P R) :
    CanonicalEndpointWidthUniformUpperBound n
      (bitWidth n.1 + (canonicalOutstandingClaimQueue n 0 + P + R)) :=
  h.to_queueUniformUpperBound.to_endpointWidthUniformUpperBound

/-!
## Proven frontier

Route 1 stops at a concrete obstruction: exact adjacent core-word recurrence
permits carry alternation, so it supplies no monotone claim-density estimate.

Route 2 is now logically sound but conditional.  The first missing theorem is
an actual Collatz construction of `CanonicalNoncircularGlobalAmortizationLaw`
with a cumulative replenishment ceiling.  Current width decreases and negative
local drift do not yet carry temporal ownership, so the same replenishment
event could be reused without a proved multiplicity bound.  Replacing this
missing construction by a queue ceiling would be circular.
-/

end DkMath.Collatz
