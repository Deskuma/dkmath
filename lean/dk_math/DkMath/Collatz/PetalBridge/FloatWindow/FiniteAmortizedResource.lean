/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

#print "file: DkMath.Collatz.PetalBridge.FloatWindow.FiniteAmortizedResource"

namespace DkMath.Collatz

/-!
# Finite amortized resource telescope

This module is deliberately independent of the Collatz observables.  It only
records a scalar queue, a scalar potential, consumed mass, replenishment, and
one-step conservation.  In particular, there is no phantom state carrier.
-/

/-- Generic finite-step amortized accounting data. -/
structure FiniteAmortizedResource where
  queue : ℕ → ℕ
  potential : ℕ → ℕ
  consumed : ℕ → ℕ
  replenishment : ℕ → ℕ
  step_conservation :
    ∀ k, queue (k + 1) + potential (k + 1) + consumed k ≤
      queue k + potential k + replenishment k

namespace FiniteAmortizedResource

/-- Iterating one-step conservation gives the finite-prefix resource ceiling. -/
theorem queue_add_potential_le_initial_add_sum
    (A : FiniteAmortizedResource) (m : ℕ) :
    A.queue m + A.potential m ≤
      A.queue 0 + A.potential 0 + ∑ k ∈ Finset.range m, A.replenishment k := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hstep := A.step_conservation m
      rw [Finset.sum_range_succ]
      omega

/-- The sharp queue estimate uses only the initial potential. -/
theorem queue_le_initial_add_potential_add_cumulativeReplenishment
    (A : FiniteAmortizedResource) (m : ℕ) :
    A.queue m ≤
      A.queue 0 + A.potential 0 + ∑ k ∈ Finset.range m, A.replenishment k := by
  have h := A.queue_add_potential_le_initial_add_sum m
  omega

/-- Initial potential and cumulative replenishment bounds give a queue bound. -/
theorem queue_le_of_initialPotential_and_cumulativeReplenishment_bounds
    (A : FiniteAmortizedResource) {P R : ℕ}
    (hpotential : A.potential 0 ≤ P)
    (hreplenishment : ∀ m,
      ∑ k ∈ Finset.range m, A.replenishment k ≤ R) (m : ℕ) :
    A.queue m ≤ A.queue 0 + P + R := by
  have hqueue := A.queue_le_initial_add_potential_add_cumulativeReplenishment m
  have hrepl := hreplenishment m
  omega

/-- Compatibility corollary: a uniform potential bound is stronger than the
initial bound actually used by the telescope. -/
theorem queue_le_of_potential_and_cumulative_replenishment_bounds
    (A : FiniteAmortizedResource) {P R : ℕ}
    (hpotential : ∀ k, A.potential k ≤ P)
    (hreplenishment : ∀ m,
      ∑ k ∈ Finset.range m, A.replenishment k ≤ R) (m : ℕ) :
    A.queue m ≤ A.queue 0 + P + R :=
  A.queue_le_of_initialPotential_and_cumulativeReplenishment_bounds
    (hpotential 0) hreplenishment m

end FiniteAmortizedResource

end DkMath.Collatz
