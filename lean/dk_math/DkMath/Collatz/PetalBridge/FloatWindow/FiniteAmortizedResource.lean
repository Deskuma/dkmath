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
# Finite amortized balance telescope

This scalar combinator has no ownership semantics.  `inflow` and `outflow`
are neutral accounting streams; a caller must separately prove that they come
from concrete resources if that interpretation is required.
-/

/-- Generic finite-step balance data. -/
structure FiniteAmortizedBalance where
  queue : ℕ → ℕ
  potential : ℕ → ℕ
  outflow : ℕ → ℕ
  inflow : ℕ → ℕ
  step_conservation :
    ∀ k, queue (k + 1) + potential (k + 1) + outflow k ≤
      queue k + potential k + inflow k

/-- Compatibility alias for the original scalar type name. -/
abbrev FiniteAmortizedResource := FiniteAmortizedBalance

namespace FiniteAmortizedBalance

/-- Keeping all outflow terms gives the strongest finite-prefix telescope. -/
theorem queue_add_potential_add_sum_outflow_le_initial_add_sum_inflow
    (A : FiniteAmortizedBalance) (m : ℕ) :
    A.queue m + A.potential m + ∑ k ∈ Finset.range m, A.outflow k ≤
      A.queue 0 + A.potential 0 + ∑ k ∈ Finset.range m, A.inflow k := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hstep := A.step_conservation m
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      omega

/-- Dropping the nonnegative cumulative outflow gives the weaker telescope. -/
theorem queue_add_potential_le_initial_add_sum
    (A : FiniteAmortizedBalance) (m : ℕ) :
    A.queue m + A.potential m ≤
      A.queue 0 + A.potential 0 + ∑ k ∈ Finset.range m, A.inflow k := by
  have h := A.queue_add_potential_add_sum_outflow_le_initial_add_sum_inflow m
  omega

/-- The direct queue estimate uses only the initial potential. -/
theorem queue_le_initial_add_potential_add_cumulativeInflow
    (A : FiniteAmortizedBalance) (m : ℕ) :
    A.queue m ≤
      A.queue 0 + A.potential 0 + ∑ k ∈ Finset.range m, A.inflow k := by
  have h := A.queue_add_potential_le_initial_add_sum m
  omega

/-- Bounded cumulative net inflow, rather than bounded total inflow, controls
the queue in a stable system with ongoing throughput. -/
theorem queue_le_of_cumulativeInflow_le_cumulativeOutflow_add
    (A : FiniteAmortizedBalance) {B : ℕ}
    (hnet : ∀ m, ∑ k ∈ Finset.range m, A.inflow k ≤
      (∑ k ∈ Finset.range m, A.outflow k) + B) (m : ℕ) :
    A.queue m ≤ A.queue 0 + A.potential 0 + B := by
  have htel := A.queue_add_potential_add_sum_outflow_le_initial_add_sum_inflow m
  have hm := hnet m
  omega

/-- Wrapper using an explicit upper bound for the initial potential. -/
theorem queue_le_of_initialPotential_and_boundedNetInflow
    (A : FiniteAmortizedBalance) {P B : ℕ}
    (hpotential : A.potential 0 ≤ P)
    (hnet : ∀ m, ∑ k ∈ Finset.range m, A.inflow k ≤
      (∑ k ∈ Finset.range m, A.outflow k) + B) (m : ℕ) :
    A.queue m ≤ A.queue 0 + P + B := by
  have hqueue := A.queue_le_of_cumulativeInflow_le_cumulativeOutflow_add hnet m
  omega

/-- Compatibility theorem for the stronger bounded-total-inflow hypothesis. -/
theorem queue_le_of_initialPotential_and_cumulativeReplenishment_bounds
    (A : FiniteAmortizedBalance) {P R : ℕ}
    (hpotential : A.potential 0 ≤ P)
    (hinflow : ∀ m, ∑ k ∈ Finset.range m, A.inflow k ≤ R) (m : ℕ) :
    A.queue m ≤ A.queue 0 + P + R := by
  have hqueue := A.queue_le_initial_add_potential_add_cumulativeInflow m
  have hm := hinflow m
  omega

/-- Compatibility corollary with an unnecessarily uniform potential bound. -/
theorem queue_le_of_potential_and_cumulative_replenishment_bounds
    (A : FiniteAmortizedBalance) {P R : ℕ}
    (hpotential : ∀ k, A.potential k ≤ P)
    (hinflow : ∀ m, ∑ k ∈ Finset.range m, A.inflow k ≤ R) (m : ℕ) :
    A.queue m ≤ A.queue 0 + P + R :=
  A.queue_le_of_initialPotential_and_cumulativeReplenishment_bounds
    (hpotential 0) hinflow m

end FiniteAmortizedBalance

/-! ## Stable-throughput regression -/

/-- A stable balance with one unit entering and leaving at every step. -/
def stableUnitThroughputBalance : FiniteAmortizedBalance where
  queue _ := 0
  potential _ := 0
  outflow _ := 1
  inflow _ := 1
  step_conservation _ := by simp

/-- The stable-throughput queue is identically zero. -/
theorem stableUnitThroughputBalance_queue (k : ℕ) :
    stableUnitThroughputBalance.queue k = 0 := rfl

/-- Conservation in the stable-throughput example is exact. -/
theorem stableUnitThroughputBalance_step_exact (k : ℕ) :
    stableUnitThroughputBalance.queue (k + 1) +
        stableUnitThroughputBalance.potential (k + 1) +
          stableUnitThroughputBalance.outflow k =
      stableUnitThroughputBalance.queue k +
        stableUnitThroughputBalance.potential k +
          stableUnitThroughputBalance.inflow k := by
  rfl

/-- No finite constant bounds every cumulative inflow prefix, even though the
queue is uniformly zero. -/
theorem stableUnitThroughputBalance_no_cumulativeInflow_bound :
    ¬ ∃ R, ∀ m, ∑ k ∈ Finset.range m,
      stableUnitThroughputBalance.inflow k ≤ R := by
  rintro ⟨R, hR⟩
  have h := hR (R + 1)
  simp [stableUnitThroughputBalance] at h

end DkMath.Collatz
