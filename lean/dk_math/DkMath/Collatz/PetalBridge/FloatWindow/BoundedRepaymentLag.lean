/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.Algebra.Order.BigOperators.Group.Finset

#print "file: DkMath.Collatz.PetalBridge.FloatWindow.BoundedRepaymentLag"

namespace DkMath.Collatz

/-!
# Generic bounded repayment lag

The predicate below is the scalar consequence of an owned statement saying
that every outstanding arrival at time `m` was born in one of the preceding
`L` slots.  It is independent of Collatz and deliberately does not manufacture
claim ownership.
-/

/-- Outstanding work is covered by arrivals in the preceding `L` slots. -/
def OutstandingQueueHasRepaymentLag
    (queue arrivals : ℕ → ℕ) (L : ℕ) : Prop :=
  ∀ m, queue m ≤ ∑ j ∈ Finset.range L, arrivals (m - L + j)

/-- A lag bound `L` and per-slot arrival bound `A` imply queue bound `L*A`. -/
theorem queue_le_mul_of_repaymentLag_of_arrivals_le
    {queue arrivals : ℕ → ℕ} {L A : ℕ}
    (hlag : OutstandingQueueHasRepaymentLag queue arrivals L)
    (harrivals : ∀ k, arrivals k ≤ A) (m : ℕ) :
    queue m ≤ L * A := by
  calc
    queue m ≤ ∑ j ∈ Finset.range L, arrivals (m - L + j) := hlag m
    _ ≤ ∑ _j ∈ Finset.range L, A :=
      Finset.sum_le_sum fun j _ => harrivals (m - L + j)
    _ = L * A := by simp

/-- Caller-facing uniform form of the generic lag theorem. -/
theorem repaymentLag_uniformUpperBound
    {queue arrivals : ℕ → ℕ} {L A : ℕ}
    (hlag : OutstandingQueueHasRepaymentLag queue arrivals L)
    (harrivals : ∀ k, arrivals k ≤ A) :
    ∀ m, queue m ≤ L * A :=
  fun m => queue_le_mul_of_repaymentLag_of_arrivals_le hlag harrivals m

/-!
For the canonical Collatz queue, the missing theorem is not the generic
counting argument above.  It is an owned statement that each actual claim is
consumed within one uniform number of later canonical blocks.  The current
residue and saturated-successor grammar proves repayment for selected local
branches, but no theorem supplies a uniform lag for all canonical claims.
-/

end DkMath.Collatz
