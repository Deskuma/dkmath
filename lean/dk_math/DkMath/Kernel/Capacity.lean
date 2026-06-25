/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib

#print "file: DkMath.Kernel.Capacity"

open scoped BigOperators

namespace DkMath.Kernel

/--
A finite capacity kernel.

The structure records finite outgoing channels, a parent capacity, a nonnegative
channel cost, and the outgoing capacity bound.  It is intentionally not a
probability object: normalization is supplied in `DkMath.Kernel.Normalize`.
-/
structure CapacityKernel (α β : Type _) where
  children : α → Finset β
  capacity : α → ℝ
  cost : α → β → ℝ
  cost_nonneg : ∀ a b, b ∈ children a → 0 ≤ cost a b
  outgoing_le : ∀ a, (children a).sum (cost a) ≤ capacity a

namespace CapacityKernel

/-- Total outgoing cost from a parent state. -/
noncomputable def outgoingCost
    (K : CapacityKernel α β)
    (a : α) : ℝ :=
  (K.children a).sum (K.cost a)

/-- The outgoing cost is nonnegative because all channel costs are nonnegative. -/
theorem outgoingCost_nonneg
    (K : CapacityKernel α β)
    (a : α) :
    0 ≤ K.outgoingCost a := by
  unfold outgoingCost
  exact Finset.sum_nonneg (fun b hb => K.cost_nonneg a b hb)

/-- The structure field exposed under the `outgoingCost` abbreviation. -/
theorem outgoingCost_le_capacity
    (K : CapacityKernel α β)
    (a : α) :
    K.outgoingCost a ≤ K.capacity a := by
  unfold outgoingCost
  exact K.outgoing_le a

end CapacityKernel

end DkMath.Kernel
