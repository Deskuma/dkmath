/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Kernel.Capacity

#print "file: DkMath.Kernel.Normalize"

open scoped BigOperators

namespace DkMath.Kernel

namespace CapacityKernel

/-- Channel weight obtained by dividing cost by the parent capacity. -/
noncomputable def normalizedWeight
    (K : CapacityKernel α β)
    (a : α)
    (b : β) : ℝ :=
  K.cost a b / K.capacity a

/-- Total normalized outgoing mass from a parent state. -/
noncomputable def normalizedOutgoing
    (K : CapacityKernel α β)
    (a : α) : ℝ :=
  (K.children a).sum (K.normalizedWeight a)

/-- Normalized channel weights are nonnegative when the parent capacity is positive. -/
theorem normalizedWeight_nonneg
    (K : CapacityKernel α β)
    (a : α)
    (b : β)
    (hb : b ∈ K.children a)
    (hcap : 0 < K.capacity a) :
    0 ≤ K.normalizedWeight a b := by
  unfold normalizedWeight
  exact div_nonneg (K.cost_nonneg a b hb) (le_of_lt hcap)

/-- The normalized outgoing mass is the outgoing cost divided by capacity. -/
theorem normalizedOutgoing_eq_outgoingCost_div
    (K : CapacityKernel α β)
    (a : α) :
    K.normalizedOutgoing a = K.outgoingCost a / K.capacity a := by
  unfold normalizedOutgoing normalizedWeight outgoingCost
  rw [Finset.sum_div]

/--
Positive-capacity normalization turns a capacity kernel into a sub-probability
bound on the finite outgoing channels.
-/
theorem normalizedOutgoing_le_one
    (K : CapacityKernel α β)
    (a : α)
    (hcap : 0 < K.capacity a) :
    K.normalizedOutgoing a ≤ 1 := by
  rw [K.normalizedOutgoing_eq_outgoingCost_div a]
  exact (div_le_iff₀ hcap).mpr (by
    simpa using K.outgoingCost_le_capacity a)

/--
Expression-level form of `normalizedOutgoing_le_one`, useful when constructing
Markov/sub-Markov-style weights directly from a capacity kernel.
-/
theorem normalizedWeight_subProbability
    (K : CapacityKernel α β)
    (a : α)
    (hcap : 0 < K.capacity a) :
    (K.children a).sum (fun b => K.cost a b / K.capacity a) ≤ 1 := by
  simpa [normalizedOutgoing, normalizedWeight] using
    K.normalizedOutgoing_le_one a hcap

end CapacityKernel

end DkMath.Kernel
