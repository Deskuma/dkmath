/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Kernel.Normalize
import DkMath.NumberTheory.PrimitiveSet.RealWeightedPath

#print "file: DkMath.Kernel.SubProbability"

namespace DkMath.Kernel

namespace CapacityKernel

open DkMath.NumberTheory.PrimitiveSet

/--
The normalized outgoing weights of a positive-capacity parent as an existing
`RealWeightProvider`.
-/
noncomputable def normalizedRealWeightProvider
    (K : CapacityKernel α β)
    (a : α)
    (hcap : 0 < K.capacity a) :
    RealWeightProvider β where
  index := K.children a
  weight := K.normalizedWeight a
  weight_nonneg := by
    intro b hb
    exact K.normalizedWeight_nonneg a b hb hcap

@[simp] theorem normalizedRealWeightProvider_index
    (K : CapacityKernel α β)
    (a : α)
    (hcap : 0 < K.capacity a) :
    (K.normalizedRealWeightProvider a hcap).index = K.children a :=
  rfl

@[simp] theorem normalizedRealWeightProvider_weight
    (K : CapacityKernel α β)
    (a : α)
    (hcap : 0 < K.capacity a) :
    (K.normalizedRealWeightProvider a hcap).weight = K.normalizedWeight a :=
  rfl

/-- The provider total weight is the normalized outgoing mass. -/
theorem normalizedRealWeightProvider_totalWeight
    (K : CapacityKernel α β)
    (a : α)
    (hcap : 0 < K.capacity a) :
    (K.normalizedRealWeightProvider a hcap).totalWeight =
      K.normalizedOutgoing a :=
  rfl

/--
The normalized provider supplied by a capacity kernel is a finite
sub-probability provider.
-/
theorem normalizedRealWeightProvider_subProbability
    (K : CapacityKernel α β)
    (a : α)
    (hcap : 0 < K.capacity a) :
    (K.normalizedRealWeightProvider a hcap).SubProbability := by
  unfold RealWeightProvider.SubProbability
  rw [K.normalizedRealWeightProvider_totalWeight a hcap]
  exact K.normalizedOutgoing_le_one a hcap

end CapacityKernel

end DkMath.Kernel
