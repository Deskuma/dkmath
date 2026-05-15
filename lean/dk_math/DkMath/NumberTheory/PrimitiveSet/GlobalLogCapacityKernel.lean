/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PrimitiveSet.SubMarkovShadow
import DkMath.NumberTheory.PrimitiveSet.VonMangoldtShadow
import DkMath.NumberTheory.PrimitiveSet.FullChannelSet

#print "file: DkMath.NumberTheory.PrimitiveSet.GlobalLogCapacityKernel"

namespace DkMath.NumberTheory.PrimitiveSet

open DkMath.Kernel

/-- Source states whose logarithmic capacity is positive. -/
abbrev LogCapacityState : Type :=
  { n : ℕ // 1 < n }

namespace LogCapacityState

@[simp] theorem one_lt (s : LogCapacityState) : 1 < s.1 :=
  s.2

/-- The logarithmic capacity of a global source state is positive. -/
theorem log_capacity_pos (s : LogCapacityState) :
    0 < Real.log (s.1 : ℝ) :=
  real_log_nat_pos_of_one_lt s.2

end LogCapacityState

namespace PrimePowerWitnessProvider

/--
Global log-capacity kernel over all source states `n > 1`.

The finite channel set is supplied externally by `IOf`; this keeps the first
global layer independent of any choice of a full divisor enumeration.
-/
noncomputable def globalLogCapacityKernel
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (IOf : ℕ → Finset ℕ)
    (hIOf :
      ∀ n q, q ∈ IOf n → q ∈ T.toDivisorTransitionKernel.index n) :
    CapacityKernel LogCapacityState ℕ where
  children := fun s => IOf s.1
  capacity := fun s => Real.log (s.1 : ℝ)
  cost := fun s q =>
    W.vonMangoldtShadowCost s.1 (IOf s.1) (hIOf s.1) q
  cost_nonneg := by
    intro s q hq
    exact W.witnessLogCost_nonneg_on s.1 (IOf s.1) (hIOf s.1) q hq
  outgoing_le := by
    intro s
    exact W.basePrimeOf_logCapacity_outgoing_le
      s.1 (IOf s.1) (hIOf s.1) s.2

@[simp] theorem globalLogCapacityKernel_children
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (IOf : ℕ → Finset ℕ)
    (hIOf :
      ∀ n q, q ∈ IOf n → q ∈ T.toDivisorTransitionKernel.index n)
    (s : LogCapacityState) :
    (W.globalLogCapacityKernel IOf hIOf).children s = IOf s.1 :=
  rfl

@[simp] theorem globalLogCapacityKernel_capacity
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (IOf : ℕ → Finset ℕ)
    (hIOf :
      ∀ n q, q ∈ IOf n → q ∈ T.toDivisorTransitionKernel.index n)
    (s : LogCapacityState) :
    (W.globalLogCapacityKernel IOf hIOf).capacity s =
      Real.log (s.1 : ℝ) :=
  rfl

@[simp] theorem globalLogCapacityKernel_cost
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (IOf : ℕ → Finset ℕ)
    (hIOf :
      ∀ n q, q ∈ IOf n → q ∈ T.toDivisorTransitionKernel.index n)
    (s : LogCapacityState) :
    (W.globalLogCapacityKernel IOf hIOf).cost s =
      W.vonMangoldtShadowCost s.1 (IOf s.1) (hIOf s.1) :=
  rfl

/-- Every global log-capacity parent has positive capacity. -/
theorem globalLogCapacityKernel_capacity_pos
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (IOf : ℕ → Finset ℕ)
    (hIOf :
      ∀ n q, q ∈ IOf n → q ∈ T.toDivisorTransitionKernel.index n)
    (s : LogCapacityState) :
    0 < (W.globalLogCapacityKernel IOf hIOf).capacity s :=
  s.log_capacity_pos

/--
The global log-capacity kernel supplies an existing real-weight provider at
each source state.
-/
noncomputable def globalLogCapacityKernelRealWeightProvider
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (IOf : ℕ → Finset ℕ)
    (hIOf :
      ∀ n q, q ∈ IOf n → q ∈ T.toDivisorTransitionKernel.index n)
    (s : LogCapacityState) :
    RealWeightProvider ℕ :=
  (W.globalLogCapacityKernel IOf hIOf).normalizedRealWeightProvider s
    (W.globalLogCapacityKernel_capacity_pos IOf hIOf s)

@[simp] theorem globalLogCapacityKernelRealWeightProvider_index
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (IOf : ℕ → Finset ℕ)
    (hIOf :
      ∀ n q, q ∈ IOf n → q ∈ T.toDivisorTransitionKernel.index n)
    (s : LogCapacityState) :
    (W.globalLogCapacityKernelRealWeightProvider IOf hIOf s).index =
      IOf s.1 :=
  rfl

@[simp] theorem globalLogCapacityKernelRealWeightProvider_weight
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (IOf : ℕ → Finset ℕ)
    (hIOf :
      ∀ n q, q ∈ IOf n → q ∈ T.toDivisorTransitionKernel.index n)
    (s : LogCapacityState) :
    (W.globalLogCapacityKernelRealWeightProvider IOf hIOf s).weight =
      W.normalizedVonMangoldtShadowWeight s.1 (IOf s.1) (hIOf s.1) :=
  rfl

/-- The global provider at every state is sub-probability normalized. -/
theorem globalLogCapacityKernelRealWeightProvider_subProbability
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (IOf : ℕ → Finset ℕ)
    (hIOf :
      ∀ n q, q ∈ IOf n → q ∈ T.toDivisorTransitionKernel.index n)
    (s : LogCapacityState) :
    (W.globalLogCapacityKernelRealWeightProvider IOf hIOf s).SubProbability :=
  (W.globalLogCapacityKernel IOf hIOf).normalizedRealWeightProvider_subProbability s
    (W.globalLogCapacityKernel_capacity_pos IOf hIOf s)

/--
Expression-level global normalized shadow bound at a source state.
-/
theorem globalLogCapacityKernel_normalizedShadow_subProbability
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (IOf : ℕ → Finset ℕ)
    (hIOf :
      ∀ n q, q ∈ IOf n → q ∈ T.toDivisorTransitionKernel.index n)
    (s : LogCapacityState) :
    (IOf s.1).sum
      (fun q => W.normalizedVonMangoldtShadowWeight s.1 (IOf s.1) (hIOf s.1) q) ≤
        1 := by
  simpa [RealWeightProvider.SubProbability, RealWeightProvider.totalWeight]
    using W.globalLogCapacityKernelRealWeightProvider_subProbability IOf hIOf s

/--
The normalized global log-capacity kernel as a sub-Markov shadow.
-/
noncomputable def globalLogCapacitySubMarkovShadow
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (IOf : ℕ → Finset ℕ)
    (hIOf :
      ∀ n q, q ∈ IOf n → q ∈ T.toDivisorTransitionKernel.index n) :
    SubMarkovShadow LogCapacityState ℕ :=
  SubMarkovShadow.ofCapacityKernel (W.globalLogCapacityKernel IOf hIOf)
    (W.globalLogCapacityKernel_capacity_pos IOf hIOf)

@[simp] theorem globalLogCapacitySubMarkovShadow_index
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (IOf : ℕ → Finset ℕ)
    (hIOf :
      ∀ n q, q ∈ IOf n → q ∈ T.toDivisorTransitionKernel.index n)
    (s : LogCapacityState) :
    (W.globalLogCapacitySubMarkovShadow IOf hIOf).index s =
      IOf s.1 :=
  rfl

@[simp] theorem globalLogCapacitySubMarkovShadow_weight
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (IOf : ℕ → Finset ℕ)
    (hIOf :
      ∀ n q, q ∈ IOf n → q ∈ T.toDivisorTransitionKernel.index n)
    (s : LogCapacityState) :
    (W.globalLogCapacitySubMarkovShadow IOf hIOf).weight s =
      W.normalizedVonMangoldtShadowWeight s.1 (IOf s.1) (hIOf s.1) :=
  rfl

/-- The global normalized shadow is sub-Markov normalized at every state. -/
theorem globalLogCapacitySubMarkovShadow_subProbability
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (IOf : ℕ → Finset ℕ)
    (hIOf :
      ∀ n q, q ∈ IOf n → q ∈ T.toDivisorTransitionKernel.index n) :
    (W.globalLogCapacitySubMarkovShadow IOf hIOf).SubProbability :=
  SubMarkovShadow.ofCapacityKernel_subProbability
    (W.globalLogCapacityKernel IOf hIOf)
    (W.globalLogCapacityKernel_capacity_pos IOf hIOf)

/--
Global log-capacity kernel for a declared full channel set.

This is still the capacity-kernel layer.  Fullness records that the selected
channels are extensionally the transition index; the later equality route must
add the analytic `Σ log p = log n` statement separately.
-/
noncomputable def fullGlobalLogCapacityKernel
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (C : FullPrimePowerChannelSet T) :
    CapacityKernel LogCapacityState ℕ :=
  W.globalLogCapacityKernel C.channels C.subset_index

@[simp] theorem fullGlobalLogCapacityKernel_children
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (C : FullPrimePowerChannelSet T)
    (s : LogCapacityState) :
    (W.fullGlobalLogCapacityKernel C).children s = C.channels s.1 :=
  rfl

theorem fullGlobalLogCapacityKernel_children_eq_index
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (C : FullPrimePowerChannelSet T)
    (s : LogCapacityState) :
    (W.fullGlobalLogCapacityKernel C).children s =
      T.toDivisorTransitionKernel.index s.1 :=
  C.channels_eq_index s.1

/-- The normalized full-channel log-capacity kernel as a sub-Markov shadow. -/
noncomputable def fullGlobalLogCapacitySubMarkovShadow
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (C : FullPrimePowerChannelSet T) :
    SubMarkovShadow LogCapacityState ℕ :=
  W.globalLogCapacitySubMarkovShadow C.channels C.subset_index

@[simp] theorem fullGlobalLogCapacitySubMarkovShadow_index
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (C : FullPrimePowerChannelSet T)
    (s : LogCapacityState) :
    (W.fullGlobalLogCapacitySubMarkovShadow C).index s = C.channels s.1 :=
  rfl

theorem fullGlobalLogCapacitySubMarkovShadow_index_eq_index
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (C : FullPrimePowerChannelSet T)
    (s : LogCapacityState) :
    (W.fullGlobalLogCapacitySubMarkovShadow C).index s =
      T.toDivisorTransitionKernel.index s.1 :=
  C.channels_eq_index s.1

/-- Full-channel normalized shadow is still sub-Markov before equality is proved. -/
theorem fullGlobalLogCapacitySubMarkovShadow_subProbability
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (C : FullPrimePowerChannelSet T) :
    (W.fullGlobalLogCapacitySubMarkovShadow C).SubProbability :=
  W.globalLogCapacitySubMarkovShadow_subProbability C.channels C.subset_index

end PrimePowerWitnessProvider

end DkMath.NumberTheory.PrimitiveSet
