/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Kernel.SubProbability

#print "file: DkMath.NumberTheory.PrimitiveSet.SubMarkovShadow"

namespace DkMath.NumberTheory.PrimitiveSet

open DkMath.Kernel

/--
A finite real-valued sub-Markov shadow over a state space.

This is only a naming layer over state-indexed `RealWeightProvider`s: it records
the finite outgoing channels and their nonnegative real weights before any full
Markov equality route is imposed.
-/
structure SubMarkovShadow (σ ι : Type _) where
  index : σ → Finset ι
  weight : σ → ι → ℝ
  weight_nonneg : ∀ s i, i ∈ index s → 0 ≤ weight s i

namespace SubMarkovShadow

/-- The real-weight provider emitted by a sub-Markov shadow at state `s`. -/
def providerAt
    {σ ι : Type _}
    (S : SubMarkovShadow σ ι) (s : σ) :
    RealWeightProvider ι where
  index := S.index s
  weight := S.weight s
  weight_nonneg := S.weight_nonneg s

@[simp] theorem providerAt_index
    {σ ι : Type _}
    (S : SubMarkovShadow σ ι) (s : σ) :
    (S.providerAt s).index = S.index s :=
  rfl

@[simp] theorem providerAt_weight
    {σ ι : Type _}
    (S : SubMarkovShadow σ ι) (s : σ) :
    (S.providerAt s).weight = S.weight s :=
  rfl

/-- Total outgoing shadow weight at a state. -/
def totalWeightAt
    {σ ι : Type _}
    (S : SubMarkovShadow σ ι) (s : σ) : ℝ :=
  (S.providerAt s).totalWeight

/-- A sub-Markov shadow is sub-probability normalized at every state. -/
def SubProbability
    {σ ι : Type _}
    (S : SubMarkovShadow σ ι) : Prop :=
  ∀ s, (S.providerAt s).SubProbability

/-- Sub-probability shadows emit sub-probability providers. -/
theorem providerAt_subProbability
    {σ ι : Type _}
    (S : SubMarkovShadow σ ι) (hS : S.SubProbability) (s : σ) :
    (S.providerAt s).SubProbability :=
  hS s

/-- Statewise total outgoing shadow mass is at most one. -/
theorem totalWeightAt_le_one
    {σ ι : Type _}
    (S : SubMarkovShadow σ ι) (hS : S.SubProbability) (s : σ) :
    S.totalWeightAt s ≤ 1 :=
  hS s

/--
Positive-capacity normalization of a capacity kernel as a sub-Markov shadow.
-/
noncomputable def ofCapacityKernel
    {σ ι : Type _}
    (K : CapacityKernel σ ι)
    (hcap : ∀ s, 0 < K.capacity s) :
    SubMarkovShadow σ ι where
  index := K.children
  weight := K.normalizedWeight
  weight_nonneg := by
    intro s i hi
    exact K.normalizedWeight_nonneg s i hi (hcap s)

@[simp] theorem ofCapacityKernel_index
    {σ ι : Type _}
    (K : CapacityKernel σ ι)
    (hcap : ∀ s, 0 < K.capacity s) :
    (ofCapacityKernel K hcap).index = K.children :=
  rfl

@[simp] theorem ofCapacityKernel_weight
    {σ ι : Type _}
    (K : CapacityKernel σ ι)
    (hcap : ∀ s, 0 < K.capacity s) :
    (ofCapacityKernel K hcap).weight = K.normalizedWeight :=
  rfl

/-- Capacity-kernel normalization is sub-Markov normalized at every state. -/
theorem ofCapacityKernel_subProbability
    {σ ι : Type _}
    (K : CapacityKernel σ ι)
    (hcap : ∀ s, 0 < K.capacity s) :
    (ofCapacityKernel K hcap).SubProbability := by
  intro s
  exact K.normalizedRealWeightProvider_subProbability s (hcap s)

end SubMarkovShadow

end DkMath.NumberTheory.PrimitiveSet
