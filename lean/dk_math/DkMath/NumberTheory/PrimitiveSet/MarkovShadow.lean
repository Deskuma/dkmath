/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PrimitiveSet.SubMarkovShadow

#print "file: DkMath.NumberTheory.PrimitiveSet.MarkovShadow"

namespace DkMath.NumberTheory.PrimitiveSet

open DkMath.Kernel

/--
A finite real-valued Markov shadow over a state space.

This is the equality counterpart of `SubMarkovShadow`: every state emits a
finite real provider whose total outgoing weight is exactly one.
-/
structure MarkovShadow (σ ι : Type _) where
  toSubMarkovShadow : SubMarkovShadow σ ι
  totalWeightAt_eq_one :
    ∀ s, toSubMarkovShadow.totalWeightAt s = 1

namespace MarkovShadow

/-- The real-weight provider emitted by a Markov shadow at state `s`. -/
def providerAt
    {σ ι : Type _}
    (M : MarkovShadow σ ι) (s : σ) :
    RealWeightProvider ι :=
  M.toSubMarkovShadow.providerAt s

/-- The finite outgoing channel set at a state. -/
def index
    {σ ι : Type _}
    (M : MarkovShadow σ ι) (s : σ) :
    Finset ι :=
  M.toSubMarkovShadow.index s

/-- The outgoing channel weight at a state. -/
def weight
    {σ ι : Type _}
    (M : MarkovShadow σ ι) (s : σ) (i : ι) : ℝ :=
  M.toSubMarkovShadow.weight s i

@[simp] theorem providerAt_index
    {σ ι : Type _}
    (M : MarkovShadow σ ι) (s : σ) :
    (M.providerAt s).index = M.index s :=
  rfl

@[simp] theorem providerAt_weight
    {σ ι : Type _}
    (M : MarkovShadow σ ι) (s : σ) :
    (M.providerAt s).weight = M.weight s :=
  rfl

/-- Markov shadows are sub-probability shadows after forgetting equality. -/
theorem subProbability
    {σ ι : Type _}
    (M : MarkovShadow σ ι) :
    M.toSubMarkovShadow.SubProbability := by
  intro s
  unfold RealWeightProvider.SubProbability
  exact le_of_eq (M.totalWeightAt_eq_one s)

/-- Markov providers are sub-probability providers after forgetting equality. -/
theorem providerAt_subProbability
    {σ ι : Type _}
    (M : MarkovShadow σ ι) (s : σ) :
    (M.providerAt s).SubProbability :=
  M.subProbability s

/--
Positive-capacity normalization of a capacity kernel with exact outgoing cost
as a Markov shadow.
-/
noncomputable def ofCapacityKernel
    {σ ι : Type _}
    (K : CapacityKernel σ ι)
    (hcap : ∀ s, 0 < K.capacity s)
    (hout : ∀ s, K.outgoingCost s = K.capacity s) :
    MarkovShadow σ ι where
  toSubMarkovShadow := SubMarkovShadow.ofCapacityKernel K hcap
  totalWeightAt_eq_one := by
    intro s
    change K.normalizedOutgoing s = 1
    rw [K.normalizedOutgoing_eq_outgoingCost_div s, hout s]
    exact div_self (ne_of_gt (hcap s))

@[simp] theorem ofCapacityKernel_toSubMarkovShadow
    {σ ι : Type _}
    (K : CapacityKernel σ ι)
    (hcap : ∀ s, 0 < K.capacity s)
    (hout : ∀ s, K.outgoingCost s = K.capacity s) :
    (ofCapacityKernel K hcap hout).toSubMarkovShadow =
      SubMarkovShadow.ofCapacityKernel K hcap :=
  rfl

end MarkovShadow

end DkMath.NumberTheory.PrimitiveSet
