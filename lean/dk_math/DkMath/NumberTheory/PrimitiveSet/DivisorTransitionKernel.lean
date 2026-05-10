/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PrimitiveSet.FiniteTransitionKernel

#print "file: DkMath.NumberTheory.PrimitiveSet.DivisorTransitionKernel"

namespace DkMath.NumberTheory.PrimitiveSet

/--
A finite transition kernel whose states and labels are natural numbers and whose
transitions are divisor removal steps `n -> n / q`.

This is still an algebraic finite skeleton: the index set chooses finite divisor
labels and the weight is only required to be nonnegative.  No analytic formula
such as von Mangoldt over logarithms is imposed here.
-/
structure DivisorTransitionKernel where
  index : ℕ → Finset ℕ
  next : ℕ → ℕ → ℕ
  weight : ℕ → ℕ → ℚ
  weight_nonneg : ∀ n q, q ∈ index n → 0 ≤ weight n q
  index_dvd : ∀ n q, q ∈ index n → q ∣ n
  next_eq_div : ∀ n q, q ∈ index n → next n q = n / q

namespace DivisorTransitionKernel

/-- Forget divisor semantics and keep the finite transition kernel. -/
def toFiniteTransitionKernel
    (T : DivisorTransitionKernel) :
    FiniteTransitionKernel ℕ ℕ where
  index := T.index
  next := T.next
  weight := T.weight
  weight_nonneg := T.weight_nonneg

@[simp] theorem toFiniteTransitionKernel_index
    (T : DivisorTransitionKernel) :
    T.toFiniteTransitionKernel.index = T.index := rfl

@[simp] theorem toFiniteTransitionKernel_next
    (T : DivisorTransitionKernel) :
    T.toFiniteTransitionKernel.next = T.next := rfl

@[simp] theorem toFiniteTransitionKernel_weight
    (T : DivisorTransitionKernel) :
    T.toFiniteTransitionKernel.weight = T.weight := rfl

/-- The finite weight provider emitted at state `n`. -/
def providerAt (T : DivisorTransitionKernel) (n : ℕ) : WeightProvider ℕ :=
  T.toFiniteTransitionKernel.providerAt n

/-- Total divisor-transition weight at state `n`. -/
def totalWeightAt (T : DivisorTransitionKernel) (n : ℕ) : ℚ :=
  T.toFiniteTransitionKernel.totalWeightAt n

/-- The divisor transition kernel is sub-probability normalized at every state. -/
def SubProbability (T : DivisorTransitionKernel) : Prop :=
  T.toFiniteTransitionKernel.SubProbability

/-- Compatibility with a source-controlled family at state `n`. -/
def CompatibleAt
    {M : DkMath.CosmicFormula.Mass.MassSpace ℕ}
    (T : DivisorTransitionKernel) (n : ℕ)
    (F : SourceControlledChainFamily M ℕ) : Prop :=
  T.toFiniteTransitionKernel.CompatibleAt n F

/-- Expanded form of divisor-transition compatibility. -/
theorem compatibleAt_iff_index_eq
    {M : DkMath.CosmicFormula.Mass.MassSpace ℕ}
    (T : DivisorTransitionKernel) (n : ℕ)
    (F : SourceControlledChainFamily M ℕ) :
    T.CompatibleAt n F ↔ T.index n = F.index := by
  rfl

/-- Membership in the transition index supplies the divisor removed from `n`. -/
theorem index_dvd_source
    (T : DivisorTransitionKernel) {n q : ℕ}
    (hq : q ∈ T.index n) :
    q ∣ n :=
  T.index_dvd n q hq

/-- A divisor transition step has the recorded quotient target. -/
theorem next_eq_div_of_mem
    (T : DivisorTransitionKernel) {n q : ℕ}
    (hq : q ∈ T.index n) :
    T.next n q = n / q :=
  T.next_eq_div n q hq

/-- The next state of a divisor transition is itself a divisor of the source. -/
theorem next_dvd_source
    (T : DivisorTransitionKernel) {n q : ℕ}
    (hq : q ∈ T.index n) :
    T.next n q ∣ n := by
  rw [T.next_eq_div_of_mem hq]
  exact Nat.div_dvd_of_dvd (T.index_dvd_source hq)

end DivisorTransitionKernel

/-- A concrete divisor-transition sample at state `10` with labels `2` and `5`. -/
def sampleTenDivisorTransitionKernel : DivisorTransitionKernel where
  index := fun n => if n = 10 then ({2, 5} : Finset ℕ) else ∅
  next := fun n q => n / q
  weight := fun n q => if n = 10 ∧ (q = 2 ∨ q = 5) then (1 / 2 : ℚ) else 0
  weight_nonneg := by
    intro n q _hq
    by_cases h : n = 10 ∧ (q = 2 ∨ q = 5)
    · simp [h]
    · simp [h]
  index_dvd := by
    intro n q hq
    by_cases hn : n = 10
    · subst n
      simp only [if_true, Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl <;> norm_num
    · simp [hn] at hq
  next_eq_div := by
    intro n q _hq
    rfl

@[simp] theorem sampleTenDivisorTransitionKernel_index_ten :
    sampleTenDivisorTransitionKernel.index 10 = ({2, 5} : Finset ℕ) := by
  simp [sampleTenDivisorTransitionKernel]

/-- In the sample, the transition label `2` sends `10` to `5`. -/
theorem sampleTenDivisorTransitionKernel_next_two :
    sampleTenDivisorTransitionKernel.next 10 2 = 5 := by
  norm_num [sampleTenDivisorTransitionKernel]

/-- In the sample, the transition label `5` sends `10` to `2`. -/
theorem sampleTenDivisorTransitionKernel_next_five :
    sampleTenDivisorTransitionKernel.next 10 5 = 2 := by
  norm_num [sampleTenDivisorTransitionKernel]

/-- The sample divisor-transition kernel is sub-probability normalized. -/
theorem sampleTenDivisorTransitionKernel_subProbability :
    sampleTenDivisorTransitionKernel.SubProbability := by
  intro n
  by_cases hn : n = 10
  · subst n
    norm_num [DivisorTransitionKernel.SubProbability,
      DivisorTransitionKernel.toFiniteTransitionKernel,
      FiniteTransitionKernel.SubProbability,
      FiniteTransitionKernel.toFiniteKernel,
      FiniteKernel.providerAt,
      WeightProvider.SubProbability,
      WeightProvider.totalWeight,
      sampleTenDivisorTransitionKernel]
  · simp [DivisorTransitionKernel.toFiniteTransitionKernel,
      FiniteTransitionKernel.toFiniteKernel,
      FiniteKernel.providerAt,
      WeightProvider.SubProbability,
      WeightProvider.totalWeight,
      sampleTenDivisorTransitionKernel, hn]

end DkMath.NumberTheory.PrimitiveSet
