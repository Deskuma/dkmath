/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PrimitiveSet.FiniteTransitionKernel
import DkMath.NumberTheory.PrimitiveSet.PrimeDescent

#print "file: DkMath.NumberTheory.PrimitiveSet.DivisorTransitionKernel"

namespace DkMath.NumberTheory.PrimitiveSet

/-- A natural-number label is a positive power of a prime. -/
def IsPrimePowerLabel (q : ℕ) : Prop :=
  ∃ p k, Nat.Prime p ∧ 0 < k ∧ q = p ^ k

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

/-- All labels available at state `n` are prime-power labels. -/
def PrimePowerIndexOn (T : DivisorTransitionKernel) (n : ℕ) : Prop :=
  ∀ q ∈ T.index n, IsPrimePowerLabel q

/-- Every state of the divisor transition kernel has only prime-power labels. -/
def PrimePowerIndexed (T : DivisorTransitionKernel) : Prop :=
  ∀ n, T.PrimePowerIndexOn n

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

/--
A divisor transition whose label is prime is exactly a one-step prime descent
from the source to the recorded next state.
-/
theorem primeDescentStep_of_prime_label
    (T : DivisorTransitionKernel) {n q : ℕ}
    (hqmem : q ∈ T.index n)
    (hqprime : Nat.Prime q) :
    PrimeDescentStep n (T.next n q) := by
  exact ⟨q, hqprime, T.index_dvd_source hqmem,
    T.next_eq_div_of_mem hqmem⟩

/--
A divisor transition whose label is a positive prime power is a one-step
prime-power descent from the source to the recorded next state.
-/
theorem primePowerDescentStep_of_primePow_label
    (T : DivisorTransitionKernel) {n q p k : ℕ}
    (hqmem : q ∈ T.index n)
    (hp : Nat.Prime p)
    (hk : 0 < k)
    (hq : q = p ^ k) :
    PrimePowerDescentStep n (T.next n q) := by
  refine ⟨p, k, hp, hk, ?_, ?_⟩
  · simpa [← hq] using T.index_dvd_source hqmem
  · simpa [hq] using T.next_eq_div_of_mem hqmem

/--
A divisor transition whose label satisfies the prime-power label predicate is a
one-step prime-power descent.
-/
theorem primePowerDescentStep_of_isPrimePowerLabel
    (T : DivisorTransitionKernel) {n q : ℕ}
    (hqmem : q ∈ T.index n)
    (hqpp : IsPrimePowerLabel q) :
    PrimePowerDescentStep n (T.next n q) := by
  rcases hqpp with ⟨p, k, hp, hk, hq⟩
  exact T.primePowerDescentStep_of_primePow_label hqmem hp hk hq

/--
If all labels at state `n` are prime-power labels, every indexed transition
from `n` is a prime-power descent step.
-/
theorem primePowerDescentStep_of_primePowerIndexOn
    (T : DivisorTransitionKernel) {n q : ℕ}
    (hT : T.PrimePowerIndexOn n)
    (hqmem : q ∈ T.index n) :
    PrimePowerDescentStep n (T.next n q) :=
  T.primePowerDescentStep_of_isPrimePowerLabel hqmem (hT q hqmem)

/--
If all states have prime-power labels, every indexed transition is a
prime-power descent step.
-/
theorem primePowerDescentStep_of_primePowerIndexed
    (T : DivisorTransitionKernel) (hT : T.PrimePowerIndexed)
    {n q : ℕ} (hqmem : q ∈ T.index n) :
    PrimePowerDescentStep n (T.next n q) :=
  T.primePowerDescentStep_of_primePowerIndexOn (hT n) hqmem

end DivisorTransitionKernel

/--
A divisor transition kernel whose labels are all prime powers.

This packages the channel-selection condition needed before adding any
von-Mangoldt-style weight formula.
-/
structure PrimePowerDivisorTransitionKernel where
  toDivisorTransitionKernel : DivisorTransitionKernel
  primePowerIndexed : toDivisorTransitionKernel.PrimePowerIndexed

namespace PrimePowerDivisorTransitionKernel

/-- Forget prime-power channel information and keep the finite transition. -/
def toFiniteTransitionKernel
    (T : PrimePowerDivisorTransitionKernel) :
    FiniteTransitionKernel ℕ ℕ :=
  T.toDivisorTransitionKernel.toFiniteTransitionKernel

/-- The finite weight provider emitted at state `n`. -/
def providerAt (T : PrimePowerDivisorTransitionKernel) (n : ℕ) :
    WeightProvider ℕ :=
  T.toDivisorTransitionKernel.providerAt n

/--
The prime-power channel weight provider emitted at state `n`.

This is currently the packaged kernel provider.  The dedicated name gives the
later von-Mangoldt-like channel a stable theorem-facing entry point.
-/
def channelProviderAt (T : PrimePowerDivisorTransitionKernel) (n : ℕ) :
    WeightProvider ℕ :=
  T.providerAt n

/-- Total transition weight at state `n`. -/
def totalWeightAt (T : PrimePowerDivisorTransitionKernel) (n : ℕ) : ℚ :=
  T.toDivisorTransitionKernel.totalWeightAt n

/-- The packaged prime-power divisor transition kernel is sub-probability. -/
def SubProbability (T : PrimePowerDivisorTransitionKernel) : Prop :=
  T.toDivisorTransitionKernel.SubProbability

/-- Compatibility with a source-controlled family at state `n`. -/
def CompatibleAt
    {M : DkMath.CosmicFormula.Mass.MassSpace ℕ}
    (T : PrimePowerDivisorTransitionKernel) (n : ℕ)
    (F : SourceControlledChainFamily M ℕ) : Prop :=
  T.toDivisorTransitionKernel.CompatibleAt n F

/-- Expanded form of packaged prime-power compatibility. -/
theorem compatibleAt_iff_index_eq
    {M : DkMath.CosmicFormula.Mass.MassSpace ℕ}
    (T : PrimePowerDivisorTransitionKernel) (n : ℕ)
    (F : SourceControlledChainFamily M ℕ) :
    T.CompatibleAt n F ↔ T.toDivisorTransitionKernel.index n = F.index := by
  rfl

/-- Sub-probability packaged kernels emit sub-probability providers. -/
theorem providerAt_subProbability
    (T : PrimePowerDivisorTransitionKernel) (hT : T.SubProbability) (n : ℕ) :
    (T.providerAt n).SubProbability :=
  T.toFiniteTransitionKernel.providerAt_subProbability hT n

/-- Sub-probability packaged kernels emit sub-probability channel providers. -/
theorem channelProviderAt_subProbability
    (T : PrimePowerDivisorTransitionKernel) (hT : T.SubProbability) (n : ℕ) :
    (T.channelProviderAt n).SubProbability :=
  T.providerAt_subProbability hT n

/-- Apply packaged prime-power transition weights at state `n` to a family. -/
def applyAtToSourceControlled
    {M : DkMath.CosmicFormula.Mass.MassSpace ℕ}
    (T : PrimePowerDivisorTransitionKernel) (n : ℕ)
    (F : SourceControlledChainFamily M ℕ)
    (hcompat : T.CompatibleAt n F) :
    WeightedPathFamily M ℕ :=
  T.toFiniteTransitionKernel.applyAtToSourceControlled n F hcompat

/--
Every indexed transition in a packaged prime-power divisor kernel is a
prime-power descent step.
-/
theorem primePowerDescentStep_of_mem
    (T : PrimePowerDivisorTransitionKernel) {n q : ℕ}
    (hqmem : q ∈ T.toDivisorTransitionKernel.index n) :
    PrimePowerDescentStep n (T.toDivisorTransitionKernel.next n q) :=
  T.toDivisorTransitionKernel.primePowerDescentStep_of_primePowerIndexed
    T.primePowerIndexed hqmem

/--
Packaged prime-power transition finite hit mass bound under sub-probability
normalization and a uniform source-mass bound.
-/
theorem weightedHitMass_le_const_of_subprob_applyAtToSourceControlled
    {M : DkMath.CosmicFormula.Mass.MassSpace ℕ} {S : Finset ℕ}
    (T : PrimePowerDivisorTransitionKernel) (hT : T.SubProbability) (n : ℕ)
    (F : SourceControlledChainFamily M ℕ)
    (hcompat : T.CompatibleAt n F)
    (hS : PrimitiveOn S) {C : ℚ} (hC : 0 ≤ C)
    (hsource : ∀ q ∈ F.index, M.μ (F.source q) ≤ C) :
    (T.applyAtToSourceControlled n F hcompat).weightedHitMass S ≤ C := by
  exact T.toFiniteTransitionKernel
    |>.weightedHitMass_le_const_of_subprob_applyAtToSourceControlled
      hT n F hcompat hS hC hsource

/--
Channel-named alias for the packaged prime-power weighted hit mass bound.
-/
theorem channelWeightedHitMass_le_const_of_subprob
    {M : DkMath.CosmicFormula.Mass.MassSpace ℕ} {S : Finset ℕ}
    (T : PrimePowerDivisorTransitionKernel) (hT : T.SubProbability) (n : ℕ)
    (F : SourceControlledChainFamily M ℕ)
    (hcompat : T.CompatibleAt n F)
    (hS : PrimitiveOn S) {C : ℚ} (hC : 0 ≤ C)
    (hsource : ∀ q ∈ F.index, M.μ (F.source q) ≤ C) :
    (T.applyAtToSourceControlled n F hcompat).weightedHitMass S ≤ C :=
  T.weightedHitMass_le_const_of_subprob_applyAtToSourceControlled
    hT n F hcompat hS hC hsource

/--
Replace the weights of a prime-power divisor transition kernel while preserving
its index, next-state map, divisor semantics, and prime-power channel condition.
-/
def withWeight
    (T : PrimePowerDivisorTransitionKernel)
    (w : ℕ → ℕ → ℚ)
    (hw : ∀ n q, q ∈ T.toDivisorTransitionKernel.index n → 0 ≤ w n q) :
    PrimePowerDivisorTransitionKernel where
  toDivisorTransitionKernel :=
    { index := T.toDivisorTransitionKernel.index
      next := T.toDivisorTransitionKernel.next
      weight := w
      weight_nonneg := hw
      index_dvd := T.toDivisorTransitionKernel.index_dvd
      next_eq_div := T.toDivisorTransitionKernel.next_eq_div }
  primePowerIndexed := by
    intro n q hq
    exact T.primePowerIndexed n q hq

@[simp] theorem withWeight_index
    (T : PrimePowerDivisorTransitionKernel)
    (w : ℕ → ℕ → ℚ)
    (hw : ∀ n q, q ∈ T.toDivisorTransitionKernel.index n → 0 ≤ w n q) :
    (T.withWeight w hw).toDivisorTransitionKernel.index =
      T.toDivisorTransitionKernel.index := rfl

@[simp] theorem withWeight_next
    (T : PrimePowerDivisorTransitionKernel)
    (w : ℕ → ℕ → ℚ)
    (hw : ∀ n q, q ∈ T.toDivisorTransitionKernel.index n → 0 ≤ w n q) :
    (T.withWeight w hw).toDivisorTransitionKernel.next =
      T.toDivisorTransitionKernel.next := rfl

@[simp] theorem withWeight_weight
    (T : PrimePowerDivisorTransitionKernel)
    (w : ℕ → ℕ → ℚ)
    (hw : ∀ n q, q ∈ T.toDivisorTransitionKernel.index n → 0 ≤ w n q) :
    (T.withWeight w hw).toDivisorTransitionKernel.weight = w := rfl

end PrimePowerDivisorTransitionKernel

/--
A packaged prime-power channel provider: a prime-power divisor transition kernel
together with sub-probability normalization.
-/
structure PrimePowerChannelProvider where
  kernel : PrimePowerDivisorTransitionKernel
  subprob : kernel.SubProbability

namespace PrimePowerChannelProvider

/-- Package a prime-power divisor transition kernel with a sub-probability proof. -/
def ofKernel
    (T : PrimePowerDivisorTransitionKernel) (hT : T.SubProbability) :
    PrimePowerChannelProvider where
  kernel := T
  subprob := hT

/-- The prime-power channel provider emitted at state `n`. -/
def providerAt (P : PrimePowerChannelProvider) (n : ℕ) : WeightProvider ℕ :=
  P.kernel.channelProviderAt n

/-- Alias matching the kernel-level channel-provider name. -/
def channelProviderAt (P : PrimePowerChannelProvider) (n : ℕ) :
    WeightProvider ℕ :=
  P.providerAt n

/-- Packaged channel providers emit sub-probability providers at every state. -/
theorem providerAt_subProbability (P : PrimePowerChannelProvider) (n : ℕ) :
    (P.providerAt n).SubProbability :=
  P.kernel.channelProviderAt_subProbability P.subprob n

/-- The channel-provider alias is sub-probability at every state. -/
theorem channelProviderAt_subProbability
    (P : PrimePowerChannelProvider) (n : ℕ) :
    (P.channelProviderAt n).SubProbability :=
  P.providerAt_subProbability n

/-- Apply the packaged channel weights at state `n` to a source-controlled family. -/
def applyAtToSourceControlled
    {M : DkMath.CosmicFormula.Mass.MassSpace ℕ}
    (P : PrimePowerChannelProvider) (n : ℕ)
    (F : SourceControlledChainFamily M ℕ)
    (hcompat : P.kernel.CompatibleAt n F) :
    WeightedPathFamily M ℕ :=
  P.kernel.applyAtToSourceControlled n F hcompat

/--
Packaged channel hit mass bound.  The sub-probability hypothesis is carried by
the provider package.
-/
theorem weightedHitMass_le_const_applyAtToSourceControlled
    {M : DkMath.CosmicFormula.Mass.MassSpace ℕ} {S : Finset ℕ}
    (P : PrimePowerChannelProvider) (n : ℕ)
    (F : SourceControlledChainFamily M ℕ)
    (hcompat : P.kernel.CompatibleAt n F)
    (hS : PrimitiveOn S) {C : ℚ} (hC : 0 ≤ C)
    (hsource : ∀ q ∈ F.index, M.μ (F.source q) ≤ C) :
    (P.applyAtToSourceControlled n F hcompat).weightedHitMass S ≤ C :=
  P.kernel.channelWeightedHitMass_le_const_of_subprob
    P.subprob n F hcompat hS hC hsource

end PrimePowerChannelProvider

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

/-- The sample label `2` is a prime-power label. -/
theorem sampleTenDivisorTransitionKernel_isPrimePowerLabel_two :
    IsPrimePowerLabel 2 := by
  exact ⟨2, 1, by norm_num, by norm_num, by norm_num⟩

/-- The sample label `5` is a prime-power label. -/
theorem sampleTenDivisorTransitionKernel_isPrimePowerLabel_five :
    IsPrimePowerLabel 5 := by
  exact ⟨5, 1, by norm_num, by norm_num, by norm_num⟩

/-- At state `10`, all sample labels are prime-power labels. -/
theorem sampleTenDivisorTransitionKernel_primePowerIndexOn_ten :
    sampleTenDivisorTransitionKernel.PrimePowerIndexOn 10 := by
  intro q hq
  simp only [sampleTenDivisorTransitionKernel_index_ten, Finset.mem_insert,
    Finset.mem_singleton] at hq
  rcases hq with rfl | rfl
  · exact sampleTenDivisorTransitionKernel_isPrimePowerLabel_two
  · exact sampleTenDivisorTransitionKernel_isPrimePowerLabel_five

/-- Every state of the sample kernel has only prime-power labels. -/
theorem sampleTenDivisorTransitionKernel_primePowerIndexed :
    sampleTenDivisorTransitionKernel.PrimePowerIndexed := by
  intro n q hq
  by_cases hn : n = 10
  · subst n
    exact sampleTenDivisorTransitionKernel_primePowerIndexOn_ten q hq
  · simp [sampleTenDivisorTransitionKernel, hn] at hq

/-- The sample packaged as a prime-power divisor transition kernel. -/
def sampleTenPrimePowerDivisorTransitionKernel :
    PrimePowerDivisorTransitionKernel where
  toDivisorTransitionKernel := sampleTenDivisorTransitionKernel
  primePowerIndexed := sampleTenDivisorTransitionKernel_primePowerIndexed

/-- The sample transition label `2` is a prime descent step from `10` to `5`. -/
theorem sampleTenDivisorTransitionKernel_primeDescentStep_two :
    PrimeDescentStep 10 (sampleTenDivisorTransitionKernel.next 10 2) := by
  exact sampleTenDivisorTransitionKernel.primeDescentStep_of_prime_label
    (by simp [sampleTenDivisorTransitionKernel]) (by norm_num)

/-- The sample transition label `5` is a prime descent step from `10` to `2`. -/
theorem sampleTenDivisorTransitionKernel_primeDescentStep_five :
    PrimeDescentStep 10 (sampleTenDivisorTransitionKernel.next 10 5) := by
  exact sampleTenDivisorTransitionKernel.primeDescentStep_of_prime_label
    (by simp [sampleTenDivisorTransitionKernel]) (by norm_num)

/-- The sample transition label `2 = 2 ^ 1` is a prime-power descent step. -/
theorem sampleTenDivisorTransitionKernel_primePowerDescentStep_two :
    PrimePowerDescentStep 10 (sampleTenDivisorTransitionKernel.next 10 2) := by
  exact sampleTenPrimePowerDivisorTransitionKernel.primePowerDescentStep_of_mem
    (by simp [sampleTenPrimePowerDivisorTransitionKernel,
      sampleTenDivisorTransitionKernel])

/-- The sample transition label `5 = 5 ^ 1` is a prime-power descent step. -/
theorem sampleTenDivisorTransitionKernel_primePowerDescentStep_five :
    PrimePowerDescentStep 10 (sampleTenDivisorTransitionKernel.next 10 5) := by
  exact sampleTenPrimePowerDivisorTransitionKernel.primePowerDescentStep_of_mem
    (by simp [sampleTenPrimePowerDivisorTransitionKernel,
      sampleTenDivisorTransitionKernel])

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

/-- The packaged prime-power sample is sub-probability normalized. -/
theorem sampleTenPrimePowerDivisorTransitionKernel_subProbability :
    sampleTenPrimePowerDivisorTransitionKernel.SubProbability :=
  sampleTenDivisorTransitionKernel_subProbability

/-- The sample packaged as a prime-power channel provider. -/
def sampleTenPrimePowerChannelProvider : PrimePowerChannelProvider :=
  PrimePowerChannelProvider.ofKernel
    sampleTenPrimePowerDivisorTransitionKernel
    sampleTenPrimePowerDivisorTransitionKernel_subProbability

/-- The packaged prime-power sample emits sub-probability channel providers. -/
theorem sampleTenPrimePowerDivisorTransitionKernel_channelProviderAt_subProbability
    (n : ℕ) :
    (sampleTenPrimePowerDivisorTransitionKernel.channelProviderAt n).SubProbability :=
  sampleTenPrimePowerDivisorTransitionKernel.channelProviderAt_subProbability
    sampleTenPrimePowerDivisorTransitionKernel_subProbability n

/-- The sample channel-provider package emits sub-probability providers. -/
theorem sampleTenPrimePowerChannelProvider_channelProviderAt_subProbability
    (n : ℕ) :
    (sampleTenPrimePowerChannelProvider.channelProviderAt n).SubProbability :=
  sampleTenPrimePowerChannelProvider.channelProviderAt_subProbability n

/--
A finite toy channel weight on the sample: at state `10`, label `2` has weight
`1` and label `5` has weight `0`.
-/
def sampleTenToyWeight (n q : ℕ) : ℚ :=
  if n = 10 ∧ q = 2 then 1 else 0

/-- The sample toy weight is nonnegative on the sample channel index. -/
theorem sampleTenToyWeight_nonneg :
    ∀ n q,
      q ∈ sampleTenPrimePowerDivisorTransitionKernel.toDivisorTransitionKernel.index n →
        0 ≤ sampleTenToyWeight n q := by
  intro n q _hq
  by_cases h : n = 10 ∧ q = 2
  · simp [sampleTenToyWeight, h]
  · simp [sampleTenToyWeight, h]

/-- The sample prime-power kernel with its weights replaced by toy weights. -/
def sampleTenToyWeightKernel : PrimePowerDivisorTransitionKernel :=
  sampleTenPrimePowerDivisorTransitionKernel.withWeight
    sampleTenToyWeight sampleTenToyWeight_nonneg

@[simp] theorem sampleTenToyWeightKernel_index_ten :
    sampleTenToyWeightKernel.toDivisorTransitionKernel.index 10 =
      ({2, 5} : Finset ℕ) := by
  simp [sampleTenToyWeightKernel, sampleTenPrimePowerDivisorTransitionKernel]

/-- The toy-weighted sample keeps the original `10 -> 5` transition by label `2`. -/
theorem sampleTenToyWeightKernel_next_two :
    sampleTenToyWeightKernel.toDivisorTransitionKernel.next 10 2 = 5 := by
  norm_num [sampleTenToyWeightKernel, sampleTenPrimePowerDivisorTransitionKernel,
    sampleTenDivisorTransitionKernel]

/-- The toy-weighted sample keeps the original `10 -> 2` transition by label `5`. -/
theorem sampleTenToyWeightKernel_next_five :
    sampleTenToyWeightKernel.toDivisorTransitionKernel.next 10 5 = 2 := by
  norm_num [sampleTenToyWeightKernel, sampleTenPrimePowerDivisorTransitionKernel,
    sampleTenDivisorTransitionKernel]

/-- The toy-weighted sample is sub-probability normalized. -/
theorem sampleTenToyWeightKernel_subProbability :
    sampleTenToyWeightKernel.SubProbability := by
  intro n
  by_cases hn : n = 10
  · subst n
    norm_num [PrimePowerDivisorTransitionKernel.SubProbability,
      PrimePowerDivisorTransitionKernel.withWeight,
      DivisorTransitionKernel.SubProbability,
      DivisorTransitionKernel.toFiniteTransitionKernel,
      FiniteTransitionKernel.SubProbability,
      FiniteTransitionKernel.toFiniteKernel,
      FiniteKernel.providerAt,
      WeightProvider.SubProbability,
      WeightProvider.totalWeight,
      sampleTenPrimePowerDivisorTransitionKernel,
      sampleTenDivisorTransitionKernel,
      sampleTenToyWeightKernel,
      sampleTenToyWeight]
  · simp [PrimePowerDivisorTransitionKernel.withWeight,
      DivisorTransitionKernel.toFiniteTransitionKernel,
      FiniteTransitionKernel.toFiniteKernel,
      FiniteKernel.providerAt,
      WeightProvider.SubProbability,
      WeightProvider.totalWeight,
      sampleTenPrimePowerDivisorTransitionKernel,
      sampleTenDivisorTransitionKernel,
      sampleTenToyWeightKernel,
      sampleTenToyWeight, hn]

/-- The toy-weighted sample packaged as a prime-power channel provider. -/
def sampleTenToyWeightChannelProvider : PrimePowerChannelProvider :=
  PrimePowerChannelProvider.ofKernel
    sampleTenToyWeightKernel sampleTenToyWeightKernel_subProbability

/-- The toy-weighted channel provider emits sub-probability providers. -/
theorem sampleTenToyWeightChannelProvider_channelProviderAt_subProbability
    (n : ℕ) :
    (sampleTenToyWeightChannelProvider.channelProviderAt n).SubProbability :=
  sampleTenToyWeightChannelProvider.channelProviderAt_subProbability n

/--
A source-controlled family whose index matches the toy-weighted sample channel
at state `10`.
-/
def sampleTenToyWeightSourceControlledFamily :
    SourceControlledChainFamily unitNatMassSpace ℕ where
  index := ({2, 5} : Finset ℕ)
  chain := fun q => ({q} : Finset ℕ)
  chain_is_chain := by
    intro q _hq a b ha hb
    simp only [Finset.mem_singleton] at ha hb
    subst a
    subst b
    exact Or.inl dvd_rfl
  source := fun _ => 10
  mass_le_source := by
    intro _q _hq _h _hh
    rfl

/--
The toy-weighted sample channel provider gives a concrete weighted hit mass
bound by `1`.
-/
theorem sampleTenToyWeightChannelProvider_hitMass_le_one :
    (sampleTenToyWeightChannelProvider.applyAtToSourceControlled 10
      sampleTenToyWeightSourceControlledFamily
      (by
        change sampleTenToyWeightKernel.toDivisorTransitionKernel.index 10 =
          sampleTenToyWeightSourceControlledFamily.index
        simp [sampleTenToyWeightSourceControlledFamily])).weightedHitMass
      ({2, 5} : Finset ℕ) ≤ 1 := by
  exact sampleTenToyWeightChannelProvider
    |>.weightedHitMass_le_const_applyAtToSourceControlled 10
      sampleTenToyWeightSourceControlledFamily
      (by
        change sampleTenToyWeightKernel.toDivisorTransitionKernel.index 10 =
          sampleTenToyWeightSourceControlledFamily.index
        simp [sampleTenToyWeightSourceControlledFamily])
      (primitiveOn_pair (by norm_num) (by norm_num))
      (by norm_num)
      (by
        intro _q _hq
        rfl)

end DkMath.NumberTheory.PrimitiveSet
