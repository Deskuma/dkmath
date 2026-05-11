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

/-- A natural-number label together with one explicit prime-power witness. -/
structure PrimePowerLabel where
  q : ℕ
  p : ℕ
  k : ℕ
  prime : Nat.Prime p
  k_pos : 0 < k
  eq_pow : q = p ^ k

namespace PrimePowerLabel

/-- Forget the chosen witness and keep only the prime-power predicate. -/
theorem isPrimePowerLabel (L : PrimePowerLabel) :
    IsPrimePowerLabel L.q :=
  ⟨L.p, L.k, L.prime, L.k_pos, L.eq_pow⟩

end PrimePowerLabel

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

namespace PrimePowerLabel

/--
An indexed divisor transition labelled by an explicit prime-power witness is a
prime-power descent step.
-/
theorem primePowerDescentStep_of_mem
    (T : DivisorTransitionKernel) {n : ℕ} (L : PrimePowerLabel)
    (hmem : L.q ∈ T.index n) :
    PrimePowerDescentStep n (T.next n L.q) :=
  T.primePowerDescentStep_of_primePow_label
    hmem L.prime L.k_pos L.eq_pow

end PrimePowerLabel

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

/--
A finite von-Mangoldt-like weight predicate for the current prime-power
channel.

This does not define the analytic von Mangoldt function.  It only records that
each indexed label has a prime-power witness and receives a nonnegative weight.
-/
def VonMangoldtLikeWeight
    (T : PrimePowerDivisorTransitionKernel) (w : ℕ → ℕ → ℚ) : Prop :=
  ∀ n q, q ∈ T.toDivisorTransitionKernel.index n →
    ∃ p k, Nat.Prime p ∧ 0 < k ∧ q = p ^ k ∧ 0 ≤ w n q

/--
A finite toy weight whose value can be expressed through the prime base of a
prime-power witness.

The auxiliary function `c n p` is the finite placeholder for a future
von-Mangoldt-like dependence on the prime base `p`.
-/
def PrimeWitnessDependentWeight
    (T : PrimePowerDivisorTransitionKernel)
    (w : ℕ → ℕ → ℚ) (c : ℕ → ℕ → ℚ) : Prop :=
  ∀ n q, q ∈ T.toDivisorTransitionKernel.index n →
    ∃ p k,
      Nat.Prime p ∧ 0 < k ∧ q = p ^ k ∧
        w n q = c n p ∧ 0 ≤ w n q

/-- A von-Mangoldt-like weight is nonnegative on the channel index. -/
theorem vonMangoldtLikeWeight_nonneg
    (T : PrimePowerDivisorTransitionKernel) {w : ℕ → ℕ → ℚ}
    (hw : T.VonMangoldtLikeWeight w) :
    ∀ n q, q ∈ T.toDivisorTransitionKernel.index n → 0 ≤ w n q := by
  intro n q hq
  rcases hw n q hq with ⟨_p, _k, _hp, _hk, _hqpow, hnq⟩
  exact hnq

/-- A von-Mangoldt-like weight carries prime-power witnesses on the channel index. -/
theorem vonMangoldtLikeWeight_isPrimePowerLabel
    (T : PrimePowerDivisorTransitionKernel) {w : ℕ → ℕ → ℚ}
    (hw : T.VonMangoldtLikeWeight w) :
    ∀ n q, q ∈ T.toDivisorTransitionKernel.index n → IsPrimePowerLabel q := by
  intro n q hq
  rcases hw n q hq with ⟨p, k, hp, hk, hqpow, _hnq⟩
  exact ⟨p, k, hp, hk, hqpow⟩

/--
For a prime-power divisor transition kernel, nonnegative channel weights are
von-Mangoldt-like in the finite predicate sense.
-/
theorem vonMangoldtLikeWeight_of_nonneg
    (T : PrimePowerDivisorTransitionKernel) {w : ℕ → ℕ → ℚ}
    (hw_nonneg :
      ∀ n q, q ∈ T.toDivisorTransitionKernel.index n → 0 ≤ w n q) :
    T.VonMangoldtLikeWeight w := by
  intro n q hq
  rcases T.primePowerIndexed n q hq with ⟨p, k, hp, hk, hqpow⟩
  exact ⟨p, k, hp, hk, hqpow, hw_nonneg n q hq⟩

/--
A prime-witness-dependent toy weight is von-Mangoldt-like in the finite
predicate sense.
-/
theorem vonMangoldtLikeWeight_of_primeWitnessDependent
    (T : PrimePowerDivisorTransitionKernel) {w c : ℕ → ℕ → ℚ}
    (hw : T.PrimeWitnessDependentWeight w c) :
    T.VonMangoldtLikeWeight w := by
  intro n q hq
  rcases hw n q hq with ⟨p, k, hp, hk, hqpow, _hweight, hnq⟩
  exact ⟨p, k, hp, hk, hqpow, hnq⟩

end PrimePowerDivisorTransitionKernel

/--
A choice of explicit prime-power witnesses for every indexed label of a
prime-power divisor transition kernel.
-/
structure PrimePowerWitnessProvider
    (T : PrimePowerDivisorTransitionKernel) where
  label :
    ∀ n q,
      q ∈ T.toDivisorTransitionKernel.index n →
        PrimePowerLabel
  label_q :
    ∀ n q (hq : q ∈ T.toDivisorTransitionKernel.index n),
      (label n q hq).q = q

namespace PrimePowerWitnessProvider

/-- The chosen witness for an indexed label proves that the label is a prime power. -/
theorem isPrimePowerLabel
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T) {n q : ℕ}
    (hq : q ∈ T.toDivisorTransitionKernel.index n) :
    IsPrimePowerLabel q := by
  simpa [W.label_q n q hq] using (W.label n q hq).isPrimePowerLabel

/-- A witness-provider-labelled indexed transition is a prime-power descent step. -/
theorem primePowerDescentStep
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T) {n q : ℕ}
    (hq : q ∈ T.toDivisorTransitionKernel.index n) :
    PrimePowerDescentStep n (T.toDivisorTransitionKernel.next n q) :=
  T.toDivisorTransitionKernel.primePowerDescentStep_of_isPrimePowerLabel
    hq (W.isPrimePowerLabel hq)

/--
Turn a base-prime weight `c n p` into a label weight by reading the chosen
prime-power witness of each indexed label.
-/
def weightOfBase
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (c : ℕ → ℕ → ℚ) :
    ℕ → ℕ → ℚ :=
  fun n q =>
    if hq : q ∈ T.toDivisorTransitionKernel.index n then
      c n ((W.label n q hq).p)
    else
      0

@[simp] theorem weightOfBase_of_mem
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (c : ℕ → ℕ → ℚ) {n q : ℕ}
    (hq : q ∈ T.toDivisorTransitionKernel.index n) :
    W.weightOfBase c n q = c n ((W.label n q hq).p) := by
  simp [weightOfBase, hq]

/--
Weights built from a witness provider and a nonnegative base-prime weight are
prime-witness-dependent weights.
-/
theorem weightOfBase_primeWitnessDependent
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (c : ℕ → ℕ → ℚ)
    (hc_nonneg :
      ∀ n q (hq : q ∈ T.toDivisorTransitionKernel.index n),
        0 ≤ c n ((W.label n q hq).p)) :
    T.PrimeWitnessDependentWeight (W.weightOfBase c) c := by
  intro n q hq
  let L := W.label n q hq
  refine ⟨L.p, L.k, L.prime, L.k_pos, ?_, ?_, ?_⟩
  · exact (W.label_q n q hq).symm.trans L.eq_pow
  · exact W.weightOfBase_of_mem c hq
  · rw [W.weightOfBase_of_mem c hq]
    exact hc_nonneg n q hq

end PrimePowerWitnessProvider

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

@[simp] theorem ofKernel_kernel
    (T : PrimePowerDivisorTransitionKernel) (hT : T.SubProbability) :
    (ofKernel T hT).kernel = T := rfl

/--
Replace a prime-power divisor kernel's weights and immediately package the
result as a sub-probability channel provider.
-/
def ofKernelWithWeight
    (T : PrimePowerDivisorTransitionKernel)
    (w : ℕ → ℕ → ℚ)
    (hw_nonneg :
      ∀ n q, q ∈ T.toDivisorTransitionKernel.index n → 0 ≤ w n q)
    (hw_subprob : (T.withWeight w hw_nonneg).SubProbability) :
    PrimePowerChannelProvider :=
  ofKernel (T.withWeight w hw_nonneg) hw_subprob

/--
Package a finite von-Mangoldt-like weight as a sub-probability channel provider.
-/
def ofVonMangoldtLikeWeight
    (T : PrimePowerDivisorTransitionKernel)
    (w : ℕ → ℕ → ℚ)
    (hw : T.VonMangoldtLikeWeight w)
    (hw_subprob :
      (T.withWeight w (T.vonMangoldtLikeWeight_nonneg hw)).SubProbability) :
    PrimePowerChannelProvider :=
  ofKernelWithWeight T w (T.vonMangoldtLikeWeight_nonneg hw) hw_subprob

/--
Package a prime-witness-dependent toy weight as a sub-probability channel
provider.
-/
def ofPrimeWitnessDependentWeight
    (T : PrimePowerDivisorTransitionKernel)
    (w c : ℕ → ℕ → ℚ)
    (hw : T.PrimeWitnessDependentWeight w c)
    (hw_subprob :
      (T.withWeight w
        (T.vonMangoldtLikeWeight_nonneg
          (T.vonMangoldtLikeWeight_of_primeWitnessDependent hw))).SubProbability) :
    PrimePowerChannelProvider :=
  ofVonMangoldtLikeWeight T w
    (T.vonMangoldtLikeWeight_of_primeWitnessDependent hw) hw_subprob

/--
Package a base-prime weight through a witness provider as a prime-power channel
provider.
-/
def ofWitnessProviderWeight
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (c : ℕ → ℕ → ℚ)
    (hc_nonneg :
      ∀ n q (hq : q ∈ T.toDivisorTransitionKernel.index n),
        0 ≤ c n ((W.label n q hq).p))
    (hw_subprob :
      (T.withWeight (W.weightOfBase c)
        (T.vonMangoldtLikeWeight_nonneg
          (T.vonMangoldtLikeWeight_of_primeWitnessDependent
            (W.weightOfBase_primeWitnessDependent c hc_nonneg)))).SubProbability) :
    PrimePowerChannelProvider :=
  ofPrimeWitnessDependentWeight T (W.weightOfBase c) c
    (W.weightOfBase_primeWitnessDependent c hc_nonneg) hw_subprob

@[simp] theorem ofKernelWithWeight_kernel
    (T : PrimePowerDivisorTransitionKernel)
    (w : ℕ → ℕ → ℚ)
    (hw_nonneg :
      ∀ n q, q ∈ T.toDivisorTransitionKernel.index n → 0 ≤ w n q)
    (hw_subprob : (T.withWeight w hw_nonneg).SubProbability) :
    (ofKernelWithWeight T w hw_nonneg hw_subprob).kernel =
      T.withWeight w hw_nonneg := rfl

@[simp] theorem ofVonMangoldtLikeWeight_kernel
    (T : PrimePowerDivisorTransitionKernel)
    (w : ℕ → ℕ → ℚ)
    (hw : T.VonMangoldtLikeWeight w)
    (hw_subprob :
      (T.withWeight w (T.vonMangoldtLikeWeight_nonneg hw)).SubProbability) :
    (ofVonMangoldtLikeWeight T w hw hw_subprob).kernel =
      T.withWeight w (T.vonMangoldtLikeWeight_nonneg hw) := rfl

@[simp] theorem ofPrimeWitnessDependentWeight_kernel
    (T : PrimePowerDivisorTransitionKernel)
    (w c : ℕ → ℕ → ℚ)
    (hw : T.PrimeWitnessDependentWeight w c)
    (hw_subprob :
      (T.withWeight w
        (T.vonMangoldtLikeWeight_nonneg
          (T.vonMangoldtLikeWeight_of_primeWitnessDependent hw))).SubProbability) :
    (ofPrimeWitnessDependentWeight T w c hw hw_subprob).kernel =
      T.withWeight w
        (T.vonMangoldtLikeWeight_nonneg
          (T.vonMangoldtLikeWeight_of_primeWitnessDependent hw)) := rfl

@[simp] theorem ofWitnessProviderWeight_kernel
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (c : ℕ → ℕ → ℚ)
    (hc_nonneg :
      ∀ n q (hq : q ∈ T.toDivisorTransitionKernel.index n),
        0 ≤ c n ((W.label n q hq).p))
    (hw_subprob :
      (T.withWeight (W.weightOfBase c)
        (T.vonMangoldtLikeWeight_nonneg
          (T.vonMangoldtLikeWeight_of_primeWitnessDependent
            (W.weightOfBase_primeWitnessDependent c hc_nonneg)))).SubProbability) :
    (ofWitnessProviderWeight W c hc_nonneg hw_subprob).kernel =
      T.withWeight (W.weightOfBase c)
        (T.vonMangoldtLikeWeight_nonneg
          (T.vonMangoldtLikeWeight_of_primeWitnessDependent
            (W.weightOfBase_primeWitnessDependent c hc_nonneg))) := rfl

/-- The prime-power channel provider emitted at state `n`. -/
def providerAt (P : PrimePowerChannelProvider) (n : ℕ) : WeightProvider ℕ :=
  P.kernel.channelProviderAt n

/-- Alias matching the kernel-level channel-provider name. -/
def channelProviderAt (P : PrimePowerChannelProvider) (n : ℕ) :
    WeightProvider ℕ :=
  P.providerAt n

@[simp] theorem ofKernelWithWeight_channelProviderAt_index
    (T : PrimePowerDivisorTransitionKernel)
    (w : ℕ → ℕ → ℚ)
    (hw_nonneg :
      ∀ n q, q ∈ T.toDivisorTransitionKernel.index n → 0 ≤ w n q)
    (hw_subprob : (T.withWeight w hw_nonneg).SubProbability)
    (n : ℕ) :
    ((ofKernelWithWeight T w hw_nonneg hw_subprob).channelProviderAt n).index =
      T.toDivisorTransitionKernel.index n := rfl

@[simp] theorem ofKernelWithWeight_channelProviderAt_weight
    (T : PrimePowerDivisorTransitionKernel)
    (w : ℕ → ℕ → ℚ)
    (hw_nonneg :
      ∀ n q, q ∈ T.toDivisorTransitionKernel.index n → 0 ≤ w n q)
    (hw_subprob : (T.withWeight w hw_nonneg).SubProbability)
    (n : ℕ) :
    ((ofKernelWithWeight T w hw_nonneg hw_subprob).channelProviderAt n).weight =
      w n := rfl

@[simp] theorem ofVonMangoldtLikeWeight_channelProviderAt_index
    (T : PrimePowerDivisorTransitionKernel)
    (w : ℕ → ℕ → ℚ)
    (hw : T.VonMangoldtLikeWeight w)
    (hw_subprob :
      (T.withWeight w (T.vonMangoldtLikeWeight_nonneg hw)).SubProbability)
    (n : ℕ) :
    ((ofVonMangoldtLikeWeight T w hw hw_subprob).channelProviderAt n).index =
      T.toDivisorTransitionKernel.index n := rfl

@[simp] theorem ofVonMangoldtLikeWeight_channelProviderAt_weight
    (T : PrimePowerDivisorTransitionKernel)
    (w : ℕ → ℕ → ℚ)
    (hw : T.VonMangoldtLikeWeight w)
    (hw_subprob :
      (T.withWeight w (T.vonMangoldtLikeWeight_nonneg hw)).SubProbability)
    (n : ℕ) :
    ((ofVonMangoldtLikeWeight T w hw hw_subprob).channelProviderAt n).weight =
      w n := rfl

@[simp] theorem ofPrimeWitnessDependentWeight_channelProviderAt_index
    (T : PrimePowerDivisorTransitionKernel)
    (w c : ℕ → ℕ → ℚ)
    (hw : T.PrimeWitnessDependentWeight w c)
    (hw_subprob :
      (T.withWeight w
        (T.vonMangoldtLikeWeight_nonneg
          (T.vonMangoldtLikeWeight_of_primeWitnessDependent hw))).SubProbability)
    (n : ℕ) :
    ((ofPrimeWitnessDependentWeight T w c hw hw_subprob).channelProviderAt n).index =
      T.toDivisorTransitionKernel.index n := rfl

@[simp] theorem ofPrimeWitnessDependentWeight_channelProviderAt_weight
    (T : PrimePowerDivisorTransitionKernel)
    (w c : ℕ → ℕ → ℚ)
    (hw : T.PrimeWitnessDependentWeight w c)
    (hw_subprob :
      (T.withWeight w
        (T.vonMangoldtLikeWeight_nonneg
          (T.vonMangoldtLikeWeight_of_primeWitnessDependent hw))).SubProbability)
    (n : ℕ) :
    ((ofPrimeWitnessDependentWeight T w c hw hw_subprob).channelProviderAt n).weight =
      w n := rfl

@[simp] theorem ofWitnessProviderWeight_channelProviderAt_index
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (c : ℕ → ℕ → ℚ)
    (hc_nonneg :
      ∀ n q (hq : q ∈ T.toDivisorTransitionKernel.index n),
        0 ≤ c n ((W.label n q hq).p))
    (hw_subprob :
      (T.withWeight (W.weightOfBase c)
        (T.vonMangoldtLikeWeight_nonneg
          (T.vonMangoldtLikeWeight_of_primeWitnessDependent
            (W.weightOfBase_primeWitnessDependent c hc_nonneg)))).SubProbability)
    (n : ℕ) :
    ((ofWitnessProviderWeight W c hc_nonneg hw_subprob).channelProviderAt n).index =
      T.toDivisorTransitionKernel.index n := rfl

@[simp] theorem ofWitnessProviderWeight_channelProviderAt_weight
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (c : ℕ → ℕ → ℚ)
    (hc_nonneg :
      ∀ n q (hq : q ∈ T.toDivisorTransitionKernel.index n),
        0 ≤ c n ((W.label n q hq).p))
    (hw_subprob :
      (T.withWeight (W.weightOfBase c)
        (T.vonMangoldtLikeWeight_nonneg
          (T.vonMangoldtLikeWeight_of_primeWitnessDependent
            (W.weightOfBase_primeWitnessDependent c hc_nonneg)))).SubProbability)
    (n : ℕ) :
    ((ofWitnessProviderWeight W c hc_nonneg hw_subprob).channelProviderAt n).weight =
      W.weightOfBase c n := rfl

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

namespace PrimePowerWitnessProvider

/--
Hit-mass bound for a channel provider built from a witness-provider base-prime
weight.
-/
theorem weightOfBase_hitMass_le_const
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (c : ℕ → ℕ → ℚ)
    (hc_nonneg :
      ∀ n q (hq : q ∈ T.toDivisorTransitionKernel.index n),
        0 ≤ c n ((W.label n q hq).p))
    (hw_subprob :
      (T.withWeight (W.weightOfBase c)
        (T.vonMangoldtLikeWeight_nonneg
          (T.vonMangoldtLikeWeight_of_primeWitnessDependent
            (W.weightOfBase_primeWitnessDependent c hc_nonneg)))).SubProbability)
    {M : DkMath.CosmicFormula.Mass.MassSpace ℕ} {S : Finset ℕ}
    (n : ℕ) (F : SourceControlledChainFamily M ℕ)
    (hcompat :
      (PrimePowerChannelProvider.ofWitnessProviderWeight W c hc_nonneg
        hw_subprob).kernel.CompatibleAt n F)
    (hS : PrimitiveOn S) {C : ℚ} (hC : 0 ≤ C)
    (hsource : ∀ q ∈ F.index, M.μ (F.source q) ≤ C) :
    ((PrimePowerChannelProvider.ofWitnessProviderWeight W c hc_nonneg
      hw_subprob).applyAtToSourceControlled n F hcompat).weightedHitMass S ≤ C := by
  exact (PrimePowerChannelProvider.ofWitnessProviderWeight W c hc_nonneg
    hw_subprob).weightedHitMass_le_const_applyAtToSourceControlled
      n F hcompat hS hC hsource

end PrimePowerWitnessProvider

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

/-- The sample label `2` with its explicit prime-power witness. -/
def samplePrimePowerLabel_two : PrimePowerLabel where
  q := 2
  p := 2
  k := 1
  prime := by norm_num
  k_pos := by norm_num
  eq_pow := by norm_num

/-- The sample label `5` with its explicit prime-power witness. -/
def samplePrimePowerLabel_five : PrimePowerLabel where
  q := 5
  p := 5
  k := 1
  prime := by norm_num
  k_pos := by norm_num
  eq_pow := by norm_num

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

/-- Explicit prime-power witnesses for every indexed label of the sample kernel. -/
def sampleTenPrimePowerWitnessProvider :
    PrimePowerWitnessProvider sampleTenPrimePowerDivisorTransitionKernel where
  label := by
    intro n q hq
    by_cases hn : n = 10
    · subst n
      by_cases hq_two : q = 2
      · subst q
        exact samplePrimePowerLabel_two
      · have hq_five : q = 5 := by
          simp only [sampleTenPrimePowerDivisorTransitionKernel,
            sampleTenDivisorTransitionKernel, if_true, Finset.mem_insert,
            Finset.mem_singleton] at hq
          rcases hq with hq_two' | hq_five
          · exact False.elim (hq_two hq_two')
          · exact hq_five
        subst q
        exact samplePrimePowerLabel_five
    · simp [sampleTenPrimePowerDivisorTransitionKernel,
        sampleTenDivisorTransitionKernel, hn] at hq
  label_q := by
    intro n q hq
    by_cases hn : n = 10
    · subst n
      simp only [sampleTenPrimePowerDivisorTransitionKernel,
        sampleTenDivisorTransitionKernel, if_true, Finset.mem_insert,
        Finset.mem_singleton] at hq
      rcases hq with rfl | rfl <;> rfl
    · simp [sampleTenPrimePowerDivisorTransitionKernel,
        sampleTenDivisorTransitionKernel, hn] at hq

/-- The sample witness provider proves indexed sample labels are prime powers. -/
theorem sampleTenPrimePowerWitnessProvider_isPrimePowerLabel
    {n q : ℕ}
    (hq :
      q ∈ sampleTenPrimePowerDivisorTransitionKernel.toDivisorTransitionKernel.index n) :
    IsPrimePowerLabel q :=
  sampleTenPrimePowerWitnessProvider.isPrimePowerLabel hq

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

/-- The explicit sample label `2 = 2 ^ 1` gives a prime-power descent step. -/
theorem samplePrimePowerLabel_two_descent :
    PrimePowerDescentStep 10
      (sampleTenPrimePowerDivisorTransitionKernel.toDivisorTransitionKernel.next
        10 samplePrimePowerLabel_two.q) := by
  exact PrimePowerLabel.primePowerDescentStep_of_mem
    sampleTenPrimePowerDivisorTransitionKernel.toDivisorTransitionKernel
    samplePrimePowerLabel_two
    (by
      simp [samplePrimePowerLabel_two, sampleTenPrimePowerDivisorTransitionKernel,
        sampleTenDivisorTransitionKernel])

/-- The explicit sample label `5 = 5 ^ 1` gives a prime-power descent step. -/
theorem samplePrimePowerLabel_five_descent :
    PrimePowerDescentStep 10
      (sampleTenPrimePowerDivisorTransitionKernel.toDivisorTransitionKernel.next
        10 samplePrimePowerLabel_five.q) := by
  exact PrimePowerLabel.primePowerDescentStep_of_mem
    sampleTenPrimePowerDivisorTransitionKernel.toDivisorTransitionKernel
    samplePrimePowerLabel_five
    (by
      simp [samplePrimePowerLabel_five, sampleTenPrimePowerDivisorTransitionKernel,
        sampleTenDivisorTransitionKernel])

/-- The sample witness provider gives the `10 -> 5` prime-power descent step. -/
theorem sampleTenPrimePowerWitnessProvider_two_descent :
    PrimePowerDescentStep 10
      (sampleTenPrimePowerDivisorTransitionKernel.toDivisorTransitionKernel.next
        10 2) := by
  exact sampleTenPrimePowerWitnessProvider.primePowerDescentStep
    (by simp [sampleTenPrimePowerDivisorTransitionKernel,
      sampleTenDivisorTransitionKernel])

/-- The sample witness provider gives the `10 -> 2` prime-power descent step. -/
theorem sampleTenPrimePowerWitnessProvider_five_descent :
    PrimePowerDescentStep 10
      (sampleTenPrimePowerDivisorTransitionKernel.toDivisorTransitionKernel.next
        10 5) := by
  exact sampleTenPrimePowerWitnessProvider.primePowerDescentStep
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

/-- The sample toy base weight assigns weight `1` to prime base `2` at state `10`. -/
def sampleTenToyPrimeBaseWeight (n p : ℕ) : ℚ :=
  if n = 10 ∧ p = 2 then 1 else 0

/--
The sample witness provider turns the sample base-prime weight into a
prime-witness-dependent label weight.
-/
theorem sampleTenPrimePowerWitnessProvider_weightOfBase_primeWitnessDependent :
    sampleTenPrimePowerDivisorTransitionKernel.PrimeWitnessDependentWeight
      (sampleTenPrimePowerWitnessProvider.weightOfBase sampleTenToyPrimeBaseWeight)
      sampleTenToyPrimeBaseWeight := by
  exact sampleTenPrimePowerWitnessProvider.weightOfBase_primeWitnessDependent
    sampleTenToyPrimeBaseWeight
    (by
      intro n q hq
      by_cases hn : n = 10
      · subst n
        simp only [sampleTenPrimePowerDivisorTransitionKernel,
          sampleTenDivisorTransitionKernel, if_true, Finset.mem_insert,
          Finset.mem_singleton] at hq
        rcases hq with rfl | rfl
        · norm_num [sampleTenPrimePowerWitnessProvider,
            samplePrimePowerLabel_two, sampleTenToyPrimeBaseWeight]
        · norm_num [sampleTenPrimePowerWitnessProvider,
            samplePrimePowerLabel_five, sampleTenToyPrimeBaseWeight]
      · simp [sampleTenPrimePowerDivisorTransitionKernel,
          sampleTenDivisorTransitionKernel, hn] at hq)

/-- The sample base-prime weight is nonnegative on the witness-provider index. -/
theorem sampleTenToyPrimeBaseWeight_nonneg_on_index :
    ∀ n q
      (hq :
        q ∈ sampleTenPrimePowerDivisorTransitionKernel.toDivisorTransitionKernel.index n),
      0 ≤ sampleTenToyPrimeBaseWeight n
        ((sampleTenPrimePowerWitnessProvider.label n q hq).p) := by
  intro n q hq
  by_cases hn : n = 10
  · subst n
    simp only [sampleTenPrimePowerDivisorTransitionKernel,
      sampleTenDivisorTransitionKernel, if_true, Finset.mem_insert,
      Finset.mem_singleton] at hq
    rcases hq with rfl | rfl
    · norm_num [sampleTenPrimePowerWitnessProvider,
        samplePrimePowerLabel_two, sampleTenToyPrimeBaseWeight]
    · norm_num [sampleTenPrimePowerWitnessProvider,
        samplePrimePowerLabel_five, sampleTenToyPrimeBaseWeight]
  · simp [sampleTenPrimePowerDivisorTransitionKernel,
      sampleTenDivisorTransitionKernel, hn] at hq

/-- The witness-provider-built sample weight agrees with the hand-written toy weight. -/
theorem sampleTenPrimePowerWitnessProvider_weightOfBase_eq_sampleTenToyWeight :
    sampleTenPrimePowerWitnessProvider.weightOfBase sampleTenToyPrimeBaseWeight =
      sampleTenToyWeight := by
  funext n q
  by_cases hn : n = 10
  · subst n
    by_cases hq_two : q = 2
    · subst q
      norm_num [PrimePowerWitnessProvider.weightOfBase,
        sampleTenPrimePowerWitnessProvider, samplePrimePowerLabel_two,
        sampleTenPrimePowerDivisorTransitionKernel, sampleTenDivisorTransitionKernel,
        sampleTenToyPrimeBaseWeight, sampleTenToyWeight]
    · by_cases hq_five : q = 5
      · subst q
        norm_num [PrimePowerWitnessProvider.weightOfBase,
          sampleTenPrimePowerWitnessProvider, samplePrimePowerLabel_five,
          sampleTenPrimePowerDivisorTransitionKernel, sampleTenDivisorTransitionKernel,
          sampleTenToyPrimeBaseWeight, sampleTenToyWeight]
      · simp [PrimePowerWitnessProvider.weightOfBase,
          sampleTenPrimePowerDivisorTransitionKernel, sampleTenDivisorTransitionKernel,
          sampleTenToyWeight, hq_two, hq_five]
  · simp [PrimePowerWitnessProvider.weightOfBase,
      sampleTenPrimePowerDivisorTransitionKernel, sampleTenDivisorTransitionKernel,
      sampleTenToyWeight, hn]

/-- The sample toy weight is nonnegative on the sample channel index. -/
theorem sampleTenToyWeight_nonneg :
    ∀ n q,
      q ∈ sampleTenPrimePowerDivisorTransitionKernel.toDivisorTransitionKernel.index n →
        0 ≤ sampleTenToyWeight n q := by
  intro n q _hq
  by_cases h : n = 10 ∧ q = 2
  · simp [sampleTenToyWeight, h]
  · simp [sampleTenToyWeight, h]

/-- The sample toy weight is von-Mangoldt-like in the finite channel sense. -/
theorem sampleTenToyWeight_vonMangoldtLikeWeight :
    sampleTenPrimePowerDivisorTransitionKernel.VonMangoldtLikeWeight
      sampleTenToyWeight :=
  sampleTenPrimePowerDivisorTransitionKernel
    |>.vonMangoldtLikeWeight_of_nonneg sampleTenToyWeight_nonneg

/--
The sample toy weight is expressible through the prime base of a prime-power
witness.
-/
theorem sampleTenToyWeight_primeWitnessDependent :
    sampleTenPrimePowerDivisorTransitionKernel.PrimeWitnessDependentWeight
      sampleTenToyWeight sampleTenToyPrimeBaseWeight := by
  intro n q hq
  by_cases hn : n = 10
  · subst n
    simp only [sampleTenPrimePowerDivisorTransitionKernel,
      sampleTenDivisorTransitionKernel, if_true, Finset.mem_insert,
      Finset.mem_singleton] at hq
    rcases hq with rfl | rfl
    · refine ⟨2, 1, by norm_num, by norm_num, by norm_num, ?_, by norm_num [sampleTenToyWeight]⟩
      norm_num [sampleTenToyWeight, sampleTenToyPrimeBaseWeight]
    · refine ⟨5, 1, by norm_num, by norm_num, by norm_num, ?_, by norm_num [sampleTenToyWeight]⟩
      norm_num [sampleTenToyWeight, sampleTenToyPrimeBaseWeight]
  · simp [sampleTenPrimePowerDivisorTransitionKernel,
      sampleTenDivisorTransitionKernel, hn] at hq

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

/--
The witness-provider-built sample kernel is sub-probability normalized.
-/
theorem sampleTenWitnessProviderWeightKernel_subProbability :
    (sampleTenPrimePowerDivisorTransitionKernel.withWeight
      (sampleTenPrimePowerWitnessProvider.weightOfBase sampleTenToyPrimeBaseWeight)
      (sampleTenPrimePowerDivisorTransitionKernel.vonMangoldtLikeWeight_nonneg
        (sampleTenPrimePowerDivisorTransitionKernel
          |>.vonMangoldtLikeWeight_of_primeWitnessDependent
            (sampleTenPrimePowerWitnessProvider.weightOfBase_primeWitnessDependent
              sampleTenToyPrimeBaseWeight
              sampleTenToyPrimeBaseWeight_nonneg_on_index)))).SubProbability := by
  intro n
  by_cases hn : n = 10
  · subst n
    norm_num [PrimePowerDivisorTransitionKernel.SubProbability,
      PrimePowerDivisorTransitionKernel.withWeight,
      PrimePowerWitnessProvider.weightOfBase,
      DivisorTransitionKernel.SubProbability,
      DivisorTransitionKernel.toFiniteTransitionKernel,
      FiniteTransitionKernel.SubProbability,
      FiniteTransitionKernel.toFiniteKernel,
      FiniteKernel.providerAt,
      WeightProvider.SubProbability,
      WeightProvider.totalWeight,
      sampleTenPrimePowerWitnessProvider,
      samplePrimePowerLabel_two,
      samplePrimePowerLabel_five,
      sampleTenPrimePowerDivisorTransitionKernel,
      sampleTenDivisorTransitionKernel,
      sampleTenToyPrimeBaseWeight]
  · simp [PrimePowerDivisorTransitionKernel.withWeight,
      PrimePowerWitnessProvider.weightOfBase,
      DivisorTransitionKernel.toFiniteTransitionKernel,
      FiniteTransitionKernel.toFiniteKernel,
      FiniteKernel.providerAt,
      WeightProvider.SubProbability,
      WeightProvider.totalWeight,
      sampleTenPrimePowerWitnessProvider,
      sampleTenPrimePowerDivisorTransitionKernel,
      sampleTenDivisorTransitionKernel, hn]

/-- The toy-weighted sample packaged as a prime-power channel provider. -/
def sampleTenToyWeightChannelProvider : PrimePowerChannelProvider :=
  PrimePowerChannelProvider.ofPrimeWitnessDependentWeight
    sampleTenPrimePowerDivisorTransitionKernel
    sampleTenToyWeight
    sampleTenToyPrimeBaseWeight
    sampleTenToyWeight_primeWitnessDependent
    sampleTenToyWeightKernel_subProbability

/-- The toy-weighted channel provider emits sub-probability providers. -/
theorem sampleTenToyWeightChannelProvider_channelProviderAt_subProbability
    (n : ℕ) :
    (sampleTenToyWeightChannelProvider.channelProviderAt n).SubProbability :=
  sampleTenToyWeightChannelProvider.channelProviderAt_subProbability n

/--
The sample witness provider and base-prime toy weight packaged as a prime-power
channel provider.
-/
def sampleTenWitnessProviderWeightChannelProvider :
    PrimePowerChannelProvider :=
  PrimePowerChannelProvider.ofWitnessProviderWeight
    sampleTenPrimePowerWitnessProvider
    sampleTenToyPrimeBaseWeight
    sampleTenToyPrimeBaseWeight_nonneg_on_index
    sampleTenWitnessProviderWeightKernel_subProbability

/-- The witness-provider-weighted sample emits sub-probability providers. -/
theorem sampleTenWitnessProviderWeightChannelProvider_channelProviderAt_subProbability
    (n : ℕ) :
    (sampleTenWitnessProviderWeightChannelProvider.channelProviderAt n).SubProbability :=
  sampleTenWitnessProviderWeightChannelProvider.channelProviderAt_subProbability n

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

/--
The same concrete bound, named for the prime-witness-dependent constructor
route.
-/
theorem sampleTenPrimeWitnessDependentWeight_hitMass_le_one :
    (sampleTenToyWeightChannelProvider.applyAtToSourceControlled 10
      sampleTenToyWeightSourceControlledFamily
      (by
        change sampleTenToyWeightKernel.toDivisorTransitionKernel.index 10 =
          sampleTenToyWeightSourceControlledFamily.index
        simp [sampleTenToyWeightSourceControlledFamily])).weightedHitMass
      ({2, 5} : Finset ℕ) ≤ 1 :=
  sampleTenToyWeightChannelProvider_hitMass_le_one

/--
The witness-provider-built sample channel provider gives the same concrete
weighted hit mass bound by `1`.
-/
theorem sampleTenWitnessProviderWeight_hitMass_le_one :
    (sampleTenWitnessProviderWeightChannelProvider.applyAtToSourceControlled 10
      sampleTenToyWeightSourceControlledFamily
      (by
        change
          sampleTenWitnessProviderWeightChannelProvider.kernel.toDivisorTransitionKernel.index 10 =
          sampleTenToyWeightSourceControlledFamily.index
        simp [sampleTenWitnessProviderWeightChannelProvider,
          sampleTenPrimePowerDivisorTransitionKernel,
          sampleTenToyWeightSourceControlledFamily])).weightedHitMass
      ({2, 5} : Finset ℕ) ≤ 1 := by
  exact sampleTenWitnessProviderWeightChannelProvider
    |>.weightedHitMass_le_const_applyAtToSourceControlled 10
      sampleTenToyWeightSourceControlledFamily
      (by
        change
          sampleTenWitnessProviderWeightChannelProvider.kernel.toDivisorTransitionKernel.index 10 =
          sampleTenToyWeightSourceControlledFamily.index
        simp [sampleTenWitnessProviderWeightChannelProvider,
          sampleTenPrimePowerDivisorTransitionKernel,
          sampleTenToyWeightSourceControlledFamily])
      (primitiveOn_pair (by norm_num) (by norm_num))
      (by norm_num)
      (by
        intro _q _hq
        rfl)

end DkMath.NumberTheory.PrimitiveSet
