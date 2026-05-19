/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PrimitiveSet.ShadowHittingBridge
import DkMath.NumberTheory.PrimitiveSet.DescentBridge
import DkMath.NumberTheory.PrimitiveSet.FullExponentSlotCanonical
import DkMath.NumberTheory.PrimitiveSet.DivisorPathList

#print "file: DkMath.NumberTheory.PrimitiveSet.LogCapacityHittingBridge"

namespace DkMath.NumberTheory.PrimitiveSet

open DkMath.CosmicFormula.Mass

/--
Uniform source-mass bound on log-capacity states.

This small provider shape lets concrete mass models supply the single source
bound needed by one-step divisor-descent families.
-/
def LogCapacitySourceMassBound
    (M : MassSpace ℕ) (C : ℝ) : Prop :=
  ∀ s : LogCapacityState, (M.μ s.1 : ℝ) ≤ C

/-- Unit mass is uniformly bounded by `1` on log-capacity states. -/
theorem unitNatMassSpace_logCapacitySourceMassBound_one :
    LogCapacitySourceMassBound unitNatMassSpace 1 := by
  intro s
  simp [unitNatMassSpace]

/-- Nonunit indicator mass is uniformly bounded by `1` on log-capacity states. -/
theorem nonunitNatMassSpace_logCapacitySourceMassBound_one :
    LogCapacitySourceMassBound nonunitNatMassSpace 1 := by
  intro s
  have hs : s.1 ≠ 1 := Nat.ne_of_gt s.2
  simp [nonunitNatMassSpace, hs]

/-- Tail-support indicator mass is uniformly bounded by `1`. -/
theorem tailIndicatorNatMassSpace_logCapacitySourceMassBound_one (N : ℕ) :
    LogCapacitySourceMassBound (tailIndicatorNatMassSpace N) 1 := by
  intro s
  by_cases hs : s.1 = 0 ∨ N ≤ s.1 <;> simp [tailIndicatorNatMassSpace, hs]

/-- Scaled tail-support indicator mass is uniformly bounded by its height. -/
theorem scaledTailIndicatorNatMassSpace_logCapacitySourceMassBound
    (N : ℕ) (c : ℚ) (hc : 0 ≤ c) :
    LogCapacitySourceMassBound (scaledTailIndicatorNatMassSpace N c hc) (c : ℝ) := by
  intro s
  by_cases hs : s.1 = 0 ∨ N ≤ s.1
  · simp [scaledTailIndicatorNatMassSpace, hs]
  · simp [scaledTailIndicatorNatMassSpace, hs, hc]

/-- Two-step tail-support mass is uniformly bounded by its high height. -/
theorem twoStepTailNatMassSpace_logCapacitySourceMassBound
    (N M : ℕ) (cLow cHigh : ℚ)
    (hLow : 0 ≤ cLow) (hStep : cLow ≤ cHigh) :
    LogCapacitySourceMassBound
      (twoStepTailNatMassSpace N M cLow cHigh hLow hStep) (cHigh : ℝ) := by
  intro s
  have hHigh : 0 ≤ cHigh := hLow.trans hStep
  by_cases hsHigh : s.1 = 0 ∨ M ≤ s.1
  · simp [twoStepTailNatMassSpace, hsHigh]
  · by_cases hsLow : N ≤ s.1
    · simp [twoStepTailNatMassSpace, hsHigh, hsLow, hStep]
    · simp [twoStepTailNatMassSpace, hsHigh, hsLow, hHigh]

/-- Bounded monotone natural mass is uniformly bounded by its top bound. -/
theorem boundedMonotoneNatMassSpace_logCapacitySourceMassBound
    (height : ℕ → ℚ) (C : ℚ)
    (hnonneg : ∀ n, 0 ≤ height n)
    (hbound : ∀ n, height n ≤ C) :
    LogCapacitySourceMassBound
      (boundedMonotoneNatMassSpace height C hnonneg hbound) (C : ℝ) := by
  intro s
  by_cases hs : s.1 = 0
  · simp [boundedMonotoneNatMassSpace, hs]
  · simp only [boundedMonotoneNatMassSpace, hs, if_false, Rat.cast_le]
    exact hbound s.1

/-- Finite step tail mass is uniformly bounded by its total increment. -/
theorem finiteStepTailNatMassSpace_logCapacitySourceMassBound
    {ι : Type _} [DecidableEq ι]
    (steps : Finset ι) (threshold : ι → ℕ) (increment : ι → ℚ)
    (hinc : ∀ i ∈ steps, 0 ≤ increment i) :
    LogCapacitySourceMassBound
      (finiteStepTailNatMassSpace steps threshold increment hinc)
      ((Finset.sum steps increment : ℚ) : ℝ) :=
  boundedMonotoneNatMassSpace_logCapacitySourceMassBound
    (finiteStepTailHeight steps threshold increment)
    (Finset.sum steps increment)
    (finiteStepTailHeight_nonneg steps threshold increment hinc)
    (finiteStepTailHeight_le_total steps threshold increment hinc)

/--
Two-step-as-finite-step tail mass is uniformly bounded by its high height.
-/
theorem twoStepAsFiniteStepTailNatMassSpace_logCapacitySourceMassBound
    (N M : ℕ) (cLow cHigh : ℚ)
    (hLow : 0 ≤ cLow) (hStep : cLow ≤ cHigh) :
    LogCapacitySourceMassBound
      (twoStepAsFiniteStepTailNatMassSpace N M cLow cHigh hLow hStep)
      (cHigh : ℝ) := by
  have hsource :=
    finiteStepTailNatMassSpace_logCapacitySourceMassBound
      (Finset.univ : Finset Bool)
      (twoStepTailFiniteThreshold N M)
      (twoStepTailFiniteIncrement cLow cHigh)
      (twoStepTailFiniteIncrement_nonneg cLow cHigh hLow hStep)
  have hsum :
      ((Finset.sum (Finset.univ : Finset Bool)
        (twoStepTailFiniteIncrement cLow cHigh) : ℚ) : ℝ) = (cHigh : ℝ) := by
    exact_mod_cast twoStepTailFiniteIncrement_sum cLow cHigh
  rw [← hsum]
  simpa [twoStepAsFiniteStepTailNatMassSpace] using hsource

namespace PrimePowerWitnessProvider

/--
The selected global log-capacity sub-Markov shadow at state `s` is compatible
with a source-controlled family whose index is the selected channel set
`IOf s.1`.
-/
theorem globalLogCapacitySubMarkovShadow_providerAt_compatible
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (IOf : ℕ → Finset ℕ)
    (hIOf :
      ∀ n q, q ∈ IOf n → q ∈ T.toDivisorTransitionKernel.index n)
    (s : LogCapacityState)
    {M : MassSpace ℕ}
    (F : SourceControlledChainFamily M ℕ)
    (hindex : IOf s.1 = F.index) :
    ((W.globalLogCapacitySubMarkovShadow IOf hIOf).providerAt s).Compatible F := by
  simpa [RealWeightProvider.Compatible] using hindex

/--
Apply the selected global log-capacity sub-Markov shadow at state `s` to a
source-controlled family whose index is `IOf s.1`.
-/
noncomputable def globalLogCapacitySubMarkovShadow_applyAtToSourceControlled
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (IOf : ℕ → Finset ℕ)
    (hIOf :
      ∀ n q, q ∈ IOf n → q ∈ T.toDivisorTransitionKernel.index n)
    (s : LogCapacityState)
    {M : MassSpace ℕ}
    (F : SourceControlledChainFamily M ℕ)
    (hindex : IOf s.1 = F.index) :
    RealWeightedPathFamily M ℕ :=
  (W.globalLogCapacitySubMarkovShadow IOf hIOf).applyAtToSourceControlled
    s F
    (W.globalLogCapacitySubMarkovShadow_providerAt_compatible IOf hIOf s F hindex)

@[simp] theorem globalLogCapacitySubMarkovShadow_applyAtToSourceControlled_index
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (IOf : ℕ → Finset ℕ)
    (hIOf :
      ∀ n q, q ∈ IOf n → q ∈ T.toDivisorTransitionKernel.index n)
    (s : LogCapacityState)
    {M : MassSpace ℕ}
    (F : SourceControlledChainFamily M ℕ)
    (hindex : IOf s.1 = F.index) :
    (W.globalLogCapacitySubMarkovShadow_applyAtToSourceControlled IOf hIOf s F hindex).index =
      F.index :=
  rfl

/--
Primitive hitting bound for the selected global log-capacity sub-Markov shadow
at state `s`, applied to an index-compatible source-controlled family.
-/
theorem globalLogCapacitySubMarkovShadow_weightedHitMass_le_const
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (IOf : ℕ → Finset ℕ)
    (hIOf :
      ∀ n q, q ∈ IOf n → q ∈ T.toDivisorTransitionKernel.index n)
    (s : LogCapacityState)
    {M : MassSpace ℕ} {A : Finset ℕ}
    (F : SourceControlledChainFamily M ℕ)
    (hindex : IOf s.1 = F.index)
    (hA : PrimitiveOn A) {C : ℝ} (hC : 0 ≤ C)
    (hsource : ∀ q ∈ F.index, (M.μ (F.source q) : ℝ) ≤ C) :
    (W.globalLogCapacitySubMarkovShadow_applyAtToSourceControlled
      IOf hIOf s F hindex).weightedHitMass A ≤ C :=
  (W.globalLogCapacitySubMarkovShadow IOf hIOf)
    |>.weightedHitMass_le_const_applyAtToSourceControlled
      (W.globalLogCapacitySubMarkovShadow_subProbability IOf hIOf)
      s F
      (W.globalLogCapacitySubMarkovShadow_providerAt_compatible IOf hIOf s F hindex)
      hA hC hsource

/--
Apply the selected global log-capacity sub-Markov shadow at state `s` to an
external multi-step divisor path family whose index is `IOf s.1`.
-/
noncomputable def globalLogCapacitySubMarkovShadow_applyAtToAdjacentDivisorPathFamily
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (IOf : ℕ → Finset ℕ)
    (hIOf :
      ∀ n q, q ∈ IOf n → q ∈ T.toDivisorTransitionKernel.index n)
    (s : LogCapacityState)
    {M : MassSpace ℕ}
    (F : AdjacentDivisorPathFamily ℕ)
    (hM : DvdMonotoneMass M)
    (hindex : IOf s.1 = F.index) :
    RealWeightedPathFamily M ℕ :=
  W.globalLogCapacitySubMarkovShadow_applyAtToSourceControlled IOf hIOf s
    (F.toDvdControlledChainFamily.toSourceControlled hM)
    (by simpa using hindex)

@[simp] theorem globalLogCapacitySubMarkovShadow_applyAtToAdjacentDivisorPathFamily_index
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (IOf : ℕ → Finset ℕ)
    (hIOf :
      ∀ n q, q ∈ IOf n → q ∈ T.toDivisorTransitionKernel.index n)
    (s : LogCapacityState)
    {M : MassSpace ℕ}
    (F : AdjacentDivisorPathFamily ℕ)
    (hM : DvdMonotoneMass M)
    (hindex : IOf s.1 = F.index) :
    (W.globalLogCapacitySubMarkovShadow_applyAtToAdjacentDivisorPathFamily
      IOf hIOf s F hM hindex).index = F.index :=
  rfl

/--
Primitive hitting bound for the selected global log-capacity sub-Markov shadow
on an external multi-step divisor path family.
-/
theorem globalLogCapacitySubMarkovShadow_adjacentDivisorPathFamily_weightedHitMass_le_const
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (IOf : ℕ → Finset ℕ)
    (hIOf :
      ∀ n q, q ∈ IOf n → q ∈ T.toDivisorTransitionKernel.index n)
    (s : LogCapacityState)
    {M : MassSpace ℕ}
    (F : AdjacentDivisorPathFamily ℕ)
    (hM : DvdMonotoneMass M)
    (hindex : IOf s.1 = F.index)
    {A : Finset ℕ}
    (hA : PrimitiveOn A) {C : ℝ} (hC : 0 ≤ C)
    (hsource : ∀ q ∈ F.index, (M.μ (F.source q) : ℝ) ≤ C) :
    (W.globalLogCapacitySubMarkovShadow_applyAtToAdjacentDivisorPathFamily
      IOf hIOf s F hM hindex).weightedHitMass A ≤ C :=
  W.globalLogCapacitySubMarkovShadow_weightedHitMass_le_const IOf hIOf s
    (F.toDvdControlledChainFamily.toSourceControlled hM)
    (by simpa using hindex)
    hA hC
    (by
      intro q hq
      simpa using hsource q hq)

/--
Primitive hitting bound for an external multi-step divisor path family whose
sources are all the current log-capacity state.
-/
theorem globalLogCapacitySubMarkovShadow_adjacentDivisorPathFamily_weightedHitMass_le_of_sourceBound
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (IOf : ℕ → Finset ℕ)
    (hIOf :
      ∀ n q, q ∈ IOf n → q ∈ T.toDivisorTransitionKernel.index n)
    (s : LogCapacityState)
    {M : MassSpace ℕ}
    (F : AdjacentDivisorPathFamily ℕ)
    (hM : DvdMonotoneMass M)
    (hindex : IOf s.1 = F.index)
    (hsource_eq : ∀ q ∈ F.index, F.source q = s.1)
    {A : Finset ℕ}
    (hA : PrimitiveOn A) {C : ℝ} (hC : 0 ≤ C)
    (hsource : LogCapacitySourceMassBound M C) :
    (W.globalLogCapacitySubMarkovShadow_applyAtToAdjacentDivisorPathFamily
      IOf hIOf s F hM hindex).weightedHitMass A ≤ C :=
  W.globalLogCapacitySubMarkovShadow_adjacentDivisorPathFamily_weightedHitMass_le_const
    IOf hIOf s F hM hindex hA hC
    (by
      intro q hq
      simpa [hsource_eq q hq] using hsource s)

/--
Primitive hitting bound for the selected global log-capacity sub-Markov shadow
on a same-source external multi-step divisor path family with finite step tail
source mass.
-/
theorem
  globalLogCapacitySubMarkovShadow_finiteStepTailAdjacentDivisorPathFamily_weightedHitMass_le
    {T : PrimePowerDivisorTransitionKernel}
    {ι : Type _} [DecidableEq ι]
    (W : PrimePowerWitnessProvider T)
    (IOf : ℕ → Finset ℕ)
    (hIOf :
      ∀ n q, q ∈ IOf n → q ∈ T.toDivisorTransitionKernel.index n)
    (steps : Finset ι) (threshold : ι → ℕ) (increment : ι → ℚ)
    (hinc : ∀ i ∈ steps, 0 ≤ increment i)
    (s : LogCapacityState)
    (F : AdjacentDivisorPathFamily ℕ)
    (hindex : IOf s.1 = F.index)
    (hsource_eq : ∀ q ∈ F.index, F.source q = s.1)
    {A : Finset ℕ}
    (hA : PrimitiveOn A) :
    (W.globalLogCapacitySubMarkovShadow_applyAtToAdjacentDivisorPathFamily
      IOf hIOf s F
        (finiteStepTailNatMassSpace_dvdMonotone
          steps threshold increment hinc)
        hindex).weightedHitMass A ≤
      ((Finset.sum steps increment : ℚ) : ℝ) :=
  W.globalLogCapacitySubMarkovShadow_adjacentDivisorPathFamily_weightedHitMass_le_of_sourceBound
    IOf hIOf s F
    (finiteStepTailNatMassSpace_dvdMonotone steps threshold increment hinc)
    hindex hsource_eq hA
    (by exact_mod_cast Finset.sum_nonneg hinc)
    (finiteStepTailNatMassSpace_logCapacitySourceMassBound
      steps threshold increment hinc)

/--
Apply the selected global log-capacity sub-Markov shadow to the nat-indexed
singleton source-controlled family on `IOf s.1`.
-/
noncomputable def globalLogCapacitySubMarkovShadow_applyAtToNatSingletonSelf
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (IOf : ℕ → Finset ℕ)
    (hIOf :
      ∀ n q, q ∈ IOf n → q ∈ T.toDivisorTransitionKernel.index n)
    (s : LogCapacityState)
    (M : MassSpace ℕ) :
    RealWeightedPathFamily M ℕ :=
  W.globalLogCapacitySubMarkovShadow_applyAtToSourceControlled IOf hIOf s
    (SourceControlledChainFamily.natSingletonSelf (M := M) (IOf s.1))
    rfl

@[simp] theorem globalLogCapacitySubMarkovShadow_applyAtToNatSingletonSelf_index
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (IOf : ℕ → Finset ℕ)
    (hIOf :
      ∀ n q, q ∈ IOf n → q ∈ T.toDivisorTransitionKernel.index n)
    (s : LogCapacityState)
    (M : MassSpace ℕ) :
    (W.globalLogCapacitySubMarkovShadow_applyAtToNatSingletonSelf IOf hIOf s M).index =
      IOf s.1 :=
  rfl

/--
Primitive hitting bound for the selected global log-capacity sub-Markov shadow
on the nat-indexed singleton source-controlled family.
-/
theorem globalLogCapacitySubMarkovShadow_natSingletonSelf_weightedHitMass_le_const
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (IOf : ℕ → Finset ℕ)
    (hIOf :
      ∀ n q, q ∈ IOf n → q ∈ T.toDivisorTransitionKernel.index n)
    (s : LogCapacityState)
    {M : MassSpace ℕ} {A : Finset ℕ}
    (hA : PrimitiveOn A) {C : ℝ} (hC : 0 ≤ C)
    (hsource : ∀ q ∈ IOf s.1, (M.μ q : ℝ) ≤ C) :
    (W.globalLogCapacitySubMarkovShadow_applyAtToNatSingletonSelf
      IOf hIOf s M).weightedHitMass A ≤ C :=
  W.globalLogCapacitySubMarkovShadow_weightedHitMass_le_const IOf hIOf s
    (SourceControlledChainFamily.natSingletonSelf (M := M) (IOf s.1))
    rfl hA hC
    (by
      simpa using hsource)

/--
Apply the selected global log-capacity sub-Markov shadow to the one-step
divisor-descent family `{s.1 / q, s.1}` indexed by `IOf s.1`.
-/
noncomputable def globalLogCapacitySubMarkovShadow_applyAtToDivisorStep
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (IOf : ℕ → Finset ℕ)
    (hIOf :
      ∀ n q, q ∈ IOf n → q ∈ T.toDivisorTransitionKernel.index n)
    (s : LogCapacityState)
    {M : MassSpace ℕ}
    (hM : DvdMonotoneMass M) :
    RealWeightedPathFamily M ℕ :=
  W.globalLogCapacitySubMarkovShadow_applyAtToSourceControlled IOf hIOf s
    (SourceControlledChainFamily.ofDivisorStep hM s.1 (IOf s.1)
      (fun q hq => T.toDivisorTransitionKernel.index_dvd s.1 q (hIOf s.1 q hq)))
    rfl

@[simp] theorem globalLogCapacitySubMarkovShadow_applyAtToDivisorStep_index
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (IOf : ℕ → Finset ℕ)
    (hIOf :
      ∀ n q, q ∈ IOf n → q ∈ T.toDivisorTransitionKernel.index n)
    (s : LogCapacityState)
    {M : MassSpace ℕ}
    (hM : DvdMonotoneMass M) :
    (W.globalLogCapacitySubMarkovShadow_applyAtToDivisorStep IOf hIOf s hM).index =
      IOf s.1 :=
  rfl

/--
Primitive hitting bound for the selected global log-capacity sub-Markov shadow
on the one-step divisor-descent family at state `s`.
-/
theorem globalLogCapacitySubMarkovShadow_divisorStep_weightedHitMass_le_const
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (IOf : ℕ → Finset ℕ)
    (hIOf :
      ∀ n q, q ∈ IOf n → q ∈ T.toDivisorTransitionKernel.index n)
    (s : LogCapacityState)
    {M : MassSpace ℕ} (hM : DvdMonotoneMass M)
    {A : Finset ℕ}
    (hA : PrimitiveOn A) {C : ℝ} (hC : 0 ≤ C)
    (hsource : (M.μ s.1 : ℝ) ≤ C) :
    (W.globalLogCapacitySubMarkovShadow_applyAtToDivisorStep
      IOf hIOf s hM).weightedHitMass A ≤ C :=
  W.globalLogCapacitySubMarkovShadow_weightedHitMass_le_const IOf hIOf s
    (SourceControlledChainFamily.ofDivisorStep hM s.1 (IOf s.1)
      (fun q hq => T.toDivisorTransitionKernel.index_dvd s.1 q (hIOf s.1 q hq)))
    rfl hA hC
    (by
      intro q hq
      simpa using hsource)

/--
Primitive hitting bound for the selected global log-capacity sub-Markov shadow
on the one-step divisor-descent family, using a statewise source-bound provider.
-/
theorem globalLogCapacitySubMarkovShadow_divisorStep_weightedHitMass_le_of_sourceBound
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (IOf : ℕ → Finset ℕ)
    (hIOf :
      ∀ n q, q ∈ IOf n → q ∈ T.toDivisorTransitionKernel.index n)
    (s : LogCapacityState)
    {M : MassSpace ℕ} (hM : DvdMonotoneMass M)
    {A : Finset ℕ}
    (hA : PrimitiveOn A) {C : ℝ} (hC : 0 ≤ C)
    (hsource : LogCapacitySourceMassBound M C) :
    (W.globalLogCapacitySubMarkovShadow_applyAtToDivisorStep
      IOf hIOf s hM).weightedHitMass A ≤ C :=
  W.globalLogCapacitySubMarkovShadow_divisorStep_weightedHitMass_le_const
    IOf hIOf s hM hA hC (hsource s)

/--
Primitive hitting bound for the selected global log-capacity sub-Markov shadow
on the one-step divisor-descent family with unit source mass.
-/
theorem globalLogCapacitySubMarkovShadow_unitDivisorStep_weightedHitMass_le_one
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (IOf : ℕ → Finset ℕ)
    (hIOf :
      ∀ n q, q ∈ IOf n → q ∈ T.toDivisorTransitionKernel.index n)
    (s : LogCapacityState)
    {A : Finset ℕ}
    (hA : PrimitiveOn A) :
    (W.globalLogCapacitySubMarkovShadow_applyAtToDivisorStep
      IOf hIOf s unitNatMassSpace_dvdMonotone).weightedHitMass A ≤ 1 :=
  W.globalLogCapacitySubMarkovShadow_divisorStep_weightedHitMass_le_of_sourceBound
    IOf hIOf s unitNatMassSpace_dvdMonotone hA
    (by norm_num) unitNatMassSpace_logCapacitySourceMassBound_one

/--
Primitive hitting bound for the selected global log-capacity sub-Markov shadow
on the one-step divisor-descent family with nonunit indicator source mass.
-/
theorem globalLogCapacitySubMarkovShadow_nonunitDivisorStep_weightedHitMass_le_one
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (IOf : ℕ → Finset ℕ)
    (hIOf :
      ∀ n q, q ∈ IOf n → q ∈ T.toDivisorTransitionKernel.index n)
    (s : LogCapacityState)
    {A : Finset ℕ}
    (hA : PrimitiveOn A) :
    (W.globalLogCapacitySubMarkovShadow_applyAtToDivisorStep
      IOf hIOf s nonunitNatMassSpace_dvdMonotone).weightedHitMass A ≤ 1 :=
  W.globalLogCapacitySubMarkovShadow_divisorStep_weightedHitMass_le_of_sourceBound
    IOf hIOf s nonunitNatMassSpace_dvdMonotone hA
    (by norm_num) nonunitNatMassSpace_logCapacitySourceMassBound_one

/--
Primitive hitting bound for the selected global log-capacity sub-Markov shadow
on the one-step divisor-descent family with tail-support indicator source mass.
-/
theorem globalLogCapacitySubMarkovShadow_tailIndicatorDivisorStep_weightedHitMass_le_one
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (IOf : ℕ → Finset ℕ)
    (hIOf :
      ∀ n q, q ∈ IOf n → q ∈ T.toDivisorTransitionKernel.index n)
    (N : ℕ) (s : LogCapacityState)
    {A : Finset ℕ}
    (hA : PrimitiveOn A) :
    (W.globalLogCapacitySubMarkovShadow_applyAtToDivisorStep
      IOf hIOf s (tailIndicatorNatMassSpace_dvdMonotone N)).weightedHitMass A ≤ 1 :=
  W.globalLogCapacitySubMarkovShadow_divisorStep_weightedHitMass_le_of_sourceBound
    IOf hIOf s (tailIndicatorNatMassSpace_dvdMonotone N) hA
    (by norm_num) (tailIndicatorNatMassSpace_logCapacitySourceMassBound_one N)

/--
Primitive hitting bound for the selected global log-capacity sub-Markov shadow
on the one-step divisor-descent family with scaled tail-support source mass.
-/
theorem globalLogCapacitySubMarkovShadow_scaledTailIndicatorDivisorStep_weightedHitMass_le
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (IOf : ℕ → Finset ℕ)
    (hIOf :
      ∀ n q, q ∈ IOf n → q ∈ T.toDivisorTransitionKernel.index n)
    (N : ℕ) (c : ℚ) (hc : 0 ≤ c) (s : LogCapacityState)
    {A : Finset ℕ}
    (hA : PrimitiveOn A) :
    (W.globalLogCapacitySubMarkovShadow_applyAtToDivisorStep
      IOf hIOf s
        (scaledTailIndicatorNatMassSpace_dvdMonotone N c hc)).weightedHitMass A ≤
      (c : ℝ) :=
  W.globalLogCapacitySubMarkovShadow_divisorStep_weightedHitMass_le_of_sourceBound
    IOf hIOf s (scaledTailIndicatorNatMassSpace_dvdMonotone N c hc) hA
    (by exact_mod_cast hc)
    (scaledTailIndicatorNatMassSpace_logCapacitySourceMassBound N c hc)

/--
Primitive hitting bound for the selected global log-capacity sub-Markov shadow
on the one-step divisor-descent family with two-step tail-support source mass.
-/
theorem globalLogCapacitySubMarkovShadow_twoStepTailDivisorStep_weightedHitMass_le
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (IOf : ℕ → Finset ℕ)
    (hIOf :
      ∀ n q, q ∈ IOf n → q ∈ T.toDivisorTransitionKernel.index n)
    (N M : ℕ) (cLow cHigh : ℚ)
    (hLow : 0 ≤ cLow) (hStep : cLow ≤ cHigh)
    (s : LogCapacityState)
    {A : Finset ℕ}
    (hA : PrimitiveOn A) :
    (W.globalLogCapacitySubMarkovShadow_applyAtToDivisorStep
      IOf hIOf s
        (twoStepTailNatMassSpace_dvdMonotone
          N M cLow cHigh hLow hStep)).weightedHitMass A ≤
      (cHigh : ℝ) :=
  W.globalLogCapacitySubMarkovShadow_divisorStep_weightedHitMass_le_of_sourceBound
    IOf hIOf s (twoStepTailNatMassSpace_dvdMonotone N M cLow cHigh hLow hStep) hA
    (by exact_mod_cast hLow.trans hStep)
    (twoStepTailNatMassSpace_logCapacitySourceMassBound N M cLow cHigh hLow hStep)

/--
Primitive hitting bound for the selected global log-capacity sub-Markov shadow
on the one-step divisor-descent family with bounded monotone source mass.
-/
theorem globalLogCapacitySubMarkovShadow_boundedMonotoneDivisorStep_weightedHitMass_le
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (IOf : ℕ → Finset ℕ)
    (hIOf :
      ∀ n q, q ∈ IOf n → q ∈ T.toDivisorTransitionKernel.index n)
    (height : ℕ → ℚ) (C : ℚ)
    (hnonneg : ∀ n, 0 ≤ height n)
    (hbound : ∀ n, height n ≤ C)
    (hmono : ∀ ⦃a b : ℕ⦄, a ≤ b → height a ≤ height b)
    (s : LogCapacityState)
    {A : Finset ℕ}
    (hA : PrimitiveOn A) :
    (W.globalLogCapacitySubMarkovShadow_applyAtToDivisorStep
      IOf hIOf s
        (boundedMonotoneNatMassSpace_dvdMonotone
          height C hnonneg hbound hmono)).weightedHitMass A ≤
      (C : ℝ) := by
  have hC : 0 ≤ C := (hnonneg 0).trans (hbound 0)
  exact
    W.globalLogCapacitySubMarkovShadow_divisorStep_weightedHitMass_le_of_sourceBound
      IOf hIOf s
      (boundedMonotoneNatMassSpace_dvdMonotone height C hnonneg hbound hmono)
      hA
      (by exact_mod_cast hC)
      (boundedMonotoneNatMassSpace_logCapacitySourceMassBound height C hnonneg hbound)

/--
Primitive hitting bound for the selected global log-capacity sub-Markov shadow
on the one-step divisor-descent family with finite step tail source mass.
-/
theorem globalLogCapacitySubMarkovShadow_finiteStepTailDivisorStep_weightedHitMass_le
    {T : PrimePowerDivisorTransitionKernel}
    {ι : Type _} [DecidableEq ι]
    (W : PrimePowerWitnessProvider T)
    (IOf : ℕ → Finset ℕ)
    (hIOf :
      ∀ n q, q ∈ IOf n → q ∈ T.toDivisorTransitionKernel.index n)
    (steps : Finset ι) (threshold : ι → ℕ) (increment : ι → ℚ)
    (hinc : ∀ i ∈ steps, 0 ≤ increment i)
    (s : LogCapacityState)
    {A : Finset ℕ}
    (hA : PrimitiveOn A) :
    (W.globalLogCapacitySubMarkovShadow_applyAtToDivisorStep
      IOf hIOf s
        (finiteStepTailNatMassSpace_dvdMonotone
          steps threshold increment hinc)).weightedHitMass A ≤
      ((Finset.sum steps increment : ℚ) : ℝ) :=
  W.globalLogCapacitySubMarkovShadow_divisorStep_weightedHitMass_le_of_sourceBound
    IOf hIOf s
    (finiteStepTailNatMassSpace_dvdMonotone steps threshold increment hinc)
    hA
    (by exact_mod_cast Finset.sum_nonneg hinc)
    (finiteStepTailNatMassSpace_logCapacitySourceMassBound
      steps threshold increment hinc)

/--
Primitive hitting bound for the selected global log-capacity sub-Markov shadow
using the two-step tail mass through the finite-step interface.
-/
theorem globalLogCapacitySubMarkovShadow_twoStepAsFiniteStepTailDivisorStep_weightedHitMass_le
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (IOf : ℕ → Finset ℕ)
    (hIOf :
      ∀ n q, q ∈ IOf n → q ∈ T.toDivisorTransitionKernel.index n)
    (N M : ℕ) (cLow cHigh : ℚ)
    (hLow : 0 ≤ cLow) (hStep : cLow ≤ cHigh)
    (s : LogCapacityState)
    {A : Finset ℕ}
    (hA : PrimitiveOn A) :
    (W.globalLogCapacitySubMarkovShadow_applyAtToDivisorStep
      IOf hIOf s
        (twoStepAsFiniteStepTailNatMassSpace_dvdMonotone
          N M cLow cHigh hLow hStep)).weightedHitMass A ≤
      (cHigh : ℝ) :=
  W.globalLogCapacitySubMarkovShadow_divisorStep_weightedHitMass_le_of_sourceBound
    IOf hIOf s
    (twoStepAsFiniteStepTailNatMassSpace_dvdMonotone N M cLow cHigh hLow hStep)
    hA
    (by exact_mod_cast hLow.trans hStep)
    (twoStepAsFiniteStepTailNatMassSpace_logCapacitySourceMassBound
      N M cLow cHigh hLow hStep)

end PrimePowerWitnessProvider

/--
The canonical exponent-slot Markov shadow at state `s` is compatible with a
source-controlled family whose index is the canonical label set.
-/
theorem canonicalExponentSlotMarkovShadow_providerAt_compatible
    (s : LogCapacityState)
    {M : MassSpace ℕ}
    (F : SourceControlledChainFamily M ℕ)
    (hindex : canonicalExponentSlotLabels s.1 = F.index) :
    (canonicalExponentSlotMarkovShadow.providerAt s).Compatible F := by
  simpa [RealWeightProvider.Compatible] using hindex

/--
Apply the canonical exponent-slot Markov shadow at state `s` to a
source-controlled family whose index is `canonicalExponentSlotLabels s.1`.
-/
noncomputable def canonicalExponentSlotMarkovShadow_applyAtToSourceControlled
    (s : LogCapacityState)
    {M : MassSpace ℕ}
    (F : SourceControlledChainFamily M ℕ)
    (hindex : canonicalExponentSlotLabels s.1 = F.index) :
    RealWeightedPathFamily M ℕ :=
  canonicalExponentSlotMarkovShadow.applyAtToSourceControlled
    s F
    (canonicalExponentSlotMarkovShadow_providerAt_compatible s F hindex)

@[simp] theorem canonicalExponentSlotMarkovShadow_applyAtToSourceControlled_index
    (s : LogCapacityState)
    {M : MassSpace ℕ}
    (F : SourceControlledChainFamily M ℕ)
    (hindex : canonicalExponentSlotLabels s.1 = F.index) :
    (canonicalExponentSlotMarkovShadow_applyAtToSourceControlled s F hindex).index =
      F.index :=
  rfl

/--
Primitive hitting bound for the canonical exponent-slot Markov shadow at state
`s`, applied to an index-compatible source-controlled family.
-/
theorem canonicalExponentSlotMarkovShadow_weightedHitMass_le_const
    (s : LogCapacityState)
    {M : MassSpace ℕ} {A : Finset ℕ}
    (F : SourceControlledChainFamily M ℕ)
    (hindex : canonicalExponentSlotLabels s.1 = F.index)
    (hA : PrimitiveOn A) {C : ℝ} (hC : 0 ≤ C)
    (hsource : ∀ q ∈ F.index, (M.μ (F.source q) : ℝ) ≤ C) :
    (canonicalExponentSlotMarkovShadow_applyAtToSourceControlled s F hindex).weightedHitMass A ≤
      C :=
  canonicalExponentSlotMarkovShadow
    |>.weightedHitMass_le_const_applyAtToSourceControlled
      s F
      (canonicalExponentSlotMarkovShadow_providerAt_compatible s F hindex)
      hA hC hsource

/--
Apply the canonical exponent-slot Markov shadow at state `s` to an external
multi-step divisor path family whose index is the canonical label set.
-/
noncomputable def canonicalExponentSlotMarkovShadow_applyAtToAdjacentDivisorPathFamily
    (s : LogCapacityState)
    {M : MassSpace ℕ}
    (F : AdjacentDivisorPathFamily ℕ)
    (hM : DvdMonotoneMass M)
    (hindex : canonicalExponentSlotLabels s.1 = F.index) :
    RealWeightedPathFamily M ℕ :=
  canonicalExponentSlotMarkovShadow_applyAtToSourceControlled s
    (F.toDvdControlledChainFamily.toSourceControlled hM)
    (by simpa using hindex)

@[simp] theorem canonicalExponentSlotMarkovShadow_applyAtToAdjacentDivisorPathFamily_index
    (s : LogCapacityState)
    {M : MassSpace ℕ}
    (F : AdjacentDivisorPathFamily ℕ)
    (hM : DvdMonotoneMass M)
    (hindex : canonicalExponentSlotLabels s.1 = F.index) :
    (canonicalExponentSlotMarkovShadow_applyAtToAdjacentDivisorPathFamily
      s F hM hindex).index = F.index :=
  rfl

/--
Primitive hitting bound for the canonical exponent-slot Markov shadow on an
external multi-step divisor path family.
-/
theorem canonicalExponentSlotMarkovShadow_adjacentDivisorPathFamily_weightedHitMass_le_const
    (s : LogCapacityState)
    {M : MassSpace ℕ}
    (F : AdjacentDivisorPathFamily ℕ)
    (hM : DvdMonotoneMass M)
    (hindex : canonicalExponentSlotLabels s.1 = F.index)
    {A : Finset ℕ}
    (hA : PrimitiveOn A) {C : ℝ} (hC : 0 ≤ C)
    (hsource : ∀ q ∈ F.index, (M.μ (F.source q) : ℝ) ≤ C) :
    (canonicalExponentSlotMarkovShadow_applyAtToAdjacentDivisorPathFamily
      s F hM hindex).weightedHitMass A ≤ C :=
  canonicalExponentSlotMarkovShadow_weightedHitMass_le_const s
    (F.toDvdControlledChainFamily.toSourceControlled hM)
    (by simpa using hindex)
    hA hC
    (by
      intro q hq
      simpa using hsource q hq)

/--
Primitive hitting bound for a canonical external multi-step divisor path family
whose sources are all the current log-capacity state.
-/
theorem
  canonicalExponentSlotMarkovShadow_adjacentDivisorPathFamily_weightedHitMass_le_of_sourceBound
    (s : LogCapacityState)
    {M : MassSpace ℕ}
    (F : AdjacentDivisorPathFamily ℕ)
    (hM : DvdMonotoneMass M)
    (hindex : canonicalExponentSlotLabels s.1 = F.index)
    (hsource_eq : ∀ q ∈ F.index, F.source q = s.1)
    {A : Finset ℕ}
    (hA : PrimitiveOn A) {C : ℝ} (hC : 0 ≤ C)
    (hsource : LogCapacitySourceMassBound M C) :
    (canonicalExponentSlotMarkovShadow_applyAtToAdjacentDivisorPathFamily
      s F hM hindex).weightedHitMass A ≤ C :=
  canonicalExponentSlotMarkovShadow_adjacentDivisorPathFamily_weightedHitMass_le_const
    s F hM hindex hA hC
    (by
      intro q hq
      simpa [hsource_eq q hq] using hsource s)

/--
Primitive hitting bound for the canonical exponent-slot Markov shadow on a
same-source external multi-step divisor path family with finite step tail
source mass.
-/
theorem
  canonicalExponentSlotMarkovShadow_finiteStepTailAdjacentDivisorPathFamily_weightedHitMass_le
    {ι : Type _} [DecidableEq ι]
    (steps : Finset ι) (threshold : ι → ℕ) (increment : ι → ℚ)
    (hinc : ∀ i ∈ steps, 0 ≤ increment i)
    (s : LogCapacityState)
    (F : AdjacentDivisorPathFamily ℕ)
    (hindex : canonicalExponentSlotLabels s.1 = F.index)
    (hsource_eq : ∀ q ∈ F.index, F.source q = s.1)
    {A : Finset ℕ}
    (hA : PrimitiveOn A) :
    (canonicalExponentSlotMarkovShadow_applyAtToAdjacentDivisorPathFamily
      s F
        (finiteStepTailNatMassSpace_dvdMonotone
          steps threshold increment hinc)
        hindex).weightedHitMass A ≤
      ((Finset.sum steps increment : ℚ) : ℝ) :=
  canonicalExponentSlotMarkovShadow_adjacentDivisorPathFamily_weightedHitMass_le_of_sourceBound
    s F
    (finiteStepTailNatMassSpace_dvdMonotone steps threshold increment hinc)
    hindex hsource_eq hA
    (by exact_mod_cast Finset.sum_nonneg hinc)
    (finiteStepTailNatMassSpace_logCapacitySourceMassBound
      steps threshold increment hinc)

/--
Apply the canonical exponent-slot Markov shadow to the nat-indexed singleton
source-controlled family on `canonicalExponentSlotLabels s.1`.
-/
noncomputable def canonicalExponentSlotMarkovShadow_applyAtToNatSingletonSelf
    (s : LogCapacityState)
    (M : MassSpace ℕ) :
    RealWeightedPathFamily M ℕ :=
  canonicalExponentSlotMarkovShadow_applyAtToSourceControlled s
    (SourceControlledChainFamily.natSingletonSelf
      (M := M) (canonicalExponentSlotLabels s.1))
    rfl

@[simp] theorem canonicalExponentSlotMarkovShadow_applyAtToNatSingletonSelf_index
    (s : LogCapacityState)
    (M : MassSpace ℕ) :
    (canonicalExponentSlotMarkovShadow_applyAtToNatSingletonSelf s M).index =
      canonicalExponentSlotLabels s.1 :=
  rfl

/--
Primitive hitting bound for the canonical exponent-slot Markov shadow on the
nat-indexed singleton source-controlled family.
-/
theorem canonicalExponentSlotMarkovShadow_natSingletonSelf_weightedHitMass_le_const
    (s : LogCapacityState)
    {M : MassSpace ℕ} {A : Finset ℕ}
    (hA : PrimitiveOn A) {C : ℝ} (hC : 0 ≤ C)
    (hsource : ∀ q ∈ canonicalExponentSlotLabels s.1, (M.μ q : ℝ) ≤ C) :
    (canonicalExponentSlotMarkovShadow_applyAtToNatSingletonSelf s M).weightedHitMass A ≤ C :=
  canonicalExponentSlotMarkovShadow_weightedHitMass_le_const s
    (SourceControlledChainFamily.natSingletonSelf
      (M := M) (canonicalExponentSlotLabels s.1))
    rfl hA hC
    (by
      simpa using hsource)

/--
Apply the canonical exponent-slot Markov shadow to the one-step
divisor-descent family `{s.1 / q, s.1}` indexed by the canonical labels.
-/
noncomputable def canonicalExponentSlotMarkovShadow_applyAtToDivisorStep
    (s : LogCapacityState)
    {M : MassSpace ℕ}
    (hM : DvdMonotoneMass M) :
    RealWeightedPathFamily M ℕ :=
  canonicalExponentSlotMarkovShadow_applyAtToSourceControlled s
    (SourceControlledChainFamily.ofDivisorStep hM s.1
      (canonicalExponentSlotLabels s.1)
      (fun q hq => canonicalExponentSlotDivisorTransitionKernel.index_dvd s.1 q hq))
    rfl

@[simp] theorem canonicalExponentSlotMarkovShadow_applyAtToDivisorStep_index
    (s : LogCapacityState)
    {M : MassSpace ℕ}
    (hM : DvdMonotoneMass M) :
    (canonicalExponentSlotMarkovShadow_applyAtToDivisorStep s hM).index =
      canonicalExponentSlotLabels s.1 :=
  rfl

/--
Primitive hitting bound for the canonical exponent-slot Markov shadow on the
one-step divisor-descent family at state `s`.
-/
theorem canonicalExponentSlotMarkovShadow_divisorStep_weightedHitMass_le_const
    (s : LogCapacityState)
    {M : MassSpace ℕ} (hM : DvdMonotoneMass M)
    {A : Finset ℕ}
    (hA : PrimitiveOn A) {C : ℝ} (hC : 0 ≤ C)
    (hsource : (M.μ s.1 : ℝ) ≤ C) :
    (canonicalExponentSlotMarkovShadow_applyAtToDivisorStep s hM).weightedHitMass A ≤ C :=
  canonicalExponentSlotMarkovShadow_weightedHitMass_le_const s
    (SourceControlledChainFamily.ofDivisorStep hM s.1
      (canonicalExponentSlotLabels s.1)
      (fun q hq => canonicalExponentSlotDivisorTransitionKernel.index_dvd s.1 q hq))
    rfl hA hC
    (by
      intro q hq
      simpa using hsource)

/--
Primitive hitting bound for the canonical exponent-slot Markov shadow on the
one-step divisor-descent family, using a statewise source-bound provider.
-/
theorem canonicalExponentSlotMarkovShadow_divisorStep_weightedHitMass_le_of_sourceBound
    (s : LogCapacityState)
    {M : MassSpace ℕ} (hM : DvdMonotoneMass M)
    {A : Finset ℕ}
    (hA : PrimitiveOn A) {C : ℝ} (hC : 0 ≤ C)
    (hsource : LogCapacitySourceMassBound M C) :
    (canonicalExponentSlotMarkovShadow_applyAtToDivisorStep s hM).weightedHitMass A ≤ C :=
  canonicalExponentSlotMarkovShadow_divisorStep_weightedHitMass_le_const
    s hM hA hC (hsource s)

/--
Primitive hitting bound for the canonical exponent-slot Markov shadow on the
one-step divisor-descent family with unit source mass.
-/
theorem canonicalExponentSlotMarkovShadow_unitDivisorStep_weightedHitMass_le_one
    (s : LogCapacityState)
    {A : Finset ℕ}
    (hA : PrimitiveOn A) :
    (canonicalExponentSlotMarkovShadow_applyAtToDivisorStep
      s unitNatMassSpace_dvdMonotone).weightedHitMass A ≤ 1 :=
  canonicalExponentSlotMarkovShadow_divisorStep_weightedHitMass_le_of_sourceBound
    s unitNatMassSpace_dvdMonotone hA
    (by norm_num) unitNatMassSpace_logCapacitySourceMassBound_one

/--
Primitive hitting bound for the canonical exponent-slot Markov shadow on the
one-step divisor-descent family with nonunit indicator source mass.
-/
theorem canonicalExponentSlotMarkovShadow_nonunitDivisorStep_weightedHitMass_le_one
    (s : LogCapacityState)
    {A : Finset ℕ}
    (hA : PrimitiveOn A) :
    (canonicalExponentSlotMarkovShadow_applyAtToDivisorStep
      s nonunitNatMassSpace_dvdMonotone).weightedHitMass A ≤ 1 :=
  canonicalExponentSlotMarkovShadow_divisorStep_weightedHitMass_le_of_sourceBound
    s nonunitNatMassSpace_dvdMonotone hA
    (by norm_num) nonunitNatMassSpace_logCapacitySourceMassBound_one

/--
Primitive hitting bound for the canonical exponent-slot Markov shadow on the
one-step divisor-descent family with tail-support indicator source mass.
-/
theorem canonicalExponentSlotMarkovShadow_tailIndicatorDivisorStep_weightedHitMass_le_one
    (N : ℕ) (s : LogCapacityState)
    {A : Finset ℕ}
    (hA : PrimitiveOn A) :
    (canonicalExponentSlotMarkovShadow_applyAtToDivisorStep
      s (tailIndicatorNatMassSpace_dvdMonotone N)).weightedHitMass A ≤ 1 :=
  canonicalExponentSlotMarkovShadow_divisorStep_weightedHitMass_le_of_sourceBound
    s (tailIndicatorNatMassSpace_dvdMonotone N) hA
    (by norm_num) (tailIndicatorNatMassSpace_logCapacitySourceMassBound_one N)

/--
Primitive hitting bound for the canonical exponent-slot Markov shadow on the
one-step divisor-descent family with scaled tail-support source mass.
-/
theorem canonicalExponentSlotMarkovShadow_scaledTailIndicatorDivisorStep_weightedHitMass_le
    (N : ℕ) (c : ℚ) (hc : 0 ≤ c) (s : LogCapacityState)
    {A : Finset ℕ}
    (hA : PrimitiveOn A) :
    (canonicalExponentSlotMarkovShadow_applyAtToDivisorStep
      s (scaledTailIndicatorNatMassSpace_dvdMonotone N c hc)).weightedHitMass A ≤
      (c : ℝ) :=
  canonicalExponentSlotMarkovShadow_divisorStep_weightedHitMass_le_of_sourceBound
    s (scaledTailIndicatorNatMassSpace_dvdMonotone N c hc) hA
    (by exact_mod_cast hc)
    (scaledTailIndicatorNatMassSpace_logCapacitySourceMassBound N c hc)

/--
Primitive hitting bound for the canonical exponent-slot Markov shadow on the
one-step divisor-descent family with two-step tail-support source mass.
-/
theorem canonicalExponentSlotMarkovShadow_twoStepTailDivisorStep_weightedHitMass_le
    (N M : ℕ) (cLow cHigh : ℚ)
    (hLow : 0 ≤ cLow) (hStep : cLow ≤ cHigh)
    (s : LogCapacityState)
    {A : Finset ℕ}
    (hA : PrimitiveOn A) :
    (canonicalExponentSlotMarkovShadow_applyAtToDivisorStep
      s (twoStepTailNatMassSpace_dvdMonotone
        N M cLow cHigh hLow hStep)).weightedHitMass A ≤
      (cHigh : ℝ) :=
  canonicalExponentSlotMarkovShadow_divisorStep_weightedHitMass_le_of_sourceBound
    s (twoStepTailNatMassSpace_dvdMonotone N M cLow cHigh hLow hStep) hA
    (by exact_mod_cast hLow.trans hStep)
    (twoStepTailNatMassSpace_logCapacitySourceMassBound N M cLow cHigh hLow hStep)

/--
Primitive hitting bound for the canonical exponent-slot Markov shadow on the
one-step divisor-descent family with bounded monotone source mass.
-/
theorem canonicalExponentSlotMarkovShadow_boundedMonotoneDivisorStep_weightedHitMass_le
    (height : ℕ → ℚ) (C : ℚ)
    (hnonneg : ∀ n, 0 ≤ height n)
    (hbound : ∀ n, height n ≤ C)
    (hmono : ∀ ⦃a b : ℕ⦄, a ≤ b → height a ≤ height b)
    (s : LogCapacityState)
    {A : Finset ℕ}
    (hA : PrimitiveOn A) :
    (canonicalExponentSlotMarkovShadow_applyAtToDivisorStep
      s (boundedMonotoneNatMassSpace_dvdMonotone
        height C hnonneg hbound hmono)).weightedHitMass A ≤
      (C : ℝ) := by
  have hC : 0 ≤ C := (hnonneg 0).trans (hbound 0)
  exact
    canonicalExponentSlotMarkovShadow_divisorStep_weightedHitMass_le_of_sourceBound
      s
      (boundedMonotoneNatMassSpace_dvdMonotone height C hnonneg hbound hmono)
      hA
      (by exact_mod_cast hC)
      (boundedMonotoneNatMassSpace_logCapacitySourceMassBound height C hnonneg hbound)

/--
Primitive hitting bound for the canonical exponent-slot Markov shadow on the
one-step divisor-descent family with finite step tail source mass.
-/
theorem canonicalExponentSlotMarkovShadow_finiteStepTailDivisorStep_weightedHitMass_le
    {ι : Type _} [DecidableEq ι]
    (steps : Finset ι) (threshold : ι → ℕ) (increment : ι → ℚ)
    (hinc : ∀ i ∈ steps, 0 ≤ increment i)
    (s : LogCapacityState)
    {A : Finset ℕ}
    (hA : PrimitiveOn A) :
    (canonicalExponentSlotMarkovShadow_applyAtToDivisorStep
      s (finiteStepTailNatMassSpace_dvdMonotone
        steps threshold increment hinc)).weightedHitMass A ≤
      ((Finset.sum steps increment : ℚ) : ℝ) :=
  canonicalExponentSlotMarkovShadow_divisorStep_weightedHitMass_le_of_sourceBound
    s (finiteStepTailNatMassSpace_dvdMonotone steps threshold increment hinc) hA
    (by exact_mod_cast Finset.sum_nonneg hinc)
    (finiteStepTailNatMassSpace_logCapacitySourceMassBound
      steps threshold increment hinc)

/--
Primitive hitting bound for the canonical exponent-slot Markov shadow using
the two-step tail mass through the finite-step interface.
-/
theorem canonicalExponentSlotMarkovShadow_twoStepAsFiniteStepTailDivisorStep_weightedHitMass_le
    (N M : ℕ) (cLow cHigh : ℚ)
    (hLow : 0 ≤ cLow) (hStep : cLow ≤ cHigh)
    (s : LogCapacityState)
    {A : Finset ℕ}
    (hA : PrimitiveOn A) :
    (canonicalExponentSlotMarkovShadow_applyAtToDivisorStep
      s (twoStepAsFiniteStepTailNatMassSpace_dvdMonotone
        N M cLow cHigh hLow hStep)).weightedHitMass A ≤
      (cHigh : ℝ) :=
  canonicalExponentSlotMarkovShadow_divisorStep_weightedHitMass_le_of_sourceBound
    s
    (twoStepAsFiniteStepTailNatMassSpace_dvdMonotone N M cLow cHigh hLow hStep)
    hA
    (by exact_mod_cast hLow.trans hStep)
    (twoStepAsFiniteStepTailNatMassSpace_logCapacitySourceMassBound
      N M cLow cHigh hLow hStep)

end DkMath.NumberTheory.PrimitiveSet
