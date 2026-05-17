/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PrimitiveSet.ShadowHittingBridge
import DkMath.NumberTheory.PrimitiveSet.DescentBridge
import DkMath.NumberTheory.PrimitiveSet.FullExponentSlotCanonical

#print "file: DkMath.NumberTheory.PrimitiveSet.LogCapacityHittingBridge"

namespace DkMath.NumberTheory.PrimitiveSet

open DkMath.CosmicFormula.Mass

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

end DkMath.NumberTheory.PrimitiveSet
