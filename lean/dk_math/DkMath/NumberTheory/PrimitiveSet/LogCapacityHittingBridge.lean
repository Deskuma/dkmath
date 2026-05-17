/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PrimitiveSet.ShadowHittingBridge
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

end DkMath.NumberTheory.PrimitiveSet
