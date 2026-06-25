/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PrimitiveSet.FiniteKernel

#print "file: DkMath.NumberTheory.PrimitiveSet.FiniteTransitionKernel"

namespace DkMath.NumberTheory.PrimitiveSet

open DkMath.CosmicFormula.Mass

/--
A finite transition kernel.

At each state `s`, the finite index set selects possible transition labels.
Each label has a next state and a nonnegative rational weight.  This is still
an algebraic finite skeleton: no analytic weight formula is imposed here.
-/
structure FiniteTransitionKernel (σ ι : Type _) [DecidableEq ι] where
  index : σ → Finset ι
  next : σ → ι → σ
  weight : σ → ι → ℚ
  weight_nonneg : ∀ s i, i ∈ index s → 0 ≤ weight s i

namespace FiniteTransitionKernel

/-- Forget transition targets and keep only the finite weight kernel. -/
def toFiniteKernel
    {σ ι : Type _} [DecidableEq ι]
    (T : FiniteTransitionKernel σ ι) :
    FiniteKernel σ ι where
  index := T.index
  weight := T.weight
  weight_nonneg := T.weight_nonneg

@[simp] theorem toFiniteKernel_index
    {σ ι : Type _} [DecidableEq ι]
    (T : FiniteTransitionKernel σ ι) :
    T.toFiniteKernel.index = T.index := rfl

@[simp] theorem toFiniteKernel_weight
    {σ ι : Type _} [DecidableEq ι]
    (T : FiniteTransitionKernel σ ι) :
    T.toFiniteKernel.weight = T.weight := rfl

/-- The finite weight provider emitted at state `s`. -/
def providerAt
    {σ ι : Type _} [DecidableEq ι]
    (T : FiniteTransitionKernel σ ι) (s : σ) :
    WeightProvider ι :=
  T.toFiniteKernel.providerAt s

/-- Total transition weight at state `s`. -/
def totalWeightAt
    {σ ι : Type _} [DecidableEq ι]
    (T : FiniteTransitionKernel σ ι) (s : σ) : ℚ :=
  T.toFiniteKernel.totalWeightAt s

/-- The transition kernel is sub-probability normalized at every state. -/
def SubProbability
    {σ ι : Type _} [DecidableEq ι]
    (T : FiniteTransitionKernel σ ι) : Prop :=
  T.toFiniteKernel.SubProbability

/-- Sub-probability transition kernels emit sub-probability providers. -/
theorem providerAt_subProbability
    {σ ι : Type _} [DecidableEq ι]
    (T : FiniteTransitionKernel σ ι) (hT : T.SubProbability) (s : σ) :
    (T.providerAt s).SubProbability :=
  T.toFiniteKernel.providerAt_subProbability hT s

/-- Compatibility with a source-controlled family at state `s`. -/
def CompatibleAt
    {σ ι : Type _} [DecidableEq ι] {M : MassSpace ℕ}
    (T : FiniteTransitionKernel σ ι) (s : σ)
    (F : SourceControlledChainFamily M ι) : Prop :=
  T.toFiniteKernel.CompatibleAt s F

/-- Expanded form of transition-kernel compatibility. -/
theorem compatibleAt_iff_index_eq
    {σ ι : Type _} [DecidableEq ι] {M : MassSpace ℕ}
    (T : FiniteTransitionKernel σ ι) (s : σ)
    (F : SourceControlledChainFamily M ι) :
    T.CompatibleAt s F ↔ T.index s = F.index := by
  rfl

/-- Apply transition-kernel weights at state `s` to a source-controlled family. -/
def applyAtToSourceControlled
    {σ ι : Type _} [DecidableEq ι] {M : MassSpace ℕ}
    (T : FiniteTransitionKernel σ ι) (s : σ)
    (F : SourceControlledChainFamily M ι)
    (hcompat : T.CompatibleAt s F) :
    WeightedPathFamily M ι :=
  T.toFiniteKernel.applyAtToSourceControlledOfCompatibleAt s F hcompat

/--
Transition-kernel finite hit mass bound under sub-probability normalization and
a uniform source-mass bound.
-/
theorem weightedHitMass_le_const_of_subprob_applyAtToSourceControlled
    {σ ι : Type _} [DecidableEq ι] {M : MassSpace ℕ} {S : Finset ℕ}
    (T : FiniteTransitionKernel σ ι) (hT : T.SubProbability) (s : σ)
    (F : SourceControlledChainFamily M ι)
    (hcompat : T.CompatibleAt s F)
    (hS : PrimitiveOn S) {C : ℚ} (hC : 0 ≤ C)
    (hsource : ∀ i ∈ F.index, M.μ (F.source i) ≤ C) :
    (T.applyAtToSourceControlled s F hcompat).weightedHitMass S ≤ C := by
  exact T.toFiniteKernel
    |>.weightedHitMass_le_const_of_subprob_applyAtToSourceControlledOfCompatibleAt
      hT s F hcompat hS hC hsource

end FiniteTransitionKernel

namespace ErdosFinitePrimitiveInput

/-- Apply a finite transition kernel state to the branch-controlled route. -/
def transitionBranchPrimePathFamilyAt
    {x : ℕ} {σ ι : Type _} [DecidableEq ι]
    (M : MassSpace ℕ) (B : Branching ℕ) [SubConservative M B]
    (I : ErdosFinitePrimitiveInput x)
    (F : AdjacentBranchPrimePathFamily ι B)
    (T : FiniteTransitionKernel σ ι) (s : σ)
    (hcompat :
      T.CompatibleAt s (I.branchPrimePathFamilySourceControlled M B F)) :
    WeightedPathFamily M ι :=
  T.applyAtToSourceControlled s
    (I.branchPrimePathFamilySourceControlled M B F) hcompat

/--
Transition-kernel branch route bound under sub-probability weights and a uniform
source-mass bound.
-/
theorem transitionBranchPrimePathFamilyAt_hitMass_le_const_of_subprob
    {x : ℕ} {σ ι : Type _} [DecidableEq ι]
    {M : MassSpace ℕ} {B : Branching ℕ} [SubConservative M B]
    (I : ErdosFinitePrimitiveInput x)
    (F : AdjacentBranchPrimePathFamily ι B)
    (T : FiniteTransitionKernel σ ι) (hT : T.SubProbability) (s : σ)
    (hcompat :
      T.CompatibleAt s (I.branchPrimePathFamilySourceControlled M B F))
    {C : ℚ} (hC : 0 ≤ C)
    (hsource :
      ∀ i ∈ (I.branchPrimePathFamilySourceControlled M B F).index,
        M.μ ((I.branchPrimePathFamilySourceControlled M B F).source i) ≤ C) :
    (I.transitionBranchPrimePathFamilyAt M B F T s hcompat).weightedHitMass
      I.support ≤ C := by
  exact T.weightedHitMass_le_const_of_subprob_applyAtToSourceControlled hT s
    (I.branchPrimePathFamilySourceControlled M B F)
    hcompat I.primitive hC hsource

/-- Apply a finite transition kernel state to the prime-path-family route. -/
def transitionPrimePathFamilyAt
    {x : ℕ} {σ ι : Type _} [DecidableEq ι]
    (M : MassSpace ℕ)
    (I : ErdosFinitePrimitiveInput x)
    (F : AdjacentPrimePathFamily ι)
    (hM : DvdMonotoneMass M)
    (T : FiniteTransitionKernel σ ι) (s : σ)
    (hcompat :
      T.CompatibleAt s (I.primePathFamilySourceControlled M F hM)) :
    WeightedPathFamily M ι :=
  T.applyAtToSourceControlled s
    (I.primePathFamilySourceControlled M F hM) hcompat

/--
Transition-kernel prime-path-family route bound under sub-probability weights
and a uniform source-mass bound.
-/
theorem transitionPrimePathFamilyAt_hitMass_le_const_of_subprob
    {x : ℕ} {σ ι : Type _} [DecidableEq ι]
    {M : MassSpace ℕ}
    (I : ErdosFinitePrimitiveInput x)
    (F : AdjacentPrimePathFamily ι)
    (hM : DvdMonotoneMass M)
    (T : FiniteTransitionKernel σ ι) (hT : T.SubProbability) (s : σ)
    (hcompat :
      T.CompatibleAt s (I.primePathFamilySourceControlled M F hM))
    {C : ℚ} (hC : 0 ≤ C)
    (hsource :
      ∀ i ∈ (I.primePathFamilySourceControlled M F hM).index,
        M.μ ((I.primePathFamilySourceControlled M F hM).source i) ≤ C) :
    (I.transitionPrimePathFamilyAt M F hM T s hcompat).weightedHitMass
      I.support ≤ C := by
  exact T.weightedHitMass_le_const_of_subprob_applyAtToSourceControlled hT s
    (I.primePathFamilySourceControlled M F hM)
    hcompat I.primitive hC hsource

end ErdosFinitePrimitiveInput

/-- A sample transition kernel with a single unit state and Bool labels. -/
def sampleUnitTransitionKernel : FiniteTransitionKernel Unit Bool where
  index := fun _ => {false, true}
  next := fun _ _ => ()
  weight := fun _ => sampleBoolSubprobPathWeight
  weight_nonneg := by
    intro _ b _hb
    cases b <;> norm_num [sampleBoolSubprobPathWeight]

/-- The sample transition kernel is sub-probability normalized. -/
theorem sampleUnitTransitionKernel_subProbability :
    sampleUnitTransitionKernel.SubProbability := by
  intro s
  cases s
  norm_num [FiniteTransitionKernel.SubProbability,
    FiniteTransitionKernel.toFiniteKernel, FiniteKernel.providerAt,
    WeightProvider.SubProbability, WeightProvider.totalWeight,
    sampleUnitTransitionKernel, sampleBoolSubprobPathWeight]

/-- Concrete sample: transition-kernel weights give branch hit mass bound by `1`. -/
theorem erdosFinitePrimitiveInput_two_five_transitionBranch_hitMass_le_one :
    (erdosFinitePrimitiveInput_two_five.transitionBranchPrimePathFamilyAt
      unitNatMassSpace sampleBranching_eight_nine_paths
      sampleAdjacentBranchPrimePathBoolFamily sampleUnitTransitionKernel ()
      (by
        simp [FiniteTransitionKernel.CompatibleAt,
          FiniteKernel.CompatibleAt,
          WeightProvider.Compatible,
          FiniteTransitionKernel.toFiniteKernel,
          FiniteKernel.providerAt,
          sampleUnitTransitionKernel,
          ErdosFinitePrimitiveInput.branchPrimePathFamilySourceControlled,
          sampleAdjacentBranchPrimePathBoolFamily])).weightedHitMass
      erdosFinitePrimitiveInput_two_five.support ≤ 1 := by
  exact erdosFinitePrimitiveInput_two_five
    |>.transitionBranchPrimePathFamilyAt_hitMass_le_const_of_subprob
      sampleAdjacentBranchPrimePathBoolFamily sampleUnitTransitionKernel
      sampleUnitTransitionKernel_subProbability ()
      (by
        simp [FiniteTransitionKernel.CompatibleAt,
          FiniteKernel.CompatibleAt,
          WeightProvider.Compatible,
          FiniteTransitionKernel.toFiniteKernel,
          FiniteKernel.providerAt,
          sampleUnitTransitionKernel,
          ErdosFinitePrimitiveInput.branchPrimePathFamilySourceControlled,
          sampleAdjacentBranchPrimePathBoolFamily])
      (by norm_num)
      (by
        intro i _hi
        rfl)

/--
Concrete sample: transition-kernel weights also give prime-path-family hit mass
bound by `1`.
-/
theorem erdosFinitePrimitiveInput_two_five_transitionPrimePath_hitMass_le_one :
    (erdosFinitePrimitiveInput_two_five.transitionPrimePathFamilyAt
      unitNatMassSpace sampleAdjacentPrimePathBoolFamily
      unitNatMassSpace_dvdMonotone sampleUnitTransitionKernel ()
      (by
        simp [FiniteTransitionKernel.CompatibleAt,
          FiniteKernel.CompatibleAt,
          WeightProvider.Compatible,
          FiniteTransitionKernel.toFiniteKernel,
          FiniteKernel.providerAt,
          sampleUnitTransitionKernel,
          ErdosFinitePrimitiveInput.primePathFamilySourceControlled,
          sampleAdjacentPrimePathBoolFamily])).weightedHitMass
      erdosFinitePrimitiveInput_two_five.support ≤ 1 := by
  exact erdosFinitePrimitiveInput_two_five
    |>.transitionPrimePathFamilyAt_hitMass_le_const_of_subprob
      sampleAdjacentPrimePathBoolFamily unitNatMassSpace_dvdMonotone
      sampleUnitTransitionKernel sampleUnitTransitionKernel_subProbability ()
      (by
        simp [FiniteTransitionKernel.CompatibleAt,
          FiniteKernel.CompatibleAt,
          WeightProvider.Compatible,
          FiniteTransitionKernel.toFiniteKernel,
          FiniteKernel.providerAt,
          sampleUnitTransitionKernel,
          ErdosFinitePrimitiveInput.primePathFamilySourceControlled,
          sampleAdjacentPrimePathBoolFamily])
      (by norm_num)
      (by
        intro i _hi
        rfl)

end DkMath.NumberTheory.PrimitiveSet
