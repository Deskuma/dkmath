/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PrimitiveSet.WeightedPathFamily

#print "file: DkMath.NumberTheory.PrimitiveSet.WeightProvider"

namespace DkMath.NumberTheory.PrimitiveSet

open DkMath.CosmicFormula.Mass

/--
A finite provider of nonnegative rational weights.

This separates the source of weights from the path/source-control structure
that will consume them.  Markov kernels can later provide instances of this
finite carrier without changing `WeightedPathFamily`.
-/
structure WeightProvider (ι : Type _) [DecidableEq ι] where
  index : Finset ι
  weight : ι → ℚ
  weight_nonneg : ∀ i ∈ index, 0 ≤ weight i

namespace WeightProvider

/-- Total finite weight carried by a provider. -/
def totalWeight
    {ι : Type _} [DecidableEq ι] (P : WeightProvider ι) : ℚ :=
  P.index.sum fun i => P.weight i

/-- The provider is normalized as a finite sub-probability. -/
def SubProbability
    {ι : Type _} [DecidableEq ι] (P : WeightProvider ι) : Prop :=
  P.totalWeight ≤ 1

/-- Total provider weight is nonnegative. -/
theorem totalWeight_nonneg
    {ι : Type _} [DecidableEq ι] (P : WeightProvider ι) :
    0 ≤ P.totalWeight := by
  classical
  unfold totalWeight
  exact Finset.sum_nonneg fun i hi => P.weight_nonneg i hi

/--
A provider is compatible with a source-controlled family when they use the same
finite index set.
-/
def Compatible
    {ι : Type _} [DecidableEq ι] {M : MassSpace ℕ}
    (P : WeightProvider ι) (F : SourceControlledChainFamily M ι) : Prop :=
  P.index = F.index

/-- Apply compatible provided weights to a source-controlled chain family. -/
def applyToSourceControlled
    {ι : Type _} [DecidableEq ι] {M : MassSpace ℕ}
    (P : WeightProvider ι) (F : SourceControlledChainFamily M ι)
    (hcompat : P.Compatible F) :
    WeightedPathFamily M ι :=
  WeightedPathFamily.ofSourceControlled F P.weight
    (by
      intro i hi
      exact P.weight_nonneg i (by simpa [Compatible] using hcompat.symm ▸ hi))

@[simp] theorem applyToSourceControlled_index
    {ι : Type _} [DecidableEq ι] {M : MassSpace ℕ}
    (P : WeightProvider ι) (F : SourceControlledChainFamily M ι)
    (hcompat : P.Compatible F) :
    (P.applyToSourceControlled F hcompat).index = F.index := rfl

@[simp] theorem applyToSourceControlled_weight
    {ι : Type _} [DecidableEq ι] {M : MassSpace ℕ}
    (P : WeightProvider ι) (F : SourceControlledChainFamily M ι)
    (hcompat : P.Compatible F) :
    (P.applyToSourceControlled F hcompat).weight = P.weight := rfl

/-- Compatible sub-probability providers yield sub-probability weighted families. -/
theorem applyToSourceControlled_weightSubProbability
    {ι : Type _} [DecidableEq ι] {M : MassSpace ℕ}
    (P : WeightProvider ι) (F : SourceControlledChainFamily M ι)
    (hcompat : P.Compatible F) (hprob : P.SubProbability) :
    (P.applyToSourceControlled F hcompat).WeightSubProbability := by
  unfold WeightedPathFamily.WeightSubProbability WeightedPathFamily.totalWeight
  dsimp [applyToSourceControlled, WeightedPathFamily.ofSourceControlled]
  simpa [SubProbability, totalWeight, Compatible] using hcompat ▸ hprob

/--
Provider-level hit mass bound under sub-probability normalization and a uniform
source-mass bound.
-/
theorem weightedHitMass_le_const_of_subprob_applyToSourceControlled
    {ι : Type _} [DecidableEq ι] {M : MassSpace ℕ} {S : Finset ℕ}
    (P : WeightProvider ι) (F : SourceControlledChainFamily M ι)
    (hcompat : P.Compatible F)
    (hS : PrimitiveOn S) {C : ℚ} (hC : 0 ≤ C)
    (hprob : P.SubProbability)
    (hsource : ∀ i ∈ F.index, M.μ (F.source i) ≤ C) :
    (P.applyToSourceControlled F hcompat).weightedHitMass S ≤ C := by
  exact (P.applyToSourceControlled F hcompat).weightedHitMass_le_const_of_subprob
    hS hC
    (P.applyToSourceControlled_weightSubProbability F hcompat hprob)
    hsource

end WeightProvider

namespace ErdosFinitePrimitiveInput

/-- Apply a compatible weight provider to the branch-controlled finite route. -/
def providerBranchPrimePathFamily
    {x : ℕ} {ι : Type _} [DecidableEq ι]
    (M : MassSpace ℕ) (B : Branching ℕ) [SubConservative M B]
    (I : ErdosFinitePrimitiveInput x)
    (F : AdjacentBranchPrimePathFamily ι B)
    (P : WeightProvider ι)
    (hcompat : P.Compatible (I.branchPrimePathFamilySourceControlled M B F)) :
    WeightedPathFamily M ι :=
  P.applyToSourceControlled
    (I.branchPrimePathFamilySourceControlled M B F) hcompat

/--
Provider-level branch route bound under sub-probability weights and a uniform
source-mass bound.
-/
theorem providerBranchPrimePathFamily_hitMass_le_const_of_subprob
    {x : ℕ} {ι : Type _} [DecidableEq ι]
    {M : MassSpace ℕ} {B : Branching ℕ} [SubConservative M B]
    (I : ErdosFinitePrimitiveInput x)
    (F : AdjacentBranchPrimePathFamily ι B)
    (P : WeightProvider ι)
    (hcompat : P.Compatible (I.branchPrimePathFamilySourceControlled M B F))
    {C : ℚ} (hC : 0 ≤ C)
    (hprob : P.SubProbability)
    (hsource :
      ∀ i ∈ (I.branchPrimePathFamilySourceControlled M B F).index,
        M.μ ((I.branchPrimePathFamilySourceControlled M B F).source i) ≤ C) :
    (I.providerBranchPrimePathFamily M B F P hcompat).weightedHitMass
      I.support ≤ C := by
  exact P.weightedHitMass_le_const_of_subprob_applyToSourceControlled
    (I.branchPrimePathFamilySourceControlled M B F)
    hcompat I.primitive hC hprob hsource

end ErdosFinitePrimitiveInput

/-- A Bool-indexed sub-probability weight provider for examples. -/
def sampleBoolSubprobWeightProvider : WeightProvider Bool where
  index := {false, true}
  weight := sampleBoolSubprobPathWeight
  weight_nonneg := by
    intro b _hb
    cases b <;> norm_num [sampleBoolSubprobPathWeight]

/-- The Bool sample provider has total weight at most `1`. -/
theorem sampleBoolSubprobWeightProvider_subProbability :
    sampleBoolSubprobWeightProvider.SubProbability := by
  norm_num [WeightProvider.SubProbability, WeightProvider.totalWeight,
    sampleBoolSubprobWeightProvider, sampleBoolSubprobPathWeight]

/--
Concrete provider sample: provider-supplied weights give the same weighted
branch hit mass bound by `1`.
-/
theorem erdosFinitePrimitiveInput_two_five_providerBranch_hitMass_le_one :
    (erdosFinitePrimitiveInput_two_five.providerBranchPrimePathFamily
      unitNatMassSpace sampleBranching_eight_nine_paths
      sampleAdjacentBranchPrimePathBoolFamily sampleBoolSubprobWeightProvider
      (by
        simp [WeightProvider.Compatible,
          sampleBoolSubprobWeightProvider,
          ErdosFinitePrimitiveInput.branchPrimePathFamilySourceControlled,
          sampleAdjacentBranchPrimePathBoolFamily])).weightedHitMass
      erdosFinitePrimitiveInput_two_five.support ≤ 1 := by
  exact erdosFinitePrimitiveInput_two_five
    |>.providerBranchPrimePathFamily_hitMass_le_const_of_subprob
      sampleAdjacentBranchPrimePathBoolFamily sampleBoolSubprobWeightProvider
      (by
        simp [WeightProvider.Compatible,
          sampleBoolSubprobWeightProvider,
          ErdosFinitePrimitiveInput.branchPrimePathFamilySourceControlled,
          sampleAdjacentBranchPrimePathBoolFamily])
      (by norm_num)
      sampleBoolSubprobWeightProvider_subProbability
      (by
        intro i _hi
        rfl)

end DkMath.NumberTheory.PrimitiveSet
