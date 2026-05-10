/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PrimitiveSet.WeightProvider

#print "file: DkMath.NumberTheory.PrimitiveSet.FiniteKernel"

namespace DkMath.NumberTheory.PrimitiveSet

open DkMath.CosmicFormula.Mass

/--
A finite kernel assigns to each state a finite nonnegative rational weight
provider on a common index type.

This is still a finite algebraic skeleton: no analytic weight, logarithm, or
von Mangoldt factor is introduced here.
-/
structure FiniteKernel (σ ι : Type _) [DecidableEq ι] where
  index : σ → Finset ι
  weight : σ → ι → ℚ
  weight_nonneg : ∀ s i, i ∈ index s → 0 ≤ weight s i

namespace FiniteKernel

/-- The finite weight provider emitted by the kernel at state `s`. -/
def providerAt
    {σ ι : Type _} [DecidableEq ι]
    (K : FiniteKernel σ ι) (s : σ) :
    WeightProvider ι where
  index := K.index s
  weight := K.weight s
  weight_nonneg := K.weight_nonneg s

/-- Total kernel weight at a state. -/
def totalWeightAt
    {σ ι : Type _} [DecidableEq ι]
    (K : FiniteKernel σ ι) (s : σ) : ℚ :=
  (K.providerAt s).totalWeight

/-- The kernel is sub-probability normalized at every state. -/
def SubProbability
    {σ ι : Type _} [DecidableEq ι]
    (K : FiniteKernel σ ι) : Prop :=
  ∀ s, (K.providerAt s).SubProbability

/-- Sub-probability kernels emit sub-probability providers. -/
theorem providerAt_subProbability
    {σ ι : Type _} [DecidableEq ι]
    (K : FiniteKernel σ ι) (hK : K.SubProbability) (s : σ) :
    (K.providerAt s).SubProbability :=
  hK s

/-- Total kernel weight is nonnegative at every state. -/
theorem totalWeightAt_nonneg
    {σ ι : Type _} [DecidableEq ι]
    (K : FiniteKernel σ ι) (s : σ) :
    0 ≤ K.totalWeightAt s :=
  (K.providerAt s).totalWeight_nonneg

/--
Apply the provider emitted at `s` to a compatible source-controlled family.
-/
def applyAtToSourceControlled
    {σ ι : Type _} [DecidableEq ι] {M : MassSpace ℕ}
    (K : FiniteKernel σ ι) (s : σ)
    (F : SourceControlledChainFamily M ι)
    (hcompat : (K.providerAt s).Compatible F) :
    WeightedPathFamily M ι :=
  (K.providerAt s).applyToSourceControlled F hcompat

/--
Kernel-level finite hit mass bound under sub-probability normalization and a
uniform source-mass bound.
-/
theorem weightedHitMass_le_const_of_subprob_applyAtToSourceControlled
    {σ ι : Type _} [DecidableEq ι] {M : MassSpace ℕ} {S : Finset ℕ}
    (K : FiniteKernel σ ι) (hK : K.SubProbability) (s : σ)
    (F : SourceControlledChainFamily M ι)
    (hcompat : (K.providerAt s).Compatible F)
    (hS : PrimitiveOn S) {C : ℚ} (hC : 0 ≤ C)
    (hsource : ∀ i ∈ F.index, M.μ (F.source i) ≤ C) :
    (K.applyAtToSourceControlled s F hcompat).weightedHitMass S ≤ C := by
  exact (K.providerAt s).weightedHitMass_le_const_of_subprob_applyToSourceControlled
    F hcompat hS hC (K.providerAt_subProbability hK s) hsource

end FiniteKernel

namespace ErdosFinitePrimitiveInput

/-- Apply a finite kernel state to the branch-controlled finite route. -/
def kernelBranchPrimePathFamilyAt
    {x : ℕ} {σ ι : Type _} [DecidableEq ι]
    (M : MassSpace ℕ) (B : Branching ℕ) [SubConservative M B]
    (I : ErdosFinitePrimitiveInput x)
    (F : AdjacentBranchPrimePathFamily ι B)
    (K : FiniteKernel σ ι) (s : σ)
    (hcompat :
      (K.providerAt s).Compatible
        (I.branchPrimePathFamilySourceControlled M B F)) :
    WeightedPathFamily M ι :=
  K.applyAtToSourceControlled s
    (I.branchPrimePathFamilySourceControlled M B F) hcompat

/--
Kernel-level branch route bound under sub-probability weights and a uniform
source-mass bound.
-/
theorem kernelBranchPrimePathFamilyAt_hitMass_le_const_of_subprob
    {x : ℕ} {σ ι : Type _} [DecidableEq ι]
    {M : MassSpace ℕ} {B : Branching ℕ} [SubConservative M B]
    (I : ErdosFinitePrimitiveInput x)
    (F : AdjacentBranchPrimePathFamily ι B)
    (K : FiniteKernel σ ι) (hK : K.SubProbability) (s : σ)
    (hcompat :
      (K.providerAt s).Compatible
        (I.branchPrimePathFamilySourceControlled M B F))
    {C : ℚ} (hC : 0 ≤ C)
    (hsource :
      ∀ i ∈ (I.branchPrimePathFamilySourceControlled M B F).index,
        M.μ ((I.branchPrimePathFamilySourceControlled M B F).source i) ≤ C) :
    (I.kernelBranchPrimePathFamilyAt M B F K s hcompat).weightedHitMass
      I.support ≤ C := by
  exact K.weightedHitMass_le_const_of_subprob_applyAtToSourceControlled hK s
    (I.branchPrimePathFamilySourceControlled M B F)
    hcompat I.primitive hC hsource

/-- Apply a finite kernel state to the prime-path-family finite route. -/
def kernelPrimePathFamilyAt
    {x : ℕ} {σ ι : Type _} [DecidableEq ι]
    (M : MassSpace ℕ)
    (I : ErdosFinitePrimitiveInput x)
    (F : AdjacentPrimePathFamily ι)
    (hM : DvdMonotoneMass M)
    (K : FiniteKernel σ ι) (s : σ)
    (hcompat :
      (K.providerAt s).Compatible
        (I.primePathFamilySourceControlled M F hM)) :
    WeightedPathFamily M ι :=
  K.applyAtToSourceControlled s
    (I.primePathFamilySourceControlled M F hM) hcompat

/--
Kernel-level prime-path-family route bound under sub-probability weights and a
uniform source-mass bound.
-/
theorem kernelPrimePathFamilyAt_hitMass_le_const_of_subprob
    {x : ℕ} {σ ι : Type _} [DecidableEq ι]
    {M : MassSpace ℕ}
    (I : ErdosFinitePrimitiveInput x)
    (F : AdjacentPrimePathFamily ι)
    (hM : DvdMonotoneMass M)
    (K : FiniteKernel σ ι) (hK : K.SubProbability) (s : σ)
    (hcompat :
      (K.providerAt s).Compatible
        (I.primePathFamilySourceControlled M F hM))
    {C : ℚ} (hC : 0 ≤ C)
    (hsource :
      ∀ i ∈ (I.primePathFamilySourceControlled M F hM).index,
        M.μ ((I.primePathFamilySourceControlled M F hM).source i) ≤ C) :
    (I.kernelPrimePathFamilyAt M F hM K s hcompat).weightedHitMass
      I.support ≤ C := by
  exact K.weightedHitMass_le_const_of_subprob_applyAtToSourceControlled hK s
    (I.primePathFamilySourceControlled M F hM)
    hcompat I.primitive hC hsource

end ErdosFinitePrimitiveInput

/-- A sample finite kernel with the Bool sub-probability weights at every state. -/
def sampleUnitFiniteKernel : FiniteKernel Unit Bool where
  index := fun _ => {false, true}
  weight := fun _ => sampleBoolSubprobPathWeight
  weight_nonneg := by
    intro _ b _hb
    cases b <;> norm_num [sampleBoolSubprobPathWeight]

/-- The sample finite kernel is sub-probability normalized. -/
theorem sampleUnitFiniteKernel_subProbability :
    sampleUnitFiniteKernel.SubProbability := by
  intro s
  cases s
  norm_num [FiniteKernel.providerAt, WeightProvider.SubProbability,
    WeightProvider.totalWeight, sampleUnitFiniteKernel, sampleBoolSubprobPathWeight]

/--
Concrete kernel sample: kernel-supplied weights give the branch hit mass bound
by `1`.
-/
theorem erdosFinitePrimitiveInput_two_five_kernelBranch_hitMass_le_one :
    (erdosFinitePrimitiveInput_two_five.kernelBranchPrimePathFamilyAt
      unitNatMassSpace sampleBranching_eight_nine_paths
      sampleAdjacentBranchPrimePathBoolFamily sampleUnitFiniteKernel ()
      (by
        simp [WeightProvider.Compatible, FiniteKernel.providerAt,
          sampleUnitFiniteKernel,
          ErdosFinitePrimitiveInput.branchPrimePathFamilySourceControlled,
          sampleAdjacentBranchPrimePathBoolFamily])).weightedHitMass
      erdosFinitePrimitiveInput_two_five.support ≤ 1 := by
  exact erdosFinitePrimitiveInput_two_five
    |>.kernelBranchPrimePathFamilyAt_hitMass_le_const_of_subprob
      sampleAdjacentBranchPrimePathBoolFamily sampleUnitFiniteKernel
      sampleUnitFiniteKernel_subProbability ()
      (by
        simp [WeightProvider.Compatible, FiniteKernel.providerAt,
          sampleUnitFiniteKernel,
          ErdosFinitePrimitiveInput.branchPrimePathFamilySourceControlled,
          sampleAdjacentBranchPrimePathBoolFamily])
      (by norm_num)
      (by
        intro i _hi
        rfl)

/--
Concrete kernel sample: kernel-supplied weights also give the prime-path-family
hit mass bound by `1`.
-/
theorem erdosFinitePrimitiveInput_two_five_kernelPrimePath_hitMass_le_one :
    (erdosFinitePrimitiveInput_two_five.kernelPrimePathFamilyAt
      unitNatMassSpace sampleAdjacentPrimePathBoolFamily
      unitNatMassSpace_dvdMonotone sampleUnitFiniteKernel ()
      (by
        simp [WeightProvider.Compatible, FiniteKernel.providerAt,
          sampleUnitFiniteKernel,
          ErdosFinitePrimitiveInput.primePathFamilySourceControlled,
          sampleAdjacentPrimePathBoolFamily])).weightedHitMass
      erdosFinitePrimitiveInput_two_five.support ≤ 1 := by
  exact erdosFinitePrimitiveInput_two_five
    |>.kernelPrimePathFamilyAt_hitMass_le_const_of_subprob
      sampleAdjacentPrimePathBoolFamily unitNatMassSpace_dvdMonotone
      sampleUnitFiniteKernel sampleUnitFiniteKernel_subProbability ()
      (by
        simp [WeightProvider.Compatible, FiniteKernel.providerAt,
          sampleUnitFiniteKernel,
          ErdosFinitePrimitiveInput.primePathFamilySourceControlled,
          sampleAdjacentPrimePathBoolFamily])
      (by norm_num)
      (by
        intro i _hi
        rfl)

end DkMath.NumberTheory.PrimitiveSet
