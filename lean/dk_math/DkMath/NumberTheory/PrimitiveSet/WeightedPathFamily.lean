/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PrimitiveSet.ErdosFinite

#print "file: DkMath.NumberTheory.PrimitiveSet.WeightedPathFamily"

namespace DkMath.NumberTheory.PrimitiveSet

open DkMath.CosmicFormula.Mass
open DkMath.NumberTheory.ValuationFlow

/--
A source-controlled finite forest with a nonnegative rational weight on each
indexed chain/path.

This is the finite weighted skeleton before introducing analytic Markov kernels
or von Mangoldt-type weights.
-/
structure WeightedPathFamily
    (M : MassSpace ℕ) (ι : Type _) [DecidableEq ι]
    extends SourceControlledChainFamily M ι where
  weight : ι → ℚ
  weight_nonneg : ∀ i ∈ index, 0 ≤ weight i

namespace WeightedPathFamily

/-- Add nonnegative weights to an existing source-controlled chain family. -/
def ofSourceControlled
    {ι : Type _} [DecidableEq ι] {M : MassSpace ℕ}
    (F : SourceControlledChainFamily M ι)
    (weight : ι → ℚ)
    (hweight : ∀ i ∈ F.index, 0 ≤ weight i) :
    WeightedPathFamily M ι where
  index := F.index
  chain := F.chain
  chain_is_chain := F.chain_is_chain
  source := F.source
  mass_le_source := F.mass_le_source
  weight := weight
  weight_nonneg := hweight

/-- Weighted indexed hit mass over a finite weighted path family. -/
def weightedHitMass
    {ι : Type _} [DecidableEq ι] {M : MassSpace ℕ}
    (W : WeightedPathFamily M ι) (S : Finset ℕ) : ℚ :=
  W.index.sum fun i => W.weight i * hitSetMass M (S ∩ W.chain i)

/-- Weighted indexed source mass over a finite weighted path family. -/
def weightedSourceMass
    {ι : Type _} [DecidableEq ι] {M : MassSpace ℕ}
    (W : WeightedPathFamily M ι) : ℚ :=
  W.index.sum fun i => W.weight i * M.μ (W.source i)

/-- Total finite weight carried by a weighted path family. -/
def totalWeight
    {ι : Type _} [DecidableEq ι] {M : MassSpace ℕ}
    (W : WeightedPathFamily M ι) : ℚ :=
  W.index.sum fun i => W.weight i

/--
The finite weights form a sub-probability mass on the index set.

This is the normalization layer before introducing an actual Markov kernel.
-/
def WeightSubProbability
    {ι : Type _} [DecidableEq ι] {M : MassSpace ℕ}
    (W : WeightedPathFamily M ι) : Prop :=
  W.totalWeight ≤ 1

/-- Total weight is nonnegative. -/
theorem totalWeight_nonneg
    {ι : Type _} [DecidableEq ι] {M : MassSpace ℕ}
    (W : WeightedPathFamily M ι) :
    0 ≤ W.totalWeight := by
  classical
  unfold totalWeight
  exact Finset.sum_nonneg fun i hi => W.weight_nonneg i hi

/--
If every source has mass at most `C`, then the weighted source mass is bounded
by `C * totalWeight`.
-/
theorem weightedSourceMass_le_const_mul_totalWeight
    {ι : Type _} [DecidableEq ι] {M : MassSpace ℕ}
    (W : WeightedPathFamily M ι) {C : ℚ}
    (hsource : ∀ i ∈ W.index, M.μ (W.source i) ≤ C) :
    W.weightedSourceMass ≤ C * W.totalWeight := by
  classical
  unfold weightedSourceMass totalWeight
  calc
    W.index.sum (fun i => W.weight i * M.μ (W.source i))
        ≤ W.index.sum (fun i => W.weight i * C) := by
          exact Finset.sum_le_sum fun i hi =>
            mul_le_mul_of_nonneg_left (hsource i hi) (W.weight_nonneg i hi)
    _ = C * W.index.sum (fun i => W.weight i) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _hi => by ring

/--
If the weights are a sub-probability and every source has mass at most `C`,
then the weighted source mass is at most `C`.
-/
theorem weightedSourceMass_le_const_of_subprob
    {ι : Type _} [DecidableEq ι] {M : MassSpace ℕ}
    (W : WeightedPathFamily M ι) {C : ℚ}
    (hC : 0 ≤ C)
    (hprob : W.WeightSubProbability)
    (hsource : ∀ i ∈ W.index, M.μ (W.source i) ≤ C) :
    W.weightedSourceMass ≤ C := by
  calc
    W.weightedSourceMass ≤ C * W.totalWeight :=
      W.weightedSourceMass_le_const_mul_totalWeight hsource
    _ ≤ C * 1 := by
      exact mul_le_mul_of_nonneg_left hprob hC
    _ = C := by ring

/--
Weighted primitive hitting bound.

Each chain has the usual primitive one-hit bound, and nonnegative weights
preserve the pointwise inequalities under the finite indexed sum.
-/
theorem primitive_weightedHitMass_le_weightedSourceMass
    {ι : Type _} [DecidableEq ι]
    {M : MassSpace ℕ} {S : Finset ℕ}
    (hS : PrimitiveOn S)
    (W : WeightedPathFamily M ι) :
    W.weightedHitMass S ≤ W.weightedSourceMass := by
  classical
  unfold weightedHitMass weightedSourceMass
  exact Finset.sum_le_sum fun i hi => by
    have hchain :
        hitSetMass M (S ∩ W.chain i) ≤ M.μ (W.source i) := by
      calc
        hitSetMass M (S ∩ W.chain i)
            ≤ sourceSetMass M ({W.source i} : Finset ℕ) := by
              exact primitive_chain_hitSetMass_le_single_source
                M hS (W.chain_is_chain i hi)
                (by
                  intro h hh
                  exact W.mass_le_source i hi h (Finset.mem_inter.mp hh).2)
        _ = M.μ (W.source i) := by
              simp [sourceSetMass]
    exact mul_le_mul_of_nonneg_left hchain (W.weight_nonneg i hi)

/--
If every source has mass at most `C`, primitive weighted hit mass is bounded by
`C * totalWeight`.
-/
theorem weightedHitMass_le_const_mul_totalWeight
    {ι : Type _} [DecidableEq ι]
    {M : MassSpace ℕ} {S : Finset ℕ}
    (hS : PrimitiveOn S)
    (W : WeightedPathFamily M ι) {C : ℚ}
    (hsource : ∀ i ∈ W.index, M.μ (W.source i) ≤ C) :
    W.weightedHitMass S ≤ C * W.totalWeight := by
  calc
    W.weightedHitMass S ≤ W.weightedSourceMass :=
      W.primitive_weightedHitMass_le_weightedSourceMass hS
    _ ≤ C * W.totalWeight :=
      W.weightedSourceMass_le_const_mul_totalWeight hsource

/--
If the weights are a sub-probability and every source has mass at most `C`,
primitive weighted hit mass is bounded by `C`.
-/
theorem weightedHitMass_le_const_of_subprob
    {ι : Type _} [DecidableEq ι]
    {M : MassSpace ℕ} {S : Finset ℕ}
    (hS : PrimitiveOn S)
    (W : WeightedPathFamily M ι) {C : ℚ}
    (hC : 0 ≤ C)
    (hprob : W.WeightSubProbability)
    (hsource : ∀ i ∈ W.index, M.μ (W.source i) ≤ C) :
    W.weightedHitMass S ≤ C := by
  calc
    W.weightedHitMass S ≤ W.weightedSourceMass :=
      W.primitive_weightedHitMass_le_weightedSourceMass hS
    _ ≤ C :=
      W.weightedSourceMass_le_const_of_subprob hC hprob hsource

end WeightedPathFamily

namespace ErdosFinitePrimitiveInput

/--
Weighted branch route: add nonnegative weights to the branch-controlled
source-controlled forest associated to a finite Erdos input.
-/
def weightedBranchPrimePathFamily
    {x : ℕ} {ι : Type _} [DecidableEq ι]
    (M : MassSpace ℕ) (B : Branching ℕ) [SubConservative M B]
    (I : ErdosFinitePrimitiveInput x)
    (F : AdjacentBranchPrimePathFamily ι B)
    (weight : ι → ℚ)
    (hweight :
      ∀ i ∈ (I.branchPrimePathFamilySourceControlled M B F).index,
        0 ≤ weight i) :
    WeightedPathFamily M ι :=
  WeightedPathFamily.ofSourceControlled
    (I.branchPrimePathFamilySourceControlled M B F) weight hweight

/-- Weighted hit mass for the branch-controlled route. -/
def weightedBranchPrimePathFamilyHitMass
    {x : ℕ} {ι : Type _} [DecidableEq ι]
    (M : MassSpace ℕ) (B : Branching ℕ) [SubConservative M B]
    (I : ErdosFinitePrimitiveInput x)
    (F : AdjacentBranchPrimePathFamily ι B)
    (weight : ι → ℚ)
    (hweight :
      ∀ i ∈ (I.branchPrimePathFamilySourceControlled M B F).index,
        0 ≤ weight i) : ℚ :=
  (I.weightedBranchPrimePathFamily M B F weight hweight).weightedHitMass
    I.support

/-- Weighted source mass for the branch-controlled route. -/
def weightedBranchPrimePathFamilySourceMass
    {x : ℕ} {ι : Type _} [DecidableEq ι]
    (M : MassSpace ℕ) (B : Branching ℕ) [SubConservative M B]
    (I : ErdosFinitePrimitiveInput x)
    (F : AdjacentBranchPrimePathFamily ι B)
    (weight : ι → ℚ)
    (hweight :
      ∀ i ∈ (I.branchPrimePathFamilySourceControlled M B F).index,
        0 ≤ weight i) : ℚ :=
  (I.weightedBranchPrimePathFamily M B F weight hweight).weightedSourceMass

/--
Weighted finite Erdos bound for the branch-controlled route.
-/
theorem weightedHitMass_le_weightedSourceMass_of_branchPrimePathFamily
    {x : ℕ} {ι : Type _} [DecidableEq ι]
    {M : MassSpace ℕ} {B : Branching ℕ} [SubConservative M B]
    (I : ErdosFinitePrimitiveInput x)
    (F : AdjacentBranchPrimePathFamily ι B)
    (weight : ι → ℚ)
    (hweight :
      ∀ i ∈ (I.branchPrimePathFamilySourceControlled M B F).index,
        0 ≤ weight i) :
    I.weightedBranchPrimePathFamilyHitMass M B F weight hweight ≤
      I.weightedBranchPrimePathFamilySourceMass M B F weight hweight := by
  exact (I.weightedBranchPrimePathFamily M B F weight hweight)
    |>.primitive_weightedHitMass_le_weightedSourceMass I.primitive

/--
Weighted prime path route: add nonnegative weights to the prime-path-family
source-controlled forest obtained from divisibility-monotone mass.
-/
def weightedPrimePathFamily
    {x : ℕ} {ι : Type _} [DecidableEq ι]
    (M : MassSpace ℕ)
    (I : ErdosFinitePrimitiveInput x)
    (F : AdjacentPrimePathFamily ι) (hM : DvdMonotoneMass M)
    (weight : ι → ℚ)
    (hweight :
      ∀ i ∈ (I.primePathFamilySourceControlled M F hM).index,
        0 ≤ weight i) :
    WeightedPathFamily M ι :=
  WeightedPathFamily.ofSourceControlled
    (I.primePathFamilySourceControlled M F hM) weight hweight

/-- Weighted hit mass for the prime-path-family / dvd-monotone route. -/
def weightedPrimePathFamilyHitMass
    {x : ℕ} {ι : Type _} [DecidableEq ι]
    (M : MassSpace ℕ)
    (I : ErdosFinitePrimitiveInput x)
    (F : AdjacentPrimePathFamily ι) (hM : DvdMonotoneMass M)
    (weight : ι → ℚ)
    (hweight :
      ∀ i ∈ (I.primePathFamilySourceControlled M F hM).index,
        0 ≤ weight i) : ℚ :=
  (I.weightedPrimePathFamily M F hM weight hweight).weightedHitMass
    I.support

/-- Weighted source mass for the prime-path-family / dvd-monotone route. -/
def weightedPrimePathFamilySourceMass
    {x : ℕ} {ι : Type _} [DecidableEq ι]
    (M : MassSpace ℕ)
    (I : ErdosFinitePrimitiveInput x)
    (F : AdjacentPrimePathFamily ι) (hM : DvdMonotoneMass M)
    (weight : ι → ℚ)
    (hweight :
      ∀ i ∈ (I.primePathFamilySourceControlled M F hM).index,
        0 ≤ weight i) : ℚ :=
  (I.weightedPrimePathFamily M F hM weight hweight).weightedSourceMass

/--
Weighted finite Erdos bound for the prime-path-family / dvd-monotone route.
-/
theorem weightedHitMass_le_weightedSourceMass_of_primePathFamily
    {x : ℕ} {ι : Type _} [DecidableEq ι]
    {M : MassSpace ℕ}
    (I : ErdosFinitePrimitiveInput x)
    (F : AdjacentPrimePathFamily ι) (hM : DvdMonotoneMass M)
    (weight : ι → ℚ)
    (hweight :
      ∀ i ∈ (I.primePathFamilySourceControlled M F hM).index,
        0 ≤ weight i) :
    I.weightedPrimePathFamilyHitMass M F hM weight hweight ≤
      I.weightedPrimePathFamilySourceMass M F hM weight hweight := by
  exact (I.weightedPrimePathFamily M F hM weight hweight)
    |>.primitive_weightedHitMass_le_weightedSourceMass I.primitive

end ErdosFinitePrimitiveInput

/-- Sample nonnegative rational weights on the Bool-indexed path family. -/
def sampleBoolPathWeight : Bool → ℚ :=
  fun b => if b then 3 else 2

/-- Sample sub-probability weights on the Bool-indexed path family. -/
def sampleBoolSubprobPathWeight : Bool → ℚ :=
  fun b => if b then (2 / 3 : ℚ) else (1 / 3 : ℚ)

/--
Concrete weighted sample for the branch-controlled finite Erdos route.
-/
theorem erdosFinitePrimitiveInput_two_five_weightedBranch_hitMass_le_sourceMass :
    erdosFinitePrimitiveInput_two_five.weightedBranchPrimePathFamilyHitMass
      unitNatMassSpace sampleBranching_eight_nine_paths
      sampleAdjacentBranchPrimePathBoolFamily sampleBoolPathWeight
      (by
        intro b _hb
        cases b <;> norm_num [sampleBoolPathWeight]) ≤
    erdosFinitePrimitiveInput_two_five.weightedBranchPrimePathFamilySourceMass
      unitNatMassSpace sampleBranching_eight_nine_paths
      sampleAdjacentBranchPrimePathBoolFamily sampleBoolPathWeight
      (by
        intro b _hb
        cases b <;> norm_num [sampleBoolPathWeight]) := by
  exact erdosFinitePrimitiveInput_two_five
    |>.weightedHitMass_le_weightedSourceMass_of_branchPrimePathFamily
      sampleAdjacentBranchPrimePathBoolFamily sampleBoolPathWeight
      (by
        intro b _hb
        cases b <;> norm_num [sampleBoolPathWeight])

/--
Concrete weighted sample for the prime-path-family / dvd-monotone finite Erdos
route.
-/
theorem erdosFinitePrimitiveInput_two_five_weightedPrimePath_hitMass_le_sourceMass :
    erdosFinitePrimitiveInput_two_five.weightedPrimePathFamilyHitMass
      unitNatMassSpace sampleAdjacentPrimePathBoolFamily
      unitNatMassSpace_dvdMonotone sampleBoolPathWeight
      (by
        intro b _hb
        cases b <;> norm_num [sampleBoolPathWeight]) ≤
    erdosFinitePrimitiveInput_two_five.weightedPrimePathFamilySourceMass
      unitNatMassSpace sampleAdjacentPrimePathBoolFamily
      unitNatMassSpace_dvdMonotone sampleBoolPathWeight
      (by
        intro b _hb
        cases b <;> norm_num [sampleBoolPathWeight]) := by
  exact erdosFinitePrimitiveInput_two_five
    |>.weightedHitMass_le_weightedSourceMass_of_primePathFamily
      sampleAdjacentPrimePathBoolFamily unitNatMassSpace_dvdMonotone
      sampleBoolPathWeight
      (by
        intro b _hb
        cases b <;> norm_num [sampleBoolPathWeight])

/--
Concrete sub-probability sample: the weighted branch source mass is bounded by
the uniform unit source-mass bound.
-/
theorem erdosFinitePrimitiveInput_two_five_weightedBranch_sourceMass_le_one :
    (erdosFinitePrimitiveInput_two_five.weightedBranchPrimePathFamily
      unitNatMassSpace sampleBranching_eight_nine_paths
      sampleAdjacentBranchPrimePathBoolFamily sampleBoolSubprobPathWeight
      (by
        intro b _hb
        cases b <;> norm_num [sampleBoolSubprobPathWeight])).weightedSourceMass
      ≤ 1 := by
  let W :=
    erdosFinitePrimitiveInput_two_five.weightedBranchPrimePathFamily
      unitNatMassSpace sampleBranching_eight_nine_paths
      sampleAdjacentBranchPrimePathBoolFamily sampleBoolSubprobPathWeight
      (by
        intro b _hb
        cases b <;> norm_num [sampleBoolSubprobPathWeight])
  have hprob : W.WeightSubProbability := by
    simp only [WeightedPathFamily.WeightSubProbability,
      WeightedPathFamily.totalWeight, W,
      ErdosFinitePrimitiveInput.weightedBranchPrimePathFamily,
      WeightedPathFamily.ofSourceControlled,
      ErdosFinitePrimitiveInput.branchPrimePathFamilySourceControlled,
      sampleAdjacentBranchPrimePathBoolFamily, sampleBoolSubprobPathWeight]
    norm_num
  have hsource : ∀ i ∈ W.index, unitNatMassSpace.μ (W.source i) ≤ (1 : ℚ) := by
    intro i _hi
    rfl
  exact W.weightedSourceMass_le_const_of_subprob (by norm_num) hprob hsource

/--
Concrete sub-probability sample: the weighted branch hit mass is bounded by the
same uniform unit source-mass bound.
-/
theorem erdosFinitePrimitiveInput_two_five_weightedBranch_hitMass_le_one :
    (erdosFinitePrimitiveInput_two_five.weightedBranchPrimePathFamily
      unitNatMassSpace sampleBranching_eight_nine_paths
      sampleAdjacentBranchPrimePathBoolFamily sampleBoolSubprobPathWeight
      (by
        intro b _hb
        cases b <;> norm_num [sampleBoolSubprobPathWeight])).weightedHitMass
      erdosFinitePrimitiveInput_two_five.support ≤ 1 := by
  let W :=
    erdosFinitePrimitiveInput_two_five.weightedBranchPrimePathFamily
      unitNatMassSpace sampleBranching_eight_nine_paths
      sampleAdjacentBranchPrimePathBoolFamily sampleBoolSubprobPathWeight
      (by
        intro b _hb
        cases b <;> norm_num [sampleBoolSubprobPathWeight])
  have hprob : W.WeightSubProbability := by
    simp only [WeightedPathFamily.WeightSubProbability,
      WeightedPathFamily.totalWeight, W,
      ErdosFinitePrimitiveInput.weightedBranchPrimePathFamily,
      WeightedPathFamily.ofSourceControlled,
      ErdosFinitePrimitiveInput.branchPrimePathFamilySourceControlled,
      sampleAdjacentBranchPrimePathBoolFamily, sampleBoolSubprobPathWeight]
    norm_num
  have hsource : ∀ i ∈ W.index, unitNatMassSpace.μ (W.source i) ≤ (1 : ℚ) := by
    intro i _hi
    rfl
  exact W.weightedHitMass_le_const_of_subprob
    erdosFinitePrimitiveInput_two_five.primitive (by norm_num) hprob hsource

end DkMath.NumberTheory.PrimitiveSet
