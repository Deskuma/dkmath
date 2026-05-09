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

end ErdosFinitePrimitiveInput

/-- Sample nonnegative rational weights on the Bool-indexed path family. -/
def sampleBoolPathWeight : Bool → ℚ :=
  fun b => if b then 3 else 2

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

end DkMath.NumberTheory.PrimitiveSet
