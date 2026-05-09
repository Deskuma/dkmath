/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PrimitiveSet.PathFamily
import DkMath.NumberTheory.PrimitiveSet.SubConservativeBridge

#print "file: DkMath.NumberTheory.PrimitiveSet.BranchPathFamily"

namespace DkMath.NumberTheory.PrimitiveSet

open DkMath.CosmicFormula.Mass

/--
A finite family of nonempty prime paths whose adjacent entries also follow a
fixed branching relation.
-/
structure AdjacentBranchPrimePathFamily
    (ι : Type _) [DecidableEq ι] (B : Branching ℕ)
    extends AdjacentPrimePathFamily ι where
  isBranchPath : ∀ i ∈ index, AdjacentBranchPath B (source i :: tail i)

namespace AdjacentBranchPrimePathFamily

/--
Use subconservativity of the branch relation to turn a branch-prime path family
into a source-controlled chain family.
-/
def toSourceControlledChainFamily
    {ι : Type _} [DecidableEq ι]
    (M : MassSpace ℕ) (B : Branching ℕ) [SubConservative M B]
    (F : AdjacentBranchPrimePathFamily ι B) :
    SourceControlledChainFamily M ι where
  index := F.index
  chain := F.toAdjacentPrimePathFamily.nodeSet
  chain_is_chain := by
    intro i hi
    exact divisibilityChain_toFinset_of_adjacentPrimePath (F.isPath i hi)
  source := F.source
  mass_le_source := by
    intro i hi h hh
    exact AdjacentBranchPath.mem_mass_le_head M B (F.isBranchPath i hi)
      (by
        simpa [AdjacentPrimePathFamily.nodeSet, AdjacentPrimePathFamily.path]
          using hh)

@[simp] theorem toSourceControlledChainFamily_index
    {ι : Type _} [DecidableEq ι]
    (M : MassSpace ℕ) (B : Branching ℕ) [SubConservative M B]
    (F : AdjacentBranchPrimePathFamily ι B) :
    (F.toSourceControlledChainFamily M B).index = F.index := rfl

@[simp] theorem toSourceControlledChainFamily_chain
    {ι : Type _} [DecidableEq ι]
    (M : MassSpace ℕ) (B : Branching ℕ) [SubConservative M B]
    (F : AdjacentBranchPrimePathFamily ι B) :
    (F.toSourceControlledChainFamily M B).chain =
      F.toAdjacentPrimePathFamily.nodeSet := rfl

@[simp] theorem toSourceControlledChainFamily_source
    {ι : Type _} [DecidableEq ι]
    (M : MassSpace ℕ) (B : Branching ℕ) [SubConservative M B]
    (F : AdjacentBranchPrimePathFamily ι B) :
    (F.toSourceControlledChainFamily M B).source = F.source := rfl

/--
Primitive hitting bound for a finite family of branch-controlled prime paths.

The source mass control is supplied by the branch subconservativity, not by a
separate divisibility-monotone mass hypothesis.
-/
theorem primitive_hitMass_le_sourceMass
    {ι : Type _} [DecidableEq ι]
    {M : MassSpace ℕ} {B : Branching ℕ} [SubConservative M B]
    {S : Finset ℕ}
    (hS : PrimitiveOn S)
    (F : AdjacentBranchPrimePathFamily ι B) :
    (F.toSourceControlledChainFamily M B).hitMass S ≤
      (F.toSourceControlledChainFamily M B).sourceMass := by
  exact (F.toSourceControlledChainFamily M B).primitive_hitMass_le_sourceMass hS

end AdjacentBranchPrimePathFamily

/--
Sample branching containing both paths `8 -> 4 -> 2` and `9 -> 3 -> 1`.
-/
def sampleBranching_eight_nine_paths : Branching ℕ where
  children := fun n =>
    if n = 8 then ({4} : Finset ℕ)
    else if n = 4 then ({2} : Finset ℕ)
    else if n = 9 then ({3} : Finset ℕ)
    else if n = 3 then ({1} : Finset ℕ)
    else ∅

/-- The path `8 -> 4 -> 2` follows `sampleBranching_eight_nine_paths`. -/
theorem adjacentBranchPath_eight_four_two_sampleBranching_eight_nine_paths :
    AdjacentBranchPath sampleBranching_eight_nine_paths [8, 4, 2] := by
  simp only [AdjacentBranchPath, List.isChain_cons_cons, List.isChain_singleton,
    and_true, sampleBranching_eight_nine_paths]
  constructor <;> simp

/-- The path `9 -> 3 -> 1` follows `sampleBranching_eight_nine_paths`. -/
theorem adjacentBranchPath_nine_three_one_sampleBranching_eight_nine_paths :
    AdjacentBranchPath sampleBranching_eight_nine_paths [9, 3, 1] := by
  simp only [AdjacentBranchPath, List.isChain_cons_cons, List.isChain_singleton,
    and_true, sampleBranching_eight_nine_paths]
  constructor <;> simp

/-- The two-path sample branching is subconservative for unit mass. -/
instance sampleBranching_eight_nine_paths_subConservative :
    SubConservative unitNatMassSpace sampleBranching_eight_nine_paths where
  outgoing_le := by
    intro n
    by_cases h8 : n = 8
    · subst n
      simp [outgoingMass, sampleBranching_eight_nine_paths, unitNatMassSpace]
    · by_cases h4 : n = 4
      · subst n
        simp [outgoingMass, sampleBranching_eight_nine_paths, h8, unitNatMassSpace]
      · by_cases h9 : n = 9
        · subst n
          simp [outgoingMass, sampleBranching_eight_nine_paths, h8, h4,
            unitNatMassSpace]
        · by_cases h3 : n = 3
          · subst n
            simp [outgoingMass, sampleBranching_eight_nine_paths, h8, h4, h9,
              unitNatMassSpace]
          · simp [outgoingMass, sampleBranching_eight_nine_paths, h8, h4, h9,
              h3, unitNatMassSpace]

/-- A Bool-indexed family of two branch-controlled prime descent paths. -/
def sampleAdjacentBranchPrimePathBoolFamily :
    AdjacentBranchPrimePathFamily Bool sampleBranching_eight_nine_paths where
  index := {false, true}
  source := fun b => if b then 9 else 8
  tail := fun b => if b then [3, 1] else [4, 2]
  isPath := by
    intro b hb
    cases b
    · simpa only [Bool.false_eq_true, ↓reduceIte] using adjacentPrimePath_eight_four_two
    · simpa only [↓reduceIte] using adjacentPrimePath_nine_three_one
  isBranchPath := by
    intro b hb
    cases b
    · simpa only [Bool.false_eq_true, ↓reduceIte] using
        adjacentBranchPath_eight_four_two_sampleBranching_eight_nine_paths
    · simpa only [↓reduceIte] using
        adjacentBranchPath_nine_three_one_sampleBranching_eight_nine_paths

/-- The branch-controlled Bool path-family sample as a source-controlled family. -/
def sampleAdjacentBranchPrimePathBoolFamilySourceControlled :
    SourceControlledChainFamily unitNatMassSpace Bool :=
  sampleAdjacentBranchPrimePathBoolFamily.toSourceControlledChainFamily
    unitNatMassSpace sampleBranching_eight_nine_paths

/--
Concrete sample: primitive `{2,5}` hitting a branch-controlled two-path family
has indexed unit hit mass bounded by the indexed source mass.
-/
theorem primitive_two_five_sampleAdjacentBranchPrimePathBoolFamily_hitMass_le_sourceMass :
    sampleAdjacentBranchPrimePathBoolFamilySourceControlled.hitMass
      ({2, 5} : Finset ℕ) ≤
      sampleAdjacentBranchPrimePathBoolFamilySourceControlled.sourceMass := by
  have hS : PrimitiveOn ({2, 5} : Finset ℕ) := by
    exact primitiveOn_pair (by norm_num) (by norm_num)
  exact sampleAdjacentBranchPrimePathBoolFamily.primitive_hitMass_le_sourceMass hS

end DkMath.NumberTheory.PrimitiveSet
