/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PrimitiveSet.PrimePathList

#print "file: DkMath.NumberTheory.PrimitiveSet.SubConservativeBridge"

namespace DkMath.NumberTheory.PrimitiveSet

open DkMath.CosmicFormula.Mass
open DkMath.NumberTheory.ValuationFlow

/--
A single branch child has mass at most its parent under a subconservative
branching.
-/
theorem child_mass_le_parent_of_subconservative
    {α : Type _} [DecidableEq α]
    (M : MassSpace α) (B : Branching α) [SubConservative M B]
    {parent child : α} (hchild : child ∈ B.children parent) :
    M.μ child ≤ M.μ parent := by
  have hsingle_le_sum :
      M.μ child ≤ (B.children parent).sum fun c => M.μ c := by
    exact Finset.single_le_sum (fun c _hc => M.nonneg c) hchild
  exact hsingle_le_sum.trans (outgoingMass_le_mass M B parent)

/--
Adjacent list entries follow the branch relation.
-/
def AdjacentBranchPath (B : Branching ℕ) (L : List ℕ) : Prop :=
  List.IsChain (fun parent child => child ∈ B.children parent) L

namespace AdjacentBranchPath

/--
Under a subconservative branching, every node of a nonempty branch path has
mass at most the head.
-/
theorem mem_mass_le_head
    (M : MassSpace ℕ) (B : Branching ℕ) [SubConservative M B] :
    ∀ {source h : ℕ} {tail : List ℕ},
      AdjacentBranchPath B (source :: tail) →
      h ∈ source :: tail →
      M.μ h ≤ M.μ source
  | source, h, [], _hL, hh => by
      simp only [List.mem_singleton] at hh
      subst h
      rfl
  | source, h, next :: rest, hL, hh => by
      have hstep : next ∈ B.children source :=
        (List.isChain_cons_cons.mp hL).1
      have htail : AdjacentBranchPath B (next :: rest) :=
        (List.isChain_cons_cons.mp hL).2
      have hnext_le_source : M.μ next ≤ M.μ source :=
        child_mass_le_parent_of_subconservative M B hstep
      simp only [List.mem_cons] at hh
      rcases hh with rfl | hh_tail
      · rfl
      · exact (mem_mass_le_head M B htail
          (by simpa only [List.mem_cons] using hh_tail)).trans hnext_le_source

end AdjacentBranchPath

/--
A list-shaped prime path whose adjacent entries are also branch children can be
packaged as a singleton source-controlled family using subconservativity.
-/
def singletonSourceControlledChainFamilyOfAdjacentBranchPrimePath
    (M : MassSpace ℕ) (B : Branching ℕ) [SubConservative M B]
    (source : ℕ) (tail : List ℕ)
    (hPrime : AdjacentPrimePath (source :: tail))
    (hBranch : AdjacentBranchPath B (source :: tail)) :
    SourceControlledChainFamily M Unit where
  index := {()}
  chain := fun _ => (source :: tail).toFinset
  chain_is_chain := by
    intro i hi
    exact divisibilityChain_toFinset_of_adjacentPrimePath hPrime
  source := fun _ => source
  mass_le_source := by
    intro i hi h hh
    exact AdjacentBranchPath.mem_mass_le_head M B hBranch (by simpa using hh)

/--
Sample branch for the concrete path `8 -> 4 -> 2`.
-/
def sampleBranching_eight_four_two : Branching ℕ where
  children := fun n =>
    if n = 8 then ({4} : Finset ℕ)
    else if n = 4 then ({2} : Finset ℕ)
    else ∅

/-- The concrete path `8 -> 4 -> 2` follows `sampleBranching_eight_four_two`. -/
theorem adjacentBranchPath_eight_four_two :
    AdjacentBranchPath sampleBranching_eight_four_two [8, 4, 2] := by
  simp only [AdjacentBranchPath, List.isChain_cons_cons, List.isChain_singleton,
    and_true, sampleBranching_eight_four_two]
  constructor <;> simp

/-- The sample branch is subconservative for unit mass. -/
instance sampleBranching_eight_four_two_subConservative :
    SubConservative unitNatMassSpace sampleBranching_eight_four_two where
  outgoing_le := by
    intro n
    by_cases h8 : n = 8
    · subst n
      simp [outgoingMass, sampleBranching_eight_four_two, unitNatMassSpace]
    · by_cases h4 : n = 4
      · subst n
        simp [outgoingMass, sampleBranching_eight_four_two, h8, unitNatMassSpace]
      · simp [outgoingMass, sampleBranching_eight_four_two, h8, h4, unitNatMassSpace]

/--
The concrete path `8 -> 4 -> 2` packaged as a source-controlled family via
subconservativity of the sample branch.
-/
def singletonSourceControlledFamily_eight_four_two_of_subConservative :
    SourceControlledChainFamily unitNatMassSpace Unit :=
  singletonSourceControlledChainFamilyOfAdjacentBranchPrimePath
    unitNatMassSpace
    sampleBranching_eight_four_two
    8 [4, 2]
    adjacentPrimePath_eight_four_two
    adjacentBranchPath_eight_four_two

/--
Concrete sample: primitive `{2,5}` hitting the branch-controlled list path
`8 -> 4 -> 2` has unit hit mass bounded by the source mass.
-/
theorem primitive_two_five_singletonSourceControlledFamily_eight_four_two_hitMass_le_sourceMass :
    singletonSourceControlledFamily_eight_four_two_of_subConservative.hitMass
      ({2, 5} : Finset ℕ) ≤
      singletonSourceControlledFamily_eight_four_two_of_subConservative.sourceMass := by
  have hS : PrimitiveOn ({2, 5} : Finset ℕ) := by
    exact primitiveOn_pair (by norm_num) (by norm_num)
  exact SourceControlledChainFamily.primitive_hitMass_le_sourceMass
    hS singletonSourceControlledFamily_eight_four_two_of_subConservative

end DkMath.NumberTheory.PrimitiveSet
