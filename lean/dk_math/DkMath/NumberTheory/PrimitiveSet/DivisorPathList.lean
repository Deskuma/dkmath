/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PrimitiveSet.PrimePathList

#print "file: DkMath.NumberTheory.PrimitiveSet.DivisorPathList"

namespace DkMath.NumberTheory.PrimitiveSet

open DkMath.CosmicFormula.Mass

/--
A concrete list-shaped divisor descent path.

Adjacent list entries descend by divisibility: for consecutive nodes `a, b`,
the next node `b` divides the previous node `a`.
-/
def AdjacentDivisorPath (L : List ℕ) : Prop :=
  List.IsChain DvdDescentStep L

namespace AdjacentDivisorPath

/-- A divisor path is pairwise comparable by divisibility. -/
theorem pairwiseDvdAlongList
    {L : List ℕ} (hL : AdjacentDivisorPath L) :
    PairwiseDvdAlongList L :=
  pairwiseDvdAlongList_of_isChain_dvd hL

/-- The node set of a list-shaped divisor path is a divisibility chain. -/
theorem divisibilityChain_toFinset
    {L : List ℕ} (hL : AdjacentDivisorPath L) :
    DivisibilityChain L.toFinset :=
  hL.pairwiseDvdAlongList.divisibilityChain_toFinset

/-- Every node of a nonempty divisor path divides its head. -/
theorem mem_dvd_head
    {source h : ℕ} {tail : List ℕ}
    (hL : AdjacentDivisorPath (source :: tail))
    (hh : h ∈ source :: tail) :
    h ∣ source := by
  simp only [List.mem_cons] at hh
  rcases hh with rfl | hh_tail
  · exact dvd_rfl
  · exact mem_tail_dvd_head_of_isChain_dvd hL hh_tail

end AdjacentDivisorPath

/--
A list-shaped divisor path packaged as a one-chain `DivisibilityChainFamily`.
-/
def singletonChainFamilyOfAdjacentDivisorPath
    (L : List ℕ) (hL : AdjacentDivisorPath L) :
    DivisibilityChainFamily Unit where
  index := {()}
  chain := fun _ => L.toFinset
  chain_is_chain := by
    intro i hi
    exact hL.divisibilityChain_toFinset

/--
A nonempty list-shaped divisor path packaged as a singleton
`DvdControlledChainFamily` with source equal to the head.
-/
def singletonDvdControlledChainFamilyOfAdjacentDivisorPath
    (source : ℕ) (tail : List ℕ)
    (hL : AdjacentDivisorPath (source :: tail)) :
    DvdControlledChainFamily Unit where
  index := {()}
  chain := fun _ => (source :: tail).toFinset
  chain_is_chain := by
    intro i hi
    exact hL.divisibilityChain_toFinset
  source := fun _ => source
  chain_dvd_source := by
    intro i hi h hh
    exact hL.mem_dvd_head (by simpa using hh)

/-- Concrete divisor path `12 -> 6 -> 3`. -/
theorem adjacentDivisorPath_twelve_six_three :
    AdjacentDivisorPath [12, 6, 3] := by
  simp only [AdjacentDivisorPath, List.isChain_cons_cons, List.isChain_singleton,
    and_true]
  exact ⟨by change 6 ∣ 12; norm_num, by change 3 ∣ 6; norm_num⟩

/-- The node set of `12 -> 6 -> 3` is a divisibility chain. -/
theorem divisibilityChain_twelve_six_three_toFinset :
    DivisibilityChain ([12, 6, 3] : List ℕ).toFinset :=
  adjacentDivisorPath_twelve_six_three.divisibilityChain_toFinset

/--
Concrete sample: primitive `{3, 5}` hits the divisor path `12 -> 6 -> 3` in
at most one point.
-/
theorem primitive_three_five_hits_twelve_six_three_card_le_one :
    (({3, 5} : Finset ℕ) ∩ ([12, 6, 3] : List ℕ).toFinset).card ≤ 1 := by
  have hS : PrimitiveOn ({3, 5} : Finset ℕ) := by
    exact primitiveOn_pair (by norm_num) (by norm_num)
  exact primitiveOn_inter_chain_card_le_one hS
    divisibilityChain_twelve_six_three_toFinset

/--
Concrete sample: the divisor path `12 -> 6 -> 3` gives a source-controlled
singleton family under unit mass.
-/
theorem primitive_three_five_singletonDvdControlled_twelve_six_three_hitMass_le_sourceMass :
    (singletonDvdControlledChainFamilyOfAdjacentDivisorPath
      12 [6, 3] adjacentDivisorPath_twelve_six_three
      |>.toSourceControlled unitNatMassSpace_dvdMonotone).hitMass
        ({3, 5} : Finset ℕ) ≤
      (singletonDvdControlledChainFamilyOfAdjacentDivisorPath
        12 [6, 3] adjacentDivisorPath_twelve_six_three
        |>.toSourceControlled unitNatMassSpace_dvdMonotone).sourceMass := by
  have hS : PrimitiveOn ({3, 5} : Finset ℕ) := by
    exact primitiveOn_pair (by norm_num) (by norm_num)
  exact
    (singletonDvdControlledChainFamilyOfAdjacentDivisorPath
      12 [6, 3] adjacentDivisorPath_twelve_six_three).primitive_hitMass_le_sourceMass
        hS unitNatMassSpace_dvdMonotone

end DkMath.NumberTheory.PrimitiveSet
