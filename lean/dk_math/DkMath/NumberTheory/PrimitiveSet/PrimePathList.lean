/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PrimitiveSet.PrimePath

#print "file: DkMath.NumberTheory.PrimitiveSet.PrimePathList"

namespace DkMath.NumberTheory.PrimitiveSet

open DkMath.CosmicFormula.Mass

/--
A concrete list-shaped prime descent path.

Adjacent list entries are connected by `PrimeDescentStep`.
-/
def AdjacentPrimePath (L : List ℕ) : Prop :=
  List.IsChain PrimeDescentStep L

/--
List-level comparability by divisibility.
-/
def PairwiseDvdAlongList (L : List ℕ) : Prop :=
  ∀ ⦃a b : ℕ⦄, a ∈ L → b ∈ L → a ∣ b ∨ b ∣ a

namespace AdjacentPrimePath

/-- A prime path is also a divisibility descent path. -/
theorem toDvdPath {L : List ℕ} (hL : AdjacentPrimePath L) :
    List.IsChain DvdDescentStep L :=
  hL.imp fun _a _b h => h.toDvdDescentStep

end AdjacentPrimePath

namespace PairwiseDvdAlongList

/-- Convert list-level comparability to a `DivisibilityChain` on `toFinset`. -/
theorem divisibilityChain_toFinset
    {L : List ℕ} (hL : PairwiseDvdAlongList L) :
    DivisibilityChain L.toFinset := by
  intro a b ha hb
  exact hL (by simpa using ha) (by simpa using hb)

end PairwiseDvdAlongList

/--
In a divisibility descent list, every tail member divides the head.
-/
theorem mem_tail_dvd_head_of_isChain_dvd :
    ∀ {x y : ℕ} {xs : List ℕ},
      List.IsChain DvdDescentStep (x :: xs) → y ∈ xs → y ∣ x
  | _x, _y, [], _hchain, hy => by
      simp at hy
  | x, y, z :: zs, hchain, hy => by
      have hz_dvd_x : z ∣ x := (List.isChain_cons_cons.mp hchain).1
      have htail : List.IsChain DvdDescentStep (z :: zs) :=
        (List.isChain_cons_cons.mp hchain).2
      simp only [List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact hz_dvd_x
      · exact dvd_trans (mem_tail_dvd_head_of_isChain_dvd htail hy) hz_dvd_x

/--
A list-shaped divisibility descent path is pairwise comparable by divisibility.
-/
theorem pairwiseDvdAlongList_of_isChain_dvd :
    ∀ {L : List ℕ}, List.IsChain DvdDescentStep L → PairwiseDvdAlongList L
  | [], _hchain => by
      intro a b ha
      simp at ha
  | [x], _hchain => by
      intro a b ha hb
      simp only [List.mem_singleton] at ha hb
      subst a
      subst b
      exact Or.inl dvd_rfl
  | x :: y :: ys, hchain => by
      intro a b ha hb
      have hy_tail : List.IsChain DvdDescentStep (y :: ys) :=
        (List.isChain_cons_cons.mp hchain).2
      have htail_pair :
          PairwiseDvdAlongList (y :: ys) :=
        pairwiseDvdAlongList_of_isChain_dvd hy_tail
      simp only [List.mem_cons] at ha hb
      rcases ha with rfl | ha_tail
      · rcases hb with rfl | hb_tail
        · exact Or.inl dvd_rfl
        · have hb_tail_mem : b ∈ y :: ys := by
            simpa only [List.mem_cons] using hb_tail
          exact Or.inr (mem_tail_dvd_head_of_isChain_dvd hchain hb_tail_mem)
      · rcases hb with rfl | hb_tail
        · have ha_tail_mem : a ∈ y :: ys := by
            simpa only [List.mem_cons] using ha_tail
          exact Or.inl (mem_tail_dvd_head_of_isChain_dvd hchain ha_tail_mem)
        · have ha_tail_mem : a ∈ y :: ys := by
            simpa only [List.mem_cons] using ha_tail
          have hb_tail_mem : b ∈ y :: ys := by
            simpa only [List.mem_cons] using hb_tail
          exact htail_pair ha_tail_mem hb_tail_mem

/--
A list-shaped prime descent path is pairwise comparable by divisibility.
-/
theorem pairwiseDvdAlongList_of_adjacentPrimePath
    {L : List ℕ} (hL : AdjacentPrimePath L) :
    PairwiseDvdAlongList L :=
  pairwiseDvdAlongList_of_isChain_dvd hL.toDvdPath

/--
The node set of a list-shaped prime descent path is a divisibility chain.
-/
theorem divisibilityChain_toFinset_of_adjacentPrimePath
    {L : List ℕ} (hL : AdjacentPrimePath L) :
    DivisibilityChain L.toFinset :=
  (pairwiseDvdAlongList_of_adjacentPrimePath hL).divisibilityChain_toFinset

/--
A list-shaped prime path packaged as a one-chain `DivisibilityChainFamily`.
-/
def singletonChainFamilyOfAdjacentPrimePath
    (L : List ℕ) (hL : AdjacentPrimePath L) :
    DivisibilityChainFamily Unit where
  index := {()}
  chain := fun _ => L.toFinset
  chain_is_chain := by
    intro i hi
    exact divisibilityChain_toFinset_of_adjacentPrimePath hL

/-- Concrete list-shaped prime path `8 -> 4 -> 2`. -/
theorem adjacentPrimePath_eight_four_two :
    AdjacentPrimePath [8, 4, 2] := by
  simp only [AdjacentPrimePath, List.isChain_cons_cons, List.isChain_singleton,
    and_true]
  exact ⟨primeDescentStep_eight_four, primeDescentStep_four_two⟩

/-- The node set of `8 -> 4 -> 2` is a divisibility chain. -/
theorem divisibilityChain_eight_four_two_toFinset :
    DivisibilityChain ([8, 4, 2] : List ℕ).toFinset :=
  divisibilityChain_toFinset_of_adjacentPrimePath adjacentPrimePath_eight_four_two

/--
Concrete sample: primitive `{2, 5}` hits the list path `8 -> 4 -> 2` in at
most one point.
-/
theorem primitive_two_five_hits_eight_four_two_card_le_one :
    (({2, 5} : Finset ℕ) ∩ ([8, 4, 2] : List ℕ).toFinset).card ≤ 1 := by
  have hS : PrimitiveOn ({2, 5} : Finset ℕ) := by
    exact primitiveOn_pair (by norm_num) (by norm_num)
  exact primitiveOn_inter_chain_card_le_one hS
    divisibilityChain_eight_four_two_toFinset

end DkMath.NumberTheory.PrimitiveSet
