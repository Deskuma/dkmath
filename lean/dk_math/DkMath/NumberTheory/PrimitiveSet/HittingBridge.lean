/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PrimitiveSet.Basic
import DkMath.NumberTheory.ValuationFlow.Hitting

#print "file: DkMath.NumberTheory.PrimitiveSet.HittingBridge"

namespace DkMath.NumberTheory.PrimitiveSet

open DkMath.CosmicFormula.Mass
open DkMath.NumberTheory.ValuationFlow

/--
Finite divisibility chain.

This is deliberately weaker than a graph reachability structure: every pair of
points in the chain is merely comparable by divisibility.  It is the exact
finite condition needed to express "a primitive set hits one descent chain at
most once".
-/
def DivisibilityChain (C : Finset ℕ) : Prop :=
  ∀ ⦃a b : ℕ⦄, a ∈ C → b ∈ C → a ∣ b ∨ b ∣ a

namespace DivisibilityChain

/-- Direct comparability eliminator for a finite divisibility chain. -/
theorem comparable
    {C : Finset ℕ} (hC : DivisibilityChain C)
    {a b : ℕ} (ha : a ∈ C) (hb : b ∈ C) :
    a ∣ b ∨ b ∣ a :=
  hC ha hb

end DivisibilityChain

/--
A primitive set hits a finite divisibility chain in at most one point.
-/
theorem primitiveOn_inter_chain_card_le_one
    {S C : Finset ℕ} (hS : PrimitiveOn S) (hC : DivisibilityChain C) :
    (S ∩ C).card ≤ 1 := by
  rw [Finset.card_le_one_iff]
  intro a b ha hb
  have haS : a ∈ S := (Finset.mem_inter.mp ha).1
  have haC : a ∈ C := (Finset.mem_inter.mp ha).2
  have hbS : b ∈ S := (Finset.mem_inter.mp hb).1
  have hbC : b ∈ C := (Finset.mem_inter.mp hb).2
  rcases hC.comparable haC hbC with hab | hba
  · exact hS.eq_of_dvd haS hbS hab
  · exact (hS.eq_of_dvd hbS haS hba).symm

/--
Pointwise form of `primitiveOn_inter_chain_card_le_one`.
-/
theorem primitiveOn_eq_of_mem_inter_chain
    {S C : Finset ℕ} (hS : PrimitiveOn S) (hC : DivisibilityChain C)
    {a b : ℕ} (ha : a ∈ S ∩ C) (hb : b ∈ S ∩ C) :
    a = b := by
  exact (Finset.card_le_one_iff.mp
    (primitiveOn_inter_chain_card_le_one hS hC)) ha hb

/--
Single-chain hitting mass bound.

If a primitive finite set `S` is observed along one finite divisibility chain
`C`, then all hits in `S ∩ C` can be assigned to a single source `r`.  Provided
each hit has mass at most the source mass, the total hit mass is at most the
singleton source mass.
-/
theorem primitive_chain_hitSetMass_le_single_source
    (M : MassSpace ℕ) {S C : Finset ℕ} {r : ℕ}
    (hS : PrimitiveOn S) (hC : DivisibilityChain C)
    (hmass : ∀ h ∈ S ∩ C, M.μ h ≤ M.μ r) :
    hitSetMass M (S ∩ C) ≤ sourceSetMass M ({r} : Finset ℕ) := by
  classical
  refine hitSetMass_le_sourceSetMass_of_injective_assignment M ?_
  exact
    { assign := fun _ => r
      assign_mem := by
        intro h _hh
        simp
      injective_on_hits := by
        intro a ha b hb _hab
        exact primitiveOn_eq_of_mem_inter_chain hS hC ha hb
      mass_le_assign := by
        intro h hh
        exact hmass h hh }

/--
Concrete divisibility-chain sample: `{2, 4, 8}` is a finite chain.
-/
theorem divisibilityChain_two_four_eight :
    DivisibilityChain ({2, 4, 8} : Finset ℕ) := by
  intro a b ha hb
  fin_cases ha <;> fin_cases hb <;> norm_num

/--
Concrete sample: the primitive set `{2, 3}` hits the chain `{2, 4, 8}` in at
most one point.
-/
theorem primitive_two_three_hits_two_four_eight_card_le_one :
    (({2, 3} : Finset ℕ) ∩ ({2, 4, 8} : Finset ℕ)).card ≤ 1 := by
  exact primitiveOn_inter_chain_card_le_one
    primitiveOn_pair_two_three
    divisibilityChain_two_four_eight

end DkMath.NumberTheory.PrimitiveSet
