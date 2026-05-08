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

/--
Erdos-route name for a finite divisibility chain.

For now this is definitionally the same as `DivisibilityChain`; later files can
refine descent by an actual step relation without changing the primitive
hitting lemmas that only need comparability.
-/
abbrev DescentChain (C : Finset ℕ) : Prop :=
  DivisibilityChain C

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
A finite family of divisibility chains.

The family is indexed by a finite `Finset`.  This keeps the first forest layer
finite and avoids committing to a concrete probability space.
-/
structure DivisibilityChainFamily (ι : Type _) [DecidableEq ι] where
  index : Finset ι
  chain : ι → Finset ℕ
  chain_is_chain : ∀ i ∈ index, DivisibilityChain (chain i)

namespace DivisibilityChainFamily

/-- A chain family member is a finite descent chain in the current sense. -/
theorem descentChain
    {ι : Type _} [DecidableEq ι]
    (F : DivisibilityChainFamily ι) {i : ι} (hi : i ∈ F.index) :
    DescentChain (F.chain i) :=
  F.chain_is_chain i hi

/-- Indexed total hit mass over a finite chain family. -/
def hitMass
    {ι : Type _} [DecidableEq ι]
    (M : MassSpace ℕ) (S : Finset ℕ) (F : DivisibilityChainFamily ι) : ℚ :=
  F.index.sum fun i => hitSetMass M (S ∩ F.chain i)

/-- Indexed total singleton-source mass over a finite chain family. -/
def sourceMass
    {ι : Type _} [DecidableEq ι]
    (M : MassSpace ℕ) (F : DivisibilityChainFamily ι) (source : ι → ℕ) : ℚ :=
  F.index.sum fun i => M.μ (source i)

@[simp] theorem hitMass_empty_index
    {ι : Type _} [DecidableEq ι]
    (M : MassSpace ℕ) (S : Finset ℕ)
    (chain : ι → Finset ℕ)
    (hchain : ∀ i ∈ (∅ : Finset ι), DivisibilityChain (chain i)) :
    hitMass M S { index := ∅, chain := chain, chain_is_chain := hchain } = 0 := by
  simp [hitMass]

@[simp] theorem sourceMass_empty_index
    {ι : Type _} [DecidableEq ι]
    (M : MassSpace ℕ) (source : ι → ℕ)
    (chain : ι → Finset ℕ)
    (hchain : ∀ i ∈ (∅ : Finset ι), DivisibilityChain (chain i)) :
    sourceMass M { index := ∅, chain := chain, chain_is_chain := hchain } source = 0 := by
  simp [sourceMass]

/--
Each primitive set hits every chain of a finite chain family in at most one
point.
-/
theorem primitiveOn_inter_chain_card_le_one
    {ι : Type _} [DecidableEq ι]
    {S : Finset ℕ} (hS : PrimitiveOn S)
    (F : DivisibilityChainFamily ι) {i : ι} (hi : i ∈ F.index) :
    (S ∩ F.chain i).card ≤ 1 :=
  PrimitiveSet.primitiveOn_inter_chain_card_le_one hS (F.chain_is_chain i hi)

/--
Finite chain-family hitting bound.

For each chain `F.chain i`, the primitive set can hit at most once.  If every
hit on that chain has mass at most the chosen source `source i`, then the
indexed sum of hit masses is bounded by the indexed sum of source masses.
-/
theorem primitive_hitMass_le_sourceMass
    {ι : Type _} [DecidableEq ι]
    (M : MassSpace ℕ) {S : Finset ℕ}
    (hS : PrimitiveOn S)
    (F : DivisibilityChainFamily ι) (source : ι → ℕ)
    (hmass : ∀ i ∈ F.index, ∀ h ∈ S ∩ F.chain i, M.μ h ≤ M.μ (source i)) :
    F.hitMass M S ≤ F.sourceMass M source := by
  classical
  unfold hitMass sourceMass
  exact Finset.sum_le_sum fun i hi =>
    calc
      hitSetMass M (S ∩ F.chain i)
          ≤ sourceSetMass M ({source i} : Finset ℕ) := by
            exact primitive_chain_hitSetMass_le_single_source
              M hS (F.chain_is_chain i hi) (hmass i hi)
      _ = M.μ (source i) := by
            simp [sourceSetMass]

end DivisibilityChainFamily

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

/-- Concrete divisibility-chain sample: `{3, 9}` is a finite chain. -/
theorem divisibilityChain_three_nine :
    DivisibilityChain ({3, 9} : Finset ℕ) := by
  intro a b ha hb
  fin_cases ha <;> fin_cases hb <;> norm_num

/-- Two sample chains indexed by `Bool`. -/
def sampleBoolChainFamily : DivisibilityChainFamily Bool where
  index := {false, true}
  chain := fun b => if b then ({3, 9} : Finset ℕ) else ({2, 4, 8} : Finset ℕ)
  chain_is_chain := by
    intro b hb
    fin_cases hb
    · simpa using divisibilityChain_two_four_eight
    · simpa using divisibilityChain_three_nine

/-- Unit mass space for concrete finite-chain examples. -/
def unitNatMassSpace : MassSpace ℕ where
  μ := fun _ => 1
  nonneg := by
    intro _n
    norm_num

/--
Concrete sample: `{2, 3}` hitting two finite chains has indexed unit hit mass
bounded by the indexed unit source mass.
-/
theorem primitive_two_three_sampleBoolChainFamily_hitMass_le_sourceMass :
    sampleBoolChainFamily.hitMass unitNatMassSpace ({2, 3} : Finset ℕ) ≤
      sampleBoolChainFamily.sourceMass unitNatMassSpace (fun _ => 1) := by
  refine sampleBoolChainFamily.primitive_hitMass_le_sourceMass
    unitNatMassSpace primitiveOn_pair_two_three (fun _ => 1) ?_
  intro i _hi h _hh
  rfl

end DkMath.NumberTheory.PrimitiveSet
