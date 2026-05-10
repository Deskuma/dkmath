/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PrimitiveSet.PrimePathList

#print "file: DkMath.NumberTheory.PrimitiveSet.PathFamily"

namespace DkMath.NumberTheory.PrimitiveSet

open DkMath.CosmicFormula.Mass

/--
A finite family of nonempty list-shaped prime descent paths.

Each indexed path is represented as `source i :: tail i`, so later bridges can
use the head as the source mass for the whole chain.
-/
structure AdjacentPrimePathFamily (ι : Type _) [DecidableEq ι] where
  index : Finset ι
  source : ι → ℕ
  tail : ι → List ℕ
  isPath : ∀ i ∈ index, AdjacentPrimePath (source i :: tail i)

namespace AdjacentPrimePathFamily

/-- The concrete list path at index `i`. -/
def path
    {ι : Type _} [DecidableEq ι]
    (F : AdjacentPrimePathFamily ι) (i : ι) :
    List ℕ :=
  F.source i :: F.tail i

/-- The node set of the indexed list path. -/
def nodeSet
    {ι : Type _} [DecidableEq ι]
    (F : AdjacentPrimePathFamily ι) (i : ι) :
    Finset ℕ :=
  (F.path i).toFinset

/-- Forget a family of prime paths to a family of divisibility chains. -/
def toDivisibilityChainFamily
    {ι : Type _} [DecidableEq ι]
    (F : AdjacentPrimePathFamily ι) :
    DivisibilityChainFamily ι where
  index := F.index
  chain := F.nodeSet
  chain_is_chain := by
    intro i hi
    exact divisibilityChain_toFinset_of_adjacentPrimePath (F.isPath i hi)

@[simp] theorem toDivisibilityChainFamily_index
    {ι : Type _} [DecidableEq ι]
    (F : AdjacentPrimePathFamily ι) :
    F.toDivisibilityChainFamily.index = F.index := rfl

@[simp] theorem toDivisibilityChainFamily_chain
    {ι : Type _} [DecidableEq ι]
    (F : AdjacentPrimePathFamily ι) :
    F.toDivisibilityChainFamily.chain = F.nodeSet := rfl

/--
Forget a family of prime paths to a reachable-controlled chain family.

The reachability proof is supplied by the list path theorem already proved in
`PrimePathList`.
-/
def toPrimeReachableControlledChainFamily
    {ι : Type _} [DecidableEq ι]
    (F : AdjacentPrimePathFamily ι) :
    PrimeReachableControlledChainFamily ι where
  index := F.index
  chain := F.nodeSet
  chain_is_chain := F.toDivisibilityChainFamily.chain_is_chain
  source := F.source
  chain_reachable := by
    intro i hi h hh
    exact mem_reachable_from_head_of_adjacentPrimePath (F.isPath i hi)
      (by
        simpa [nodeSet, path] using hh)

@[simp] theorem toPrimeReachableControlledChainFamily_index
    {ι : Type _} [DecidableEq ι]
    (F : AdjacentPrimePathFamily ι) :
    F.toPrimeReachableControlledChainFamily.index = F.index := rfl

@[simp] theorem toPrimeReachableControlledChainFamily_chain
    {ι : Type _} [DecidableEq ι]
    (F : AdjacentPrimePathFamily ι) :
    F.toPrimeReachableControlledChainFamily.chain = F.nodeSet := rfl

@[simp] theorem toPrimeReachableControlledChainFamily_source
    {ι : Type _} [DecidableEq ι]
    (F : AdjacentPrimePathFamily ι) :
    F.toPrimeReachableControlledChainFamily.source = F.source := rfl

/--
Primitive hitting bound for a finite family of list-shaped prime paths, supplied
by divisibility-monotone mass after forgetting to reachability control.
-/
theorem primitive_hitMass_le_sourceMass
    {ι : Type _} [DecidableEq ι]
    {M : MassSpace ℕ} {S : Finset ℕ}
    (hS : PrimitiveOn S)
    (F : AdjacentPrimePathFamily ι)
    (hM : DvdMonotoneMass M) :
    (F.toPrimeReachableControlledChainFamily.toDvdControlled.toSourceControlled
      hM).hitMass S ≤
      (F.toPrimeReachableControlledChainFamily.toDvdControlled.toSourceControlled
        hM).sourceMass := by
  exact F.toPrimeReachableControlledChainFamily.primitive_hitMass_le_sourceMass hS hM

end AdjacentPrimePathFamily

/-- Concrete list-shaped prime path `9 -> 3 -> 1`. -/
theorem adjacentPrimePath_nine_three_one :
    AdjacentPrimePath [9, 3, 1] := by
  simp only [AdjacentPrimePath, List.isChain_cons_cons, List.isChain_singleton,
    and_true]
  exact ⟨primeDescentStep_nine_three, primeDescentStep_three_one⟩

/-- A Bool-indexed family of two nonempty prime descent paths. -/
def sampleAdjacentPrimePathBoolFamily :
    AdjacentPrimePathFamily Bool where
  index := {false, true}
  source := fun b => if b then 9 else 8
  tail := fun b => if b then [3, 1] else [4, 2]
  isPath := by
    intro b hb
    cases b
    · simpa only [Bool.false_eq_true, ↓reduceIte] using adjacentPrimePath_eight_four_two
    · simpa only [↓reduceIte] using adjacentPrimePath_nine_three_one

/-- The Bool path-family sample as a source-controlled family for unit mass. -/
def sampleAdjacentPrimePathBoolFamilySourceControlled :
    SourceControlledChainFamily unitNatMassSpace Bool :=
  sampleAdjacentPrimePathBoolFamily.toPrimeReachableControlledChainFamily
    |>.toDvdControlled
    |>.toSourceControlled unitNatMassSpace_dvdMonotone

/--
Concrete sample: primitive `{2,5}` hitting a two-path family has indexed unit
hit mass bounded by the indexed source mass.
-/
theorem primitive_two_five_sampleAdjacentPrimePathBoolFamily_hitMass_le_sourceMass :
    sampleAdjacentPrimePathBoolFamilySourceControlled.hitMass ({2, 5} : Finset ℕ) ≤
      sampleAdjacentPrimePathBoolFamilySourceControlled.sourceMass := by
  have hS : PrimitiveOn ({2, 5} : Finset ℕ) := by
    exact primitiveOn_pair (by norm_num) (by norm_num)
  exact sampleAdjacentPrimePathBoolFamilySourceControlled.primitive_hitMass_le_sourceMass hS

end DkMath.NumberTheory.PrimitiveSet
