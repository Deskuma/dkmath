/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PrimitiveSet.Support
import DkMath.NumberTheory.PrimitiveSet.BranchPathFamily

#print "file: DkMath.NumberTheory.PrimitiveSet.ErdosFinite"

namespace DkMath.NumberTheory.PrimitiveSet

open DkMath.CosmicFormula.Mass

/--
Finite theorem-facing input for the primitive-set side of Erdos #1196.

The primitive antichain condition and the support lower bound are kept as
separate fields so downstream theorems can use either hypothesis explicitly.
-/
structure ErdosFinitePrimitiveInput (x : ℕ) where
  support : Finset ℕ
  primitive : PrimitiveOn support
  lowerBound : LowerBoundOn x support

namespace ErdosFinitePrimitiveInput

/-- A lower bound by at least `1` gives positivity of the support. -/
theorem positiveOn_of_one_le
    {x : ℕ} (I : ErdosFinitePrimitiveInput x) (hx : 1 ≤ x) :
    PositiveOn I.support :=
  lowerBoundOn_one_implies_positiveOn
    (LowerBoundOn.mono_left hx I.lowerBound)

/-- A support lower-bounded by at least `1` cannot contain `0`. -/
theorem not_mem_zero_of_one_le
    {x : ℕ} (I : ErdosFinitePrimitiveInput x) (hx : 1 ≤ x) :
    0 ∉ I.support :=
  not_mem_zero_of_positiveOn (I.positiveOn_of_one_le hx)

/-- A support lower-bounded by at least `2` cannot contain `1`. -/
theorem not_mem_one_of_two_le
    {x : ℕ} (I : ErdosFinitePrimitiveInput x) (hx : 2 ≤ x) :
    1 ∉ I.support :=
  not_mem_one_of_lowerBoundOn_two
    (LowerBoundOn.mono_left hx I.lowerBound)

/--
Branch-controlled finite Erdos hit bound.

This is the theorem-facing wrapper around
`AdjacentBranchPrimePathFamily.primitive_hitMass_le_sourceMass`: the primitive
set is supplied by the finite Erdos input package.
-/
theorem branchPrimePathFamily_hitMass_le_sourceMass
    {x : ℕ} {ι : Type _} [DecidableEq ι]
    {M : MassSpace ℕ} {B : Branching ℕ} [SubConservative M B]
    (I : ErdosFinitePrimitiveInput x)
    (F : AdjacentBranchPrimePathFamily ι B) :
    (F.toSourceControlledChainFamily M B).hitMass I.support ≤
      (F.toSourceControlledChainFamily M B).sourceMass := by
  exact F.primitive_hitMass_le_sourceMass I.primitive

end ErdosFinitePrimitiveInput

/-- Concrete finite Erdos input for the primitive support `{2,5}` above `2`. -/
def erdosFinitePrimitiveInput_two_five :
    ErdosFinitePrimitiveInput 2 where
  support := {2, 5}
  primitive := by
    exact primitiveOn_pair (by norm_num) (by norm_num)
  lowerBound := lowerBoundOn_pair_two_five

/-- The concrete input `{2,5}` is positive. -/
theorem erdosFinitePrimitiveInput_two_five_positiveOn :
    PositiveOn erdosFinitePrimitiveInput_two_five.support :=
  erdosFinitePrimitiveInput_two_five.positiveOn_of_one_le (by norm_num)

/-- The concrete input `{2,5}` does not contain `1`. -/
theorem erdosFinitePrimitiveInput_two_five_not_mem_one :
    1 ∉ erdosFinitePrimitiveInput_two_five.support :=
  erdosFinitePrimitiveInput_two_five.not_mem_one_of_two_le (by norm_num)

/--
Concrete theorem-facing sample: the finite Erdos input `{2,5}` hitting the
branch-controlled two-path family has hit mass bounded by source mass.
-/
theorem erdosFinitePrimitiveInput_two_five_branchPath_hitMass_le_sourceMass :
    sampleAdjacentBranchPrimePathBoolFamilySourceControlled.hitMass
      erdosFinitePrimitiveInput_two_five.support ≤
      sampleAdjacentBranchPrimePathBoolFamilySourceControlled.sourceMass := by
  exact erdosFinitePrimitiveInput_two_five.branchPrimePathFamily_hitMass_le_sourceMass
    sampleAdjacentBranchPrimePathBoolFamily

end DkMath.NumberTheory.PrimitiveSet
