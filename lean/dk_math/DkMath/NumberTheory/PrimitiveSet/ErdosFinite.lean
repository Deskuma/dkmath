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

/-!
Route-facing API naming convention:

- `<route>SourceControlled` packages the finite forest used by that route.
- `<route>HitMass` is the indexed mass of `I.support` hitting that forest.
- `<route>SourceMass` is the indexed mass of the route sources.
- `hitMass_le_sourceMass_of_<route>` is the theorem-facing bound.

The route name records where source control comes from.  Currently
`branchPrimePathFamily` uses `SubConservative M B`, while `primePathFamily`
uses `DvdMonotoneMass M`.
-/

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
The source-controlled forest obtained from a branch-controlled prime path
family and a subconservative branching.
-/
def branchPrimePathFamilySourceControlled
    {x : ℕ} {ι : Type _} [DecidableEq ι]
    (M : MassSpace ℕ) (B : Branching ℕ) [SubConservative M B]
    (_I : ErdosFinitePrimitiveInput x)
    (F : AdjacentBranchPrimePathFamily ι B) :
    SourceControlledChainFamily M ι :=
  F.toSourceControlledChainFamily M B

/--
Indexed hit mass of the finite Erdos support against a branch-controlled prime
path family.
-/
def branchPrimePathFamilyHitMass
    {x : ℕ} {ι : Type _} [DecidableEq ι]
    (M : MassSpace ℕ) (B : Branching ℕ) [SubConservative M B]
    (I : ErdosFinitePrimitiveInput x)
    (F : AdjacentBranchPrimePathFamily ι B) : ℚ :=
  (I.branchPrimePathFamilySourceControlled M B F).hitMass I.support

/--
Indexed source mass of a branch-controlled prime path family.
-/
def branchPrimePathFamilySourceMass
    {x : ℕ} {ι : Type _} [DecidableEq ι]
    (M : MassSpace ℕ) (B : Branching ℕ) [SubConservative M B]
    (I : ErdosFinitePrimitiveInput x)
    (F : AdjacentBranchPrimePathFamily ι B) : ℚ :=
  (I.branchPrimePathFamilySourceControlled M B F).sourceMass

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

/--
Named finite Erdos bound using the input-side hit/source mass wrappers.
-/
theorem hitMass_le_sourceMass_of_branchPrimePathFamily
    {x : ℕ} {ι : Type _} [DecidableEq ι]
    {M : MassSpace ℕ} {B : Branching ℕ} [SubConservative M B]
    (I : ErdosFinitePrimitiveInput x)
    (F : AdjacentBranchPrimePathFamily ι B) :
    I.branchPrimePathFamilyHitMass M B F ≤
      I.branchPrimePathFamilySourceMass M B F := by
  exact I.branchPrimePathFamily_hitMass_le_sourceMass F

/--
Alias emphasizing that source control is supplied by branch subconservativity.
-/
theorem hitMass_le_sourceMass_of_subconservativeBranchPrimePathFamily
    {x : ℕ} {ι : Type _} [DecidableEq ι]
    {M : MassSpace ℕ} {B : Branching ℕ} [SubConservative M B]
    (I : ErdosFinitePrimitiveInput x)
    (F : AdjacentBranchPrimePathFamily ι B) :
    I.branchPrimePathFamilyHitMass M B F ≤
      I.branchPrimePathFamilySourceMass M B F := by
  exact I.hitMass_le_sourceMass_of_branchPrimePathFamily F

/--
The source-controlled forest obtained from a prime path family using
divisibility-monotone mass.
-/
def primePathFamilySourceControlled
    {x : ℕ} {ι : Type _} [DecidableEq ι]
    (M : MassSpace ℕ) (_I : ErdosFinitePrimitiveInput x)
    (F : AdjacentPrimePathFamily ι) (hM : DvdMonotoneMass M) :
    SourceControlledChainFamily M ι :=
  F.toPrimeReachableControlledChainFamily.toDvdControlled.toSourceControlled hM

/--
Indexed hit mass of the finite Erdos support against a prime path family, using
divisibility-monotone mass for source control.
-/
def primePathFamilyHitMass
    {x : ℕ} {ι : Type _} [DecidableEq ι]
    (M : MassSpace ℕ) (I : ErdosFinitePrimitiveInput x)
    (F : AdjacentPrimePathFamily ι) (hM : DvdMonotoneMass M) : ℚ :=
  (I.primePathFamilySourceControlled M F hM).hitMass I.support

/--
Indexed source mass of a prime path family, using divisibility-monotone mass for
source control.
-/
def primePathFamilySourceMass
    {x : ℕ} {ι : Type _} [DecidableEq ι]
    (M : MassSpace ℕ) (I : ErdosFinitePrimitiveInput x)
    (F : AdjacentPrimePathFamily ι) (hM : DvdMonotoneMass M) : ℚ :=
  (I.primePathFamilySourceControlled M F hM).sourceMass

/--
Prime-path-family finite Erdos hit bound using divisibility-monotone mass.
-/
theorem hitMass_le_sourceMass_of_primePathFamily
    {x : ℕ} {ι : Type _} [DecidableEq ι]
    {M : MassSpace ℕ}
    (I : ErdosFinitePrimitiveInput x)
    (F : AdjacentPrimePathFamily ι) (hM : DvdMonotoneMass M) :
    I.primePathFamilyHitMass M F hM ≤
      I.primePathFamilySourceMass M F hM := by
  exact F.primitive_hitMass_le_sourceMass I.primitive hM

/--
Alias emphasizing that source control is supplied by divisibility-monotone mass.
-/
theorem hitMass_le_sourceMass_of_dvdMonotonePrimePathFamily
    {x : ℕ} {ι : Type _} [DecidableEq ι]
    {M : MassSpace ℕ}
    (I : ErdosFinitePrimitiveInput x)
    (F : AdjacentPrimePathFamily ι) (hM : DvdMonotoneMass M) :
    I.primePathFamilyHitMass M F hM ≤
      I.primePathFamilySourceMass M F hM := by
  exact I.hitMass_le_sourceMass_of_primePathFamily F hM

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

/--
Concrete theorem-facing sample using the input-side hit/source mass wrapper
names.
-/
theorem erdosFinitePrimitiveInput_two_five_named_hitMass_le_sourceMass :
    erdosFinitePrimitiveInput_two_five.branchPrimePathFamilyHitMass
      unitNatMassSpace sampleBranching_eight_nine_paths
      sampleAdjacentBranchPrimePathBoolFamily ≤
    erdosFinitePrimitiveInput_two_five.branchPrimePathFamilySourceMass
      unitNatMassSpace sampleBranching_eight_nine_paths
      sampleAdjacentBranchPrimePathBoolFamily := by
  exact erdosFinitePrimitiveInput_two_five
    |>.hitMass_le_sourceMass_of_branchPrimePathFamily
      sampleAdjacentBranchPrimePathBoolFamily

/--
Concrete theorem-facing sample for the prime-path-family / dvd-monotone route.
-/
theorem erdosFinitePrimitiveInput_two_five_primePath_hitMass_le_sourceMass :
    erdosFinitePrimitiveInput_two_five.primePathFamilyHitMass
      unitNatMassSpace sampleAdjacentPrimePathBoolFamily
      unitNatMassSpace_dvdMonotone ≤
    erdosFinitePrimitiveInput_two_five.primePathFamilySourceMass
      unitNatMassSpace sampleAdjacentPrimePathBoolFamily
      unitNatMassSpace_dvdMonotone := by
  exact erdosFinitePrimitiveInput_two_five
    |>.hitMass_le_sourceMass_of_primePathFamily
      sampleAdjacentPrimePathBoolFamily unitNatMassSpace_dvdMonotone

/--
Concrete branch-route sample using the alias that names subconservativity.
-/
theorem erdosFinitePrimitiveInput_two_five_subconservativeBranch_alias :
    erdosFinitePrimitiveInput_two_five.branchPrimePathFamilyHitMass
      unitNatMassSpace sampleBranching_eight_nine_paths
      sampleAdjacentBranchPrimePathBoolFamily ≤
    erdosFinitePrimitiveInput_two_five.branchPrimePathFamilySourceMass
      unitNatMassSpace sampleBranching_eight_nine_paths
      sampleAdjacentBranchPrimePathBoolFamily := by
  exact erdosFinitePrimitiveInput_two_five
    |>.hitMass_le_sourceMass_of_subconservativeBranchPrimePathFamily
      sampleAdjacentBranchPrimePathBoolFamily

/--
Concrete prime-route sample using the alias that names divisibility monotonicity.
-/
theorem erdosFinitePrimitiveInput_two_five_dvdMonotonePrime_alias :
    erdosFinitePrimitiveInput_two_five.primePathFamilyHitMass
      unitNatMassSpace sampleAdjacentPrimePathBoolFamily
      unitNatMassSpace_dvdMonotone ≤
    erdosFinitePrimitiveInput_two_five.primePathFamilySourceMass
      unitNatMassSpace sampleAdjacentPrimePathBoolFamily
      unitNatMassSpace_dvdMonotone := by
  exact erdosFinitePrimitiveInput_two_five
    |>.hitMass_le_sourceMass_of_dvdMonotonePrimePathFamily
      sampleAdjacentPrimePathBoolFamily unitNatMassSpace_dvdMonotone

end DkMath.NumberTheory.PrimitiveSet
