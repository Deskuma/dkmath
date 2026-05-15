/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PrimitiveSet.PrimeDescent

#print "file: DkMath.NumberTheory.PrimitiveSet.PrimePath"

namespace DkMath.NumberTheory.PrimitiveSet

open DkMath.CosmicFormula.Mass

/--
Multi-step prime descent reachability.

`PrimeReachable n m` means that `m` is reached from `n` by zero or more
`PrimeDescentStep`s.
-/
def PrimeReachable (n m : ℕ) : Prop :=
  Relation.ReflTransGen PrimeDescentStep n m

namespace PrimeReachable

/-- Prime reachability is reflexive. -/
theorem refl (n : ℕ) : PrimeReachable n n :=
  Relation.ReflTransGen.refl

/-- A single prime descent step gives prime reachability. -/
theorem single {n m : ℕ} (h : PrimeDescentStep n m) :
    PrimeReachable n m :=
  Relation.ReflTransGen.single h

/-- Prime reachability is transitive. -/
theorem trans {a b c : ℕ} (hab : PrimeReachable a b) (hbc : PrimeReachable b c) :
    PrimeReachable a c :=
  Relation.ReflTransGen.trans hab hbc

/--
Every multi-step prime descent target divides its source.
-/
theorem dvd_source {n m : ℕ} (h : PrimeReachable n m) : m ∣ n := by
  induction h with
  | refl =>
      exact dvd_rfl
  | tail _hxy hyz ih =>
      exact dvd_trans hyz.dvd_source ih

end PrimeReachable

/--
A finite chain family controlled by multi-step prime reachability from chosen
sources.
-/
structure PrimeReachableControlledChainFamily
    (ι : Type _) [DecidableEq ι]
    extends DivisibilityChainFamily ι where
  source : ι → ℕ
  chain_reachable :
    ∀ i ∈ index, ∀ h ∈ chain i, PrimeReachable (source i) h

namespace PrimeReachableControlledChainFamily

/-- Forget multi-step prime reachability control to divisibility control. -/
def toDvdControlled
    {ι : Type _} [DecidableEq ι]
    (F : PrimeReachableControlledChainFamily ι) :
    DvdControlledChainFamily ι where
  index := F.index
  chain := F.chain
  chain_is_chain := F.chain_is_chain
  source := F.source
  chain_dvd_source := by
    intro i hi h hh
    exact (F.chain_reachable i hi h hh).dvd_source

@[simp] theorem toDvdControlled_index
    {ι : Type _} [DecidableEq ι]
    (F : PrimeReachableControlledChainFamily ι) :
    F.toDvdControlled.index = F.index := rfl

@[simp] theorem toDvdControlled_chain
    {ι : Type _} [DecidableEq ι]
    (F : PrimeReachableControlledChainFamily ι) :
    F.toDvdControlled.chain = F.chain := rfl

@[simp] theorem toDvdControlled_source
    {ι : Type _} [DecidableEq ι]
    (F : PrimeReachableControlledChainFamily ι) :
    F.toDvdControlled.source = F.source := rfl

/--
Primitive hitting bound supplied by multi-step prime reachability plus
divisibility-monotone mass.
-/
theorem primitive_hitMass_le_sourceMass
    {ι : Type _} [DecidableEq ι]
    {M : MassSpace ℕ} {S : Finset ℕ}
    (hS : PrimitiveOn S)
    (F : PrimeReachableControlledChainFamily ι)
    (hM : DvdMonotoneMass M) :
    (F.toDvdControlled.toSourceControlled hM).hitMass S ≤
      (F.toDvdControlled.toSourceControlled hM).sourceMass := by
  exact F.toDvdControlled.primitive_hitMass_le_sourceMass hS hM

end PrimeReachableControlledChainFamily

/-- Concrete prime descent step: `4 -> 2`. -/
theorem primeDescentStep_four_two :
    PrimeDescentStep 4 2 := by
  refine ⟨2, by norm_num, by norm_num, ?_⟩
  norm_num

/-- Concrete prime descent step: `3 -> 1`. -/
theorem primeDescentStep_three_one :
    PrimeDescentStep 3 1 := by
  refine ⟨3, by norm_num, by norm_num, ?_⟩
  norm_num

/-- Concrete multi-step prime reachability: `8 -> 4 -> 2`. -/
theorem primeReachable_eight_two :
    PrimeReachable 8 2 :=
  (PrimeReachable.single primeDescentStep_eight_four).trans
    (PrimeReachable.single primeDescentStep_four_two)

/-- Concrete multi-step prime reachability: `9 -> 3 -> 1`. -/
theorem primeReachable_nine_one :
    PrimeReachable 9 1 :=
  (PrimeReachable.single primeDescentStep_nine_three).trans
    (PrimeReachable.single primeDescentStep_three_one)

/-- A Bool-indexed multi-step prime reachable sample. -/
def samplePrimeReachableControlledBoolChainFamily :
    PrimeReachableControlledChainFamily Bool where
  index := {false, true}
  chain := fun b => if b then ({1} : Finset ℕ) else ({2} : Finset ℕ)
  chain_is_chain := by
    intro b hb
    cases b
    · intro a c ha hc
      simp only [Bool.false_eq_true, ↓reduceIte, Finset.mem_singleton] at ha hc
      subst a
      subst c
      exact Or.inl dvd_rfl
    · intro a c ha hc
      simp only [↓reduceIte, Finset.mem_singleton] at ha hc
      subst a
      subst c
      exact Or.inl dvd_rfl
  source := fun b => if b then 9 else 8
  chain_reachable := by
    intro b hb h hh
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte, Finset.mem_singleton] at hh
      subst h
      simpa only [Bool.false_eq_true, ↓reduceIte] using primeReachable_eight_two
    · simp only [↓reduceIte, Finset.mem_singleton] at hh
      subst h
      simpa only [↓reduceIte] using primeReachable_nine_one

/--
Concrete multi-step sample: `{2, 5}` hitting the two reachable chains has
indexed unit hit mass bounded by source mass.
-/
theorem primitive_two_five_samplePrimeReachableControlledBoolChainFamily_hitMass_le_sourceMass :
    (samplePrimeReachableControlledBoolChainFamily.toDvdControlled.toSourceControlled
      unitNatMassSpace_dvdMonotone).hitMass ({2, 5} : Finset ℕ) ≤
      (samplePrimeReachableControlledBoolChainFamily.toDvdControlled.toSourceControlled
        unitNatMassSpace_dvdMonotone).sourceMass := by
  have hS : PrimitiveOn ({2, 5} : Finset ℕ) := by
    exact primitiveOn_pair (by norm_num) (by norm_num)
  exact samplePrimeReachableControlledBoolChainFamily.primitive_hitMass_le_sourceMass
    hS unitNatMassSpace_dvdMonotone

end DkMath.NumberTheory.PrimitiveSet
