/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PrimitiveSet.BranchBridge

#print "file: DkMath.NumberTheory.PrimitiveSet.DescentBridge"

namespace DkMath.NumberTheory.PrimitiveSet

open DkMath.CosmicFormula.Mass

/--
Mass monotonicity along divisibility descent.

The convention is that `a ∣ b` means `a` is a lower divisor of `b`, so a
divisibility-monotone mass satisfies `μ a <= μ b`.
-/
def DvdMonotoneMass (M : MassSpace ℕ) : Prop :=
  ∀ ⦃a b : ℕ⦄, a ∣ b → M.μ a ≤ M.μ b

/--
A finite chain family controlled by divisibility below chosen source nodes.

This is the lightest descent provider: every point on the `i`-th chain divides
the source `source i`.
-/
structure DvdControlledChainFamily
    (ι : Type _) [DecidableEq ι]
    extends DivisibilityChainFamily ι where
  source : ι → ℕ
  chain_dvd_source :
    ∀ i ∈ index, ∀ h ∈ chain i, h ∣ source i

namespace DvdControlledChainFamily

/--
Divisibility-controlled one-step divisor-descent family at source `n`.

For each indexed divisor label `q`, the chain is `{n / q, n}` and the source is
`n`. The divisor hypothesis supplies `n / q ∣ n`, so each chain is comparable
by divisibility and lies below its source.
-/
def divisorStep
    (n : ℕ) (I : Finset ℕ)
    (hdiv : ∀ q ∈ I, q ∣ n) :
    DvdControlledChainFamily ℕ where
  index := I
  chain := fun q => ({n / q, n} : Finset ℕ)
  chain_is_chain := by
    intro q hq a b ha hb
    have hchild : n / q ∣ n := Nat.div_dvd_of_dvd (hdiv q hq)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact Or.inl (dvd_refl (n / q))
    · exact Or.inl hchild
    · exact Or.inr hchild
    · exact Or.inl (dvd_refl _)
  source := fun _ => n
  chain_dvd_source := by
    intro q hq h hh
    have hchild : n / q ∣ n := Nat.div_dvd_of_dvd (hdiv q hq)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hh
    rcases hh with rfl | rfl
    · exact hchild
    · exact dvd_refl _

@[simp] theorem divisorStep_index
    (n : ℕ) (I : Finset ℕ)
    (hdiv : ∀ q ∈ I, q ∣ n) :
    (divisorStep n I hdiv).index = I := rfl

@[simp] theorem divisorStep_chain
    (n : ℕ) (I : Finset ℕ)
    (hdiv : ∀ q ∈ I, q ∣ n) :
    (divisorStep n I hdiv).chain = fun q => ({n / q, n} : Finset ℕ) := rfl

@[simp] theorem divisorStep_source
    (n : ℕ) (I : Finset ℕ)
    (hdiv : ∀ q ∈ I, q ∣ n) :
    (divisorStep n I hdiv).source = fun _ => n := rfl

/--
Convert a divisibility-controlled forest into a source-controlled forest using
a divisibility-monotone mass.
-/
def toSourceControlled
    {ι : Type _} [DecidableEq ι]
    {M : MassSpace ℕ}
    (F : DvdControlledChainFamily ι)
    (hM : DvdMonotoneMass M) :
    SourceControlledChainFamily M ι where
  index := F.index
  chain := F.chain
  chain_is_chain := F.chain_is_chain
  source := F.source
  mass_le_source := by
    intro i hi h hh
    exact hM (F.chain_dvd_source i hi h hh)

@[simp] theorem toSourceControlled_index
    {ι : Type _} [DecidableEq ι]
    {M : MassSpace ℕ}
    (F : DvdControlledChainFamily ι)
    (hM : DvdMonotoneMass M) :
    (F.toSourceControlled hM).index = F.index := rfl

@[simp] theorem toSourceControlled_chain
    {ι : Type _} [DecidableEq ι]
    {M : MassSpace ℕ}
    (F : DvdControlledChainFamily ι)
    (hM : DvdMonotoneMass M) :
    (F.toSourceControlled hM).chain = F.chain := rfl

@[simp] theorem toSourceControlled_source
    {ι : Type _} [DecidableEq ι]
    {M : MassSpace ℕ}
    (F : DvdControlledChainFamily ι)
    (hM : DvdMonotoneMass M) :
    (F.toSourceControlled hM).source = F.source := rfl

/--
Primitive hitting bound supplied by divisibility descent plus monotone mass.
-/
theorem primitive_hitMass_le_sourceMass
    {ι : Type _} [DecidableEq ι]
    {M : MassSpace ℕ} {S : Finset ℕ}
    (hS : PrimitiveOn S)
    (F : DvdControlledChainFamily ι)
    (hM : DvdMonotoneMass M) :
    (F.toSourceControlled hM).hitMass S ≤
      (F.toSourceControlled hM).sourceMass := by
  exact (F.toSourceControlled hM).primitive_hitMass_le_sourceMass hS

end DvdControlledChainFamily

namespace SourceControlledChainFamily

/--
Source-controlled one-step divisor-descent family at source `n`.

This is `DvdControlledChainFamily.divisorStep` converted by a
divisibility-monotone mass. Its index is definitionally the supplied index,
which keeps compatibility with divisor-channel providers lightweight.
-/
def ofDivisorStep
    {M : MassSpace ℕ}
    (hM : DvdMonotoneMass M)
    (n : ℕ) (I : Finset ℕ)
    (hdiv : ∀ q ∈ I, q ∣ n) :
    SourceControlledChainFamily M ℕ :=
  (DvdControlledChainFamily.divisorStep n I hdiv).toSourceControlled hM

@[simp] theorem ofDivisorStep_index
    {M : MassSpace ℕ}
    (hM : DvdMonotoneMass M)
    (n : ℕ) (I : Finset ℕ)
    (hdiv : ∀ q ∈ I, q ∣ n) :
    (ofDivisorStep hM n I hdiv).index = I := rfl

@[simp] theorem ofDivisorStep_chain
    {M : MassSpace ℕ}
    (hM : DvdMonotoneMass M)
    (n : ℕ) (I : Finset ℕ)
    (hdiv : ∀ q ∈ I, q ∣ n) :
    (ofDivisorStep hM n I hdiv).chain = fun q => ({n / q, n} : Finset ℕ) := rfl

@[simp] theorem ofDivisorStep_source
    {M : MassSpace ℕ}
    (hM : DvdMonotoneMass M)
    (n : ℕ) (I : Finset ℕ)
    (hdiv : ∀ q ∈ I, q ∣ n) :
    (ofDivisorStep hM n I hdiv).source = fun _ => n := rfl

end SourceControlledChainFamily

/-- The unit natural mass is monotone along divisibility. -/
theorem unitNatMassSpace_dvdMonotone :
    DvdMonotoneMass unitNatMassSpace := by
  intro _a _b _hab
  rfl

/--
The sample Bool-indexed chain family is controlled by divisibility below
sources `8` and `9`.
-/
def sampleDvdControlledBoolChainFamily : DvdControlledChainFamily Bool where
  index := sampleBoolChainFamily.index
  chain := sampleBoolChainFamily.chain
  chain_is_chain := sampleBoolChainFamily.chain_is_chain
  source := fun b => if b then 9 else 8
  chain_dvd_source := by
    intro b hb h hh
    fin_cases hb
    · simp only [sampleBoolChainFamily] at hh ⊢
      fin_cases hh <;> norm_num
    · simp only [sampleBoolChainFamily] at hh ⊢
      fin_cases hh <;> norm_num

/--
Concrete divisibility-controlled sample: `{2, 3}` hitting the sample forest has
indexed unit hit mass bounded by source mass.
-/
theorem primitive_two_three_sampleDvdControlledBoolChainFamily_hitMass_le_sourceMass :
    (sampleDvdControlledBoolChainFamily.toSourceControlled
      unitNatMassSpace_dvdMonotone).hitMass ({2, 3} : Finset ℕ) ≤
      (sampleDvdControlledBoolChainFamily.toSourceControlled
        unitNatMassSpace_dvdMonotone).sourceMass := by
  exact sampleDvdControlledBoolChainFamily.primitive_hitMass_le_sourceMass
    primitiveOn_pair_two_three
    unitNatMassSpace_dvdMonotone

end DkMath.NumberTheory.PrimitiveSet
