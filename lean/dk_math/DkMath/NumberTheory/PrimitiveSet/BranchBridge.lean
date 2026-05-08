/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PrimitiveSet.HittingBridge

#print "file: DkMath.NumberTheory.PrimitiveSet.BranchBridge"

namespace DkMath.NumberTheory.PrimitiveSet

open DkMath.CosmicFormula.Mass

/--
A finite chain family whose chains are controlled by chosen source nodes.

The field `mass_le_source` is the finite placeholder for the later
`Branching`/`SubConservative` or actual descent argument that every observed
hit below a source has mass at most the source mass.
-/
structure SourceControlledChainFamily
    (M : MassSpace ℕ) (ι : Type _) [DecidableEq ι]
    extends DivisibilityChainFamily ι where
  source : ι → ℕ
  mass_le_source :
    ∀ i ∈ index, ∀ h ∈ chain i, M.μ h ≤ M.μ (source i)

namespace SourceControlledChainFamily

/-- Indexed hit mass of a source-controlled chain family. -/
def hitMass
    {ι : Type _} [DecidableEq ι]
    {M : MassSpace ℕ} (F : SourceControlledChainFamily M ι)
    (S : Finset ℕ) : ℚ :=
  F.toDivisibilityChainFamily.hitMass M S

/-- Indexed source mass of a source-controlled chain family. -/
def sourceMass
    {ι : Type _} [DecidableEq ι]
    {M : MassSpace ℕ} (F : SourceControlledChainFamily M ι) : ℚ :=
  F.toDivisibilityChainFamily.sourceMass M F.source

@[simp] theorem hitMass_empty_index
    {ι : Type _} [DecidableEq ι]
    (M : MassSpace ℕ) (S : Finset ℕ)
    (chain : ι → Finset ℕ)
    (hchain : ∀ i ∈ (∅ : Finset ι), DivisibilityChain (chain i))
    (source : ι → ℕ)
    (hmass :
      ∀ i ∈ (∅ : Finset ι), ∀ h ∈ chain i, M.μ h ≤ M.μ (source i)) :
    hitMass
      { index := ∅
        chain := chain
        chain_is_chain := hchain
        source := source
        mass_le_source := hmass } S = 0 := by
  simp [hitMass]

@[simp] theorem sourceMass_empty_index
    {ι : Type _} [DecidableEq ι]
    (M : MassSpace ℕ)
    (chain : ι → Finset ℕ)
    (hchain : ∀ i ∈ (∅ : Finset ι), DivisibilityChain (chain i))
    (source : ι → ℕ)
    (hmass :
      ∀ i ∈ (∅ : Finset ι), ∀ h ∈ chain i, M.μ h ≤ M.μ (source i)) :
    sourceMass
      { index := ∅
        chain := chain
        chain_is_chain := hchain
        source := source
        mass_le_source := hmass } = 0 := by
  simp [sourceMass]

/--
Source-controlled primitive forest bound.

This is a convenience wrapper around
`DivisibilityChainFamily.primitive_hitMass_le_sourceMass`: the per-chain mass
hypothesis is supplied by the `SourceControlledChainFamily` package.
-/
theorem primitive_hitMass_le_sourceMass
    {ι : Type _} [DecidableEq ι]
    {M : MassSpace ℕ} {S : Finset ℕ}
    (hS : PrimitiveOn S)
    (F : SourceControlledChainFamily M ι) :
    F.hitMass S ≤ F.sourceMass := by
  classical
  exact F.toDivisibilityChainFamily.primitive_hitMass_le_sourceMass
    M hS F.source
    (by
      intro i hi h hh
      exact F.mass_le_source i hi h (Finset.mem_inter.mp hh).2)

end SourceControlledChainFamily

/--
The sample Bool-indexed chain family is source-controlled for unit mass.
-/
def sampleSourceControlledBoolChainFamily :
    SourceControlledChainFamily unitNatMassSpace Bool where
  index := sampleBoolChainFamily.index
  chain := sampleBoolChainFamily.chain
  chain_is_chain := sampleBoolChainFamily.chain_is_chain
  source := fun _ => 1
  mass_le_source := by
    intro _i _hi _h _hh
    rfl

/--
Concrete source-controlled sample: `{2, 3}` hitting the two sample chains has
indexed unit hit mass bounded by the packaged source mass.
-/
theorem primitive_two_three_sampleSourceControlledBoolChainFamily_hitMass_le_sourceMass :
    sampleSourceControlledBoolChainFamily.hitMass ({2, 3} : Finset ℕ) ≤
      sampleSourceControlledBoolChainFamily.sourceMass := by
  exact sampleSourceControlledBoolChainFamily.primitive_hitMass_le_sourceMass
    primitiveOn_pair_two_three

end DkMath.NumberTheory.PrimitiveSet
