/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PrimitiveSet.ShadowHittingBridge

#print "file: DkMath.NumberTheory.PrimitiveSet.CapacityKernelHittingBridge"

namespace DkMath.Kernel

open DkMath.CosmicFormula.Mass
open DkMath.NumberTheory.PrimitiveSet

namespace CapacityKernel

/--
The normalized shadow of a positive-capacity kernel is compatible with a
source-controlled family whose index is the outgoing channel set at `s`.
-/
theorem normalizedSubMarkovShadow_providerAt_compatible
    {σ ι : Type _} [DecidableEq ι]
    (K : CapacityKernel σ ι) (hcap : ∀ s, 0 < K.capacity s)
    (s : σ) {M : MassSpace ℕ}
    (F : SourceControlledChainFamily M ι)
    (hindex : K.children s = F.index) :
    ((SubMarkovShadow.ofCapacityKernel K hcap).providerAt s).Compatible F := by
  simpa [RealWeightProvider.Compatible] using hindex

/--
Apply the normalized shadow of a positive-capacity kernel at state `s` to a
compatible source-controlled chain family.
-/
noncomputable def applyAtToSourceControlled
    {σ ι : Type _} [DecidableEq ι]
    (K : CapacityKernel σ ι) (hcap : ∀ s, 0 < K.capacity s)
    (s : σ) {M : MassSpace ℕ}
    (F : SourceControlledChainFamily M ι)
    (hindex : K.children s = F.index) :
    RealWeightedPathFamily M ι :=
  (SubMarkovShadow.ofCapacityKernel K hcap).applyAtToSourceControlled
    s F
    (K.normalizedSubMarkovShadow_providerAt_compatible hcap s F hindex)

@[simp] theorem applyAtToSourceControlled_index
    {σ ι : Type _} [DecidableEq ι]
    (K : CapacityKernel σ ι) (hcap : ∀ s, 0 < K.capacity s)
    (s : σ) {M : MassSpace ℕ}
    (F : SourceControlledChainFamily M ι)
    (hindex : K.children s = F.index) :
    (K.applyAtToSourceControlled hcap s F hindex).index = F.index :=
  rfl

@[simp] theorem applyAtToSourceControlled_weight
    {σ ι : Type _} [DecidableEq ι]
    (K : CapacityKernel σ ι) (hcap : ∀ s, 0 < K.capacity s)
    (s : σ) {M : MassSpace ℕ}
    (F : SourceControlledChainFamily M ι)
    (hindex : K.children s = F.index) :
    (K.applyAtToSourceControlled hcap s F hindex).weight =
      K.normalizedWeight s :=
  rfl

/--
Applying a positive-capacity kernel's normalized shadow gives a
sub-probability weighted path family.
-/
theorem applyAtToSourceControlled_weightSubProbability
    {σ ι : Type _} [DecidableEq ι]
    (K : CapacityKernel σ ι) (hcap : ∀ s, 0 < K.capacity s)
    (s : σ) {M : MassSpace ℕ}
    (F : SourceControlledChainFamily M ι)
    (hindex : K.children s = F.index) :
    (K.applyAtToSourceControlled hcap s F hindex).WeightSubProbability :=
  (SubMarkovShadow.ofCapacityKernel K hcap)
    |>.applyAtToSourceControlled_weightSubProbability
      (SubMarkovShadow.ofCapacityKernel_subProbability K hcap)
      s F
      (K.normalizedSubMarkovShadow_providerAt_compatible hcap s F hindex)

/--
Primitive hitting bound for a source-controlled family weighted by the
normalized shadow of a positive-capacity kernel.
-/
theorem weightedHitMass_le_const_applyAtToSourceControlled
    {σ ι : Type _} [DecidableEq ι]
    (K : CapacityKernel σ ι) (hcap : ∀ s, 0 < K.capacity s)
    (s : σ) {M : MassSpace ℕ} {A : Finset ℕ}
    (F : SourceControlledChainFamily M ι)
    (hindex : K.children s = F.index)
    (hA : PrimitiveOn A) {C : ℝ} (hC : 0 ≤ C)
    (hsource : ∀ i ∈ F.index, (M.μ (F.source i) : ℝ) ≤ C) :
    (K.applyAtToSourceControlled hcap s F hindex).weightedHitMass A ≤ C :=
  (SubMarkovShadow.ofCapacityKernel K hcap)
    |>.weightedHitMass_le_const_applyAtToSourceControlled
      (SubMarkovShadow.ofCapacityKernel_subProbability K hcap)
      s F
      (K.normalizedSubMarkovShadow_providerAt_compatible hcap s F hindex)
      hA hC hsource

end CapacityKernel

end DkMath.Kernel
