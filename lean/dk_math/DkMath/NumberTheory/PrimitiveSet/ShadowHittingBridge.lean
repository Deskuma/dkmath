/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PrimitiveSet.MarkovShadow

#print "file: DkMath.NumberTheory.PrimitiveSet.ShadowHittingBridge"

namespace DkMath.NumberTheory.PrimitiveSet

open DkMath.CosmicFormula.Mass

namespace SubMarkovShadow

/--
Apply the real provider emitted by a sub-Markov shadow at state `s` to a
source-controlled chain family with the same index.
-/
def applyAtToSourceControlled
    {σ ι : Type _} [DecidableEq ι] {M : MassSpace ℕ}
    (S : SubMarkovShadow σ ι) (s : σ)
    (F : SourceControlledChainFamily M ι)
    (hcompat : (S.providerAt s).Compatible F) :
    RealWeightedPathFamily M ι :=
  (S.providerAt s).applyToSourceControlled F hcompat

@[simp] theorem applyAtToSourceControlled_index
    {σ ι : Type _} [DecidableEq ι] {M : MassSpace ℕ}
    (S : SubMarkovShadow σ ι) (s : σ)
    (F : SourceControlledChainFamily M ι)
    (hcompat : (S.providerAt s).Compatible F) :
    (S.applyAtToSourceControlled s F hcompat).index = F.index :=
  rfl

/--
Applying a sub-probability sub-Markov shadow at a state gives a sub-probability
real-weighted path family.
-/
theorem applyAtToSourceControlled_weightSubProbability
    {σ ι : Type _} [DecidableEq ι] {M : MassSpace ℕ}
    (S : SubMarkovShadow σ ι) (hS : S.SubProbability) (s : σ)
    (F : SourceControlledChainFamily M ι)
    (hcompat : (S.providerAt s).Compatible F) :
    (S.applyAtToSourceControlled s F hcompat).WeightSubProbability :=
  (S.providerAt s).applyToSourceControlled_weightSubProbability F hcompat
    (S.providerAt_subProbability hS s)

/--
Primitive real-weighted hitting bound for a statewise sub-Markov shadow applied
to a compatible source-controlled chain family.
-/
theorem weightedHitMass_le_const_applyAtToSourceControlled
    {σ ι : Type _} [DecidableEq ι]
    {M : MassSpace ℕ} {A : Finset ℕ}
    (S : SubMarkovShadow σ ι) (hS : S.SubProbability) (s : σ)
    (F : SourceControlledChainFamily M ι)
    (hcompat : (S.providerAt s).Compatible F)
    (hA : PrimitiveOn A) {C : ℝ} (hC : 0 ≤ C)
    (hsource : ∀ i ∈ F.index, (M.μ (F.source i) : ℝ) ≤ C) :
    (S.applyAtToSourceControlled s F hcompat).weightedHitMass A ≤ C :=
  (S.providerAt s).weightedHitMass_le_const_of_subprob_applyToSourceControlled
    F hcompat hA hC (S.providerAt_subProbability hS s) hsource

end SubMarkovShadow

namespace MarkovShadow

/--
Apply the real provider emitted by a Markov shadow at state `s` to a
source-controlled chain family with the same index.
-/
def applyAtToSourceControlled
    {σ ι : Type _} [DecidableEq ι] {M : MassSpace ℕ}
    (S : MarkovShadow σ ι) (s : σ)
    (F : SourceControlledChainFamily M ι)
    (hcompat : (S.providerAt s).Compatible F) :
    RealWeightedPathFamily M ι :=
  (S.providerAt s).applyToSourceControlled F hcompat

@[simp] theorem applyAtToSourceControlled_index
    {σ ι : Type _} [DecidableEq ι] {M : MassSpace ℕ}
    (S : MarkovShadow σ ι) (s : σ)
    (F : SourceControlledChainFamily M ι)
    (hcompat : (S.providerAt s).Compatible F) :
    (S.applyAtToSourceControlled s F hcompat).index = F.index :=
  rfl

/--
Applying a Markov shadow at a state gives a sub-probability real-weighted path
family after forgetting equality.
-/
theorem applyAtToSourceControlled_weightSubProbability
    {σ ι : Type _} [DecidableEq ι] {M : MassSpace ℕ}
    (S : MarkovShadow σ ι) (s : σ)
    (F : SourceControlledChainFamily M ι)
    (hcompat : (S.providerAt s).Compatible F) :
    (S.applyAtToSourceControlled s F hcompat).WeightSubProbability :=
  (S.providerAt s).applyToSourceControlled_weightSubProbability F hcompat
    (S.providerAt_subProbability s)

/--
Primitive real-weighted hitting bound for a statewise Markov shadow applied to
a compatible source-controlled chain family.
-/
theorem weightedHitMass_le_const_applyAtToSourceControlled
    {σ ι : Type _} [DecidableEq ι]
    {M : MassSpace ℕ} {A : Finset ℕ}
    (S : MarkovShadow σ ι) (s : σ)
    (F : SourceControlledChainFamily M ι)
    (hcompat : (S.providerAt s).Compatible F)
    (hA : PrimitiveOn A) {C : ℝ} (hC : 0 ≤ C)
    (hsource : ∀ i ∈ F.index, (M.μ (F.source i) : ℝ) ≤ C) :
    (S.applyAtToSourceControlled s F hcompat).weightedHitMass A ≤ C :=
  (S.providerAt s).weightedHitMass_le_const_of_subprob_applyToSourceControlled
    F hcompat hA hC (S.providerAt_subProbability s) hsource

end MarkovShadow

end DkMath.NumberTheory.PrimitiveSet
