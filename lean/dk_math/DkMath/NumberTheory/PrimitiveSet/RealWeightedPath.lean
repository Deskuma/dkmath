/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PrimitiveSet.RealWeight
import DkMath.NumberTheory.PrimitiveSet.WeightedPathFamily

#print "file: DkMath.NumberTheory.PrimitiveSet.RealWeightedPath"

namespace DkMath.NumberTheory.PrimitiveSet

/--
A finite provider of nonnegative real weights.

This is the R-version parallel prototype of `WeightProvider`.  It intentionally
does not generalize the existing rational provider; the real-valued route is
kept separate while its theorem shape is still being stabilized.
-/
structure RealWeightProvider (ι : Type _) where
  index : Finset ι
  weight : ι → ℝ
  weight_nonneg : ∀ i, i ∈ index → 0 ≤ weight i

namespace RealWeightProvider

/-- Total finite real weight carried by a provider. -/
def totalWeight
    {ι : Type _} (P : RealWeightProvider ι) : ℝ :=
  P.index.sum fun i => P.weight i

/-- The real provider is normalized as a finite sub-probability. -/
def SubProbability
    {ι : Type _} (P : RealWeightProvider ι) : Prop :=
  P.totalWeight ≤ 1

/-- Total real provider weight is nonnegative. -/
theorem totalWeight_nonneg
    {ι : Type _} (P : RealWeightProvider ι) :
    0 ≤ P.totalWeight := by
  unfold totalWeight
  exact Finset.sum_nonneg fun i hi => P.weight_nonneg i hi

/-- A direct budget bound proves real provider sub-probability. -/
theorem subProbability_of_budget
    {ι : Type _} (P : RealWeightProvider ι)
    (h : P.totalWeight ≤ 1) :
    P.SubProbability :=
  h

end RealWeightProvider

/--
A source-controlled finite forest with a nonnegative real weight on each
indexed chain/path.

This is the real-valued counterpart of `WeightedPathFamily`, used by the
normalized log-capacity and Markov-shadow route.
-/
structure RealWeightedPathFamily
    (M : DkMath.CosmicFormula.Mass.MassSpace ℕ) (ι : Type _) [DecidableEq ι]
    extends SourceControlledChainFamily M ι where
  weight : ι → ℝ
  weight_nonneg : ∀ i ∈ index, 0 ≤ weight i

namespace RealWeightedPathFamily

open DkMath.CosmicFormula.Mass
open DkMath.NumberTheory.ValuationFlow

/-- Add nonnegative real weights to an existing source-controlled chain family. -/
def ofSourceControlled
    {ι : Type _} [DecidableEq ι] {M : MassSpace ℕ}
    (F : SourceControlledChainFamily M ι)
    (weight : ι → ℝ)
    (hweight : ∀ i ∈ F.index, 0 ≤ weight i) :
    RealWeightedPathFamily M ι where
  index := F.index
  chain := F.chain
  chain_is_chain := F.chain_is_chain
  source := F.source
  mass_le_source := F.mass_le_source
  weight := weight
  weight_nonneg := hweight

/-- Real-weighted indexed hit mass over a finite weighted path family. -/
def weightedHitMass
    {ι : Type _} [DecidableEq ι] {M : MassSpace ℕ}
    (W : RealWeightedPathFamily M ι) (S : Finset ℕ) : ℝ :=
  W.index.sum fun i => W.weight i * (hitSetMass M (S ∩ W.chain i) : ℝ)

/-- Real-weighted indexed source mass over a finite weighted path family. -/
def weightedSourceMass
    {ι : Type _} [DecidableEq ι] {M : MassSpace ℕ}
    (W : RealWeightedPathFamily M ι) : ℝ :=
  W.index.sum fun i => W.weight i * (M.μ (W.source i) : ℝ)

/-- Total finite real weight carried by a real-weighted path family. -/
def totalWeight
    {ι : Type _} [DecidableEq ι] {M : MassSpace ℕ}
    (W : RealWeightedPathFamily M ι) : ℝ :=
  W.index.sum fun i => W.weight i

/-- The real weights form a finite sub-probability on the index set. -/
def WeightSubProbability
    {ι : Type _} [DecidableEq ι] {M : MassSpace ℕ}
    (W : RealWeightedPathFamily M ι) : Prop :=
  W.totalWeight ≤ 1

/-- Total real weight is nonnegative. -/
theorem totalWeight_nonneg
    {ι : Type _} [DecidableEq ι] {M : MassSpace ℕ}
    (W : RealWeightedPathFamily M ι) :
    0 ≤ W.totalWeight := by
  classical
  unfold totalWeight
  exact Finset.sum_nonneg fun i hi => W.weight_nonneg i hi

/--
If every source has mass at most `C`, then the real-weighted source mass is
bounded by `C * totalWeight`.
-/
theorem weightedSourceMass_le_const_mul_totalWeight
    {ι : Type _} [DecidableEq ι] {M : MassSpace ℕ}
    (W : RealWeightedPathFamily M ι) {C : ℝ}
    (hsource : ∀ i ∈ W.index, (M.μ (W.source i) : ℝ) ≤ C) :
    W.weightedSourceMass ≤ C * W.totalWeight := by
  classical
  unfold weightedSourceMass totalWeight
  calc
    W.index.sum (fun i => W.weight i * (M.μ (W.source i) : ℝ))
        ≤ W.index.sum (fun i => W.weight i * C) := by
          exact Finset.sum_le_sum fun i hi =>
            mul_le_mul_of_nonneg_left (hsource i hi) (W.weight_nonneg i hi)
    _ = C * W.index.sum (fun i => W.weight i) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _hi => by ring

/--
If the real weights are a sub-probability and every source has mass at most
`C`, then the real-weighted source mass is at most `C`.
-/
theorem weightedSourceMass_le_const_of_subprob
    {ι : Type _} [DecidableEq ι] {M : MassSpace ℕ}
    (W : RealWeightedPathFamily M ι) {C : ℝ}
    (hC : 0 ≤ C)
    (hprob : W.WeightSubProbability)
    (hsource : ∀ i ∈ W.index, (M.μ (W.source i) : ℝ) ≤ C) :
    W.weightedSourceMass ≤ C := by
  calc
    W.weightedSourceMass ≤ C * W.totalWeight :=
      W.weightedSourceMass_le_const_mul_totalWeight hsource
    _ ≤ C * 1 := by
      exact mul_le_mul_of_nonneg_left hprob hC
    _ = C := by ring

/--
Real-weighted primitive hitting bound.
-/
theorem primitive_weightedHitMass_le_weightedSourceMass
    {ι : Type _} [DecidableEq ι]
    {M : MassSpace ℕ} {S : Finset ℕ}
    (hS : PrimitiveOn S)
    (W : RealWeightedPathFamily M ι) :
    W.weightedHitMass S ≤ W.weightedSourceMass := by
  classical
  unfold weightedHitMass weightedSourceMass
  exact Finset.sum_le_sum fun i hi => by
    have hchain_rat :
        hitSetMass M (S ∩ W.chain i) ≤ M.μ (W.source i) := by
      calc
        hitSetMass M (S ∩ W.chain i)
            ≤ sourceSetMass M ({W.source i} : Finset ℕ) := by
              exact primitive_chain_hitSetMass_le_single_source
                M hS (W.chain_is_chain i hi)
                (by
                  intro h hh
                  exact W.mass_le_source i hi h (Finset.mem_inter.mp hh).2)
        _ = M.μ (W.source i) := by
              simp [sourceSetMass]
    have hchain :
        (hitSetMass M (S ∩ W.chain i) : ℝ) ≤
          (M.μ (W.source i) : ℝ) := by
      exact_mod_cast hchain_rat
    exact mul_le_mul_of_nonneg_left hchain (W.weight_nonneg i hi)

/--
If every source has mass at most `C`, primitive real-weighted hit mass is bounded
by `C * totalWeight`.
-/
theorem weightedHitMass_le_const_mul_totalWeight
    {ι : Type _} [DecidableEq ι]
    {M : MassSpace ℕ} {S : Finset ℕ}
    (hS : PrimitiveOn S)
    (W : RealWeightedPathFamily M ι) {C : ℝ}
    (hsource : ∀ i ∈ W.index, (M.μ (W.source i) : ℝ) ≤ C) :
    W.weightedHitMass S ≤ C * W.totalWeight := by
  calc
    W.weightedHitMass S ≤ W.weightedSourceMass :=
      W.primitive_weightedHitMass_le_weightedSourceMass hS
    _ ≤ C * W.totalWeight :=
      W.weightedSourceMass_le_const_mul_totalWeight hsource

/--
If the real weights are a sub-probability and every source has mass at most `C`,
primitive real-weighted hit mass is bounded by `C`.
-/
theorem weightedHitMass_le_const_of_subprob
    {ι : Type _} [DecidableEq ι]
    {M : MassSpace ℕ} {S : Finset ℕ}
    (hS : PrimitiveOn S)
    (W : RealWeightedPathFamily M ι) {C : ℝ}
    (hC : 0 ≤ C)
    (hprob : W.WeightSubProbability)
    (hsource : ∀ i ∈ W.index, (M.μ (W.source i) : ℝ) ≤ C) :
    W.weightedHitMass S ≤ C := by
  calc
    W.weightedHitMass S ≤ W.weightedSourceMass :=
      W.primitive_weightedHitMass_le_weightedSourceMass hS
    _ ≤ C :=
      W.weightedSourceMass_le_const_of_subprob hC hprob hsource

end RealWeightedPathFamily

namespace RealWeightProvider

open DkMath.CosmicFormula.Mass

/-- A real provider is compatible with a source-controlled family when indexes agree. -/
def Compatible
    {ι : Type _} [DecidableEq ι] {M : MassSpace ℕ}
    (P : RealWeightProvider ι) (F : SourceControlledChainFamily M ι) : Prop :=
  P.index = F.index

/-- Apply a real provider to a source-controlled family. -/
def applyToSourceControlled
    {ι : Type _} [DecidableEq ι] {M : MassSpace ℕ}
    (P : RealWeightProvider ι) (F : SourceControlledChainFamily M ι)
    (hcompat : P.Compatible F) :
    RealWeightedPathFamily M ι :=
  RealWeightedPathFamily.ofSourceControlled F P.weight
    (by
      intro i hi
      exact P.weight_nonneg i (by
        rw [hcompat]
        exact hi))

@[simp] theorem applyToSourceControlled_index
    {ι : Type _} [DecidableEq ι] {M : MassSpace ℕ}
    (P : RealWeightProvider ι) (F : SourceControlledChainFamily M ι)
    (hcompat : P.Compatible F) :
    (P.applyToSourceControlled F hcompat).index = F.index :=
  rfl

@[simp] theorem applyToSourceControlled_weight
    {ι : Type _} [DecidableEq ι] {M : MassSpace ℕ}
    (P : RealWeightProvider ι) (F : SourceControlledChainFamily M ι)
    (hcompat : P.Compatible F) :
    (P.applyToSourceControlled F hcompat).weight = P.weight :=
  rfl

/-- Applying a sub-probability real provider gives a sub-probability path family. -/
theorem applyToSourceControlled_weightSubProbability
    {ι : Type _} [DecidableEq ι] {M : MassSpace ℕ}
    (P : RealWeightProvider ι) (F : SourceControlledChainFamily M ι)
    (hcompat : P.Compatible F) (hprob : P.SubProbability) :
    (P.applyToSourceControlled F hcompat).WeightSubProbability := by
  unfold RealWeightedPathFamily.WeightSubProbability RealWeightedPathFamily.totalWeight
  dsimp [applyToSourceControlled, RealWeightedPathFamily.ofSourceControlled]
  simpa [SubProbability, totalWeight, Compatible] using hcompat ▸ hprob

/-- Primitive hitting bound after applying a real sub-probability provider. -/
theorem weightedHitMass_le_const_of_subprob_applyToSourceControlled
    {ι : Type _} [DecidableEq ι]
    {M : MassSpace ℕ} {S : Finset ℕ}
    (P : RealWeightProvider ι) (F : SourceControlledChainFamily M ι)
    (hcompat : P.Compatible F)
    (hS : PrimitiveOn S) {C : ℝ} (hC : 0 ≤ C)
    (hprob : P.SubProbability)
    (hsource :
      ∀ i ∈ F.index, (M.μ (F.source i) : ℝ) ≤ C) :
    (P.applyToSourceControlled F hcompat).weightedHitMass S ≤ C := by
  exact (P.applyToSourceControlled F hcompat).weightedHitMass_le_const_of_subprob
    hS hC
    (P.applyToSourceControlled_weightSubProbability F hcompat hprob)
    hsource

end RealWeightProvider

end DkMath.NumberTheory.PrimitiveSet
