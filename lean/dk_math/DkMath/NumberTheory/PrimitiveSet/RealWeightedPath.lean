/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PrimitiveSet.RealWeight

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

end DkMath.NumberTheory.PrimitiveSet
