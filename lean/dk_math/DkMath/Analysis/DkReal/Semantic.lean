/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Analysis.DkReal.Equiv

#print "file: DkMath.Analysis.DkReal.Semantic"

/-!
# Semantic real value of a DkReal representation

This module begins the noncomputable bridge from nested rational intervals to
Mathlib's `Real`.

The represented value is the supremum of the lower endpoints after casting
them to `Real`. Nestedness makes this sequence monotone, while every upper
endpoint bounds it. Consequently the supremum lies in every approximation
interval.

This file deliberately stops before quotient descent and arithmetic
preservation. Those require representative independence of `semanticValue`.

[TODO: semantic/equiv] Prove
`DkReal.Equiv x y -> semanticValue x = semanticValue y`.

[TODO: semantic/quotient] Lift the value through `DkNNRealQ`, then prove
preservation of zero, one, addition, nonnegative multiplication, powers, and
order.
-/

namespace DkMath.Analysis.DkReal

noncomputable section

/-- Lower endpoint of a representation, interpreted in Mathlib's `Real`. -/
def lowerReal (x : DkMath.Analysis.DkReal) (n : ℕ) : ℝ :=
  (x.interval n).lo

/-- Upper endpoint of a representation, interpreted in Mathlib's `Real`. -/
def upperReal (x : DkMath.Analysis.DkReal) (n : ℕ) : ℝ :=
  (x.interval n).hi

/-- Cast lower endpoints form a monotone real sequence. -/
theorem lowerReal_monotone (x : DkMath.Analysis.DkReal) :
    Monotone (lowerReal x) := by
  intro n m hnm
  simp only [lowerReal]
  exact_mod_cast x.lo_mono hnm

/-- Every fixed upper endpoint bounds all cast lower endpoints. -/
theorem lowerReal_le_upperReal
    (x : DkMath.Analysis.DkReal) (n m : ℕ) :
    lowerReal x m ≤ upperReal x n := by
  simp only [lowerReal, upperReal]
  by_cases hmn : m ≤ n
  · exact_mod_cast
      (x.lo_mono hmn).trans (x.interval n).le_lo_hi
  · have hnm : n ≤ m := le_of_not_ge hmn
    exact_mod_cast
      (x.interval m).le_lo_hi.trans (x.hi_antitone hnm)

/-- The range of cast lower endpoints is bounded above. -/
theorem bddAbove_range_lowerReal (x : DkMath.Analysis.DkReal) :
    BddAbove (Set.range (lowerReal x)) := by
  refine ⟨upperReal x 0, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact lowerReal_le_upperReal x 0 n

/--
The semantic real represented by a nested interval sequence.

Completeness enters exactly here, through the conditionally complete order on
Mathlib's real numbers.
-/
def semanticValue (x : DkMath.Analysis.DkReal) : ℝ :=
  ⨆ n, lowerReal x n

/-- Every lower endpoint is below the represented semantic value. -/
theorem lowerReal_le_semanticValue
    (x : DkMath.Analysis.DkReal) (n : ℕ) :
    lowerReal x n ≤ semanticValue x := by
  exact le_ciSup (bddAbove_range_lowerReal x) n

/-- The represented semantic value is below every upper endpoint. -/
theorem semanticValue_le_upperReal
    (x : DkMath.Analysis.DkReal) (n : ℕ) :
    semanticValue x ≤ upperReal x n := by
  apply ciSup_le
  intro m
  exact lowerReal_le_upperReal x n m

/-- The semantic value belongs to every cast approximation interval. -/
theorem semanticValue_mem_interval
    (x : DkMath.Analysis.DkReal) (n : ℕ) :
    semanticValue x ∈ Set.Icc (lowerReal x n) (upperReal x n) :=
  ⟨lowerReal_le_semanticValue x n, semanticValue_le_upperReal x n⟩

/-- Cast lower endpoints converge monotonically to the semantic value. -/
theorem tendsto_lowerReal_semanticValue (x : DkMath.Analysis.DkReal) :
    Filter.Tendsto (lowerReal x) Filter.atTop (nhds (semanticValue x)) := by
  exact tendsto_atTop_ciSup (lowerReal_monotone x) (bddAbove_range_lowerReal x)

end

end DkMath.Analysis.DkReal
