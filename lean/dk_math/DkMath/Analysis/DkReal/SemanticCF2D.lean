/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Analysis.DkReal.Semantic
import DkMath.CosmicFormula.Rotation.CF2D.Basic

#print "file: DkMath.Analysis.DkReal.SemanticCF2D"

/-!
# Semantic CF2D bridge for nonnegative DkMath reals

This module is the first CF2D consumer of the semantic real interpretation.
It maps both coordinates of a nonnegative DkMath vector to Mathlib `Real` and
shows that the quadratic invariant

`q2(core, beam) = core^2 + beam^2`

is preserved by that interpretation.

The bridge uses only the semiring laws already proved for `semanticValue`.
It does not require subtraction, decidable comparison, order reflection, or
any analytic theorem about trigonometric functions.

At the bridge boundary, squares are normalized to products. This avoids
identifying CF2D's abstract `Semiring` power instance with the representation
power operation used to construct DkMath interval powers.
-/

namespace DkMath.Analysis.DkNNRealQ

open DkMath.CosmicFormula.Rotation.CF2D

noncomputable section

/-- Interpret both coordinates of a CF2D vector as Mathlib real numbers. -/
def semanticVec (z : Vec DkNNRealQ) : Vec ℝ :=
  ⟨semanticValue z.core, semanticValue z.beam⟩

/-- Semantic interpretation of the core coordinate. -/
@[simp]
theorem semanticVec_core (z : Vec DkNNRealQ) :
    (semanticVec z).core = semanticValue z.core := rfl

/-- Semantic interpretation of the beam coordinate. -/
@[simp]
theorem semanticVec_beam (z : Vec DkNNRealQ) :
    (semanticVec z).beam = semanticValue z.beam := rfl

/--
Semantic evaluation preserves the CF2D quadratic invariant.

Thus the internal square mass and the ordinary real square mass describe the
same quantity after interpretation.
-/
theorem semanticValue_q2 (z : Vec DkNNRealQ) :
    semanticValue (Vec.q2 z) = Vec.q2 (semanticVec z) := by
  simp only [Vec.q2, semanticVec, semanticValue_add, pow_two,
    semanticValue_mul]

/-- Coordinate form of semantic preservation of the quadratic invariant. -/
theorem semanticValue_q2_eq (z : Vec DkNNRealQ) :
    semanticValue (Vec.q2 z) =
      semanticValue z.core ^ 2 + semanticValue z.beam ^ 2 := by
  simpa [Vec.q2, semanticVec] using semanticValue_q2 z

/--
A nonnegative DkMath unit kernel determines a real CF2D unit kernel by
coordinatewise semantic interpretation.
-/
def semanticUnitKernel (r : UnitKernel DkNNRealQ) : UnitKernel ℝ :=
  ⟨semanticVec (r : Vec DkNNRealQ), by
    rw [← semanticValue_q2]
    simp⟩

/-- The underlying vector of a semantic unit kernel is the semantic vector. -/
@[simp]
theorem semanticUnitKernel_val (r : UnitKernel DkNNRealQ) :
    (semanticUnitKernel r : Vec ℝ) = semanticVec (r : Vec DkNNRealQ) := rfl

end

end DkMath.Analysis.DkNNRealQ
