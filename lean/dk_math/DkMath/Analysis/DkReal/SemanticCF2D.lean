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

/-- The interpreted core coordinate remains nonnegative. -/
theorem semanticUnitKernel_core_nonneg (r : UnitKernel DkNNRealQ) :
    0 ≤ (semanticUnitKernel r : Vec ℝ).core :=
  semanticValue_nonneg (r : Vec DkNNRealQ).core

/-- The interpreted beam coordinate remains nonnegative. -/
theorem semanticUnitKernel_beam_nonneg (r : UnitKernel DkNNRealQ) :
    0 ≤ (semanticUnitKernel r : Vec ℝ).beam :=
  semanticValue_nonneg (r : Vec DkNNRealQ).beam

/--
The coordinates of an interpreted nonnegative unit kernel satisfy the real
Pythagorean identity.
-/
theorem semanticUnitKernel_sq_add_sq (r : UnitKernel DkNNRealQ) :
    semanticValue (r : Vec DkNNRealQ).core ^ 2
      + semanticValue (r : Vec DkNNRealQ).beam ^ 2 = 1 := by
  simpa [Vec.q2, semanticVec] using
    (UnitKernel.coe_q2 (semanticUnitKernel r))

/--
Act on a real CF2D vector by first interpreting a nonnegative DkMath unit
kernel as a real unit kernel.

Subtraction enters only in this real-side action. It is not added to
`DkNNRealQ`.
-/
def semanticAct (r : UnitKernel DkNNRealQ) (z : Vec ℝ) : Vec ℝ :=
  UnitKernel.act (semanticUnitKernel r) z

/-- Core-coordinate formula for the transported real action. -/
@[simp]
theorem semanticAct_core (r : UnitKernel DkNNRealQ) (z : Vec ℝ) :
    (semanticAct r z).core =
      semanticValue (r : Vec DkNNRealQ).core * z.core
        - semanticValue (r : Vec DkNNRealQ).beam * z.beam := rfl

/-- Beam-coordinate formula for the transported real action. -/
@[simp]
theorem semanticAct_beam (r : UnitKernel DkNNRealQ) (z : Vec ℝ) :
    (semanticAct r z).beam =
      semanticValue (r : Vec DkNNRealQ).core * z.beam
        + semanticValue (r : Vec DkNNRealQ).beam * z.core := rfl

/--
The transported real action preserves the CF2D quadratic invariant.

This is the first direct consumer of an existing real-side CF2D action
theorem. No new analytic argument is needed after the unit-kernel transport.
-/
theorem semanticAct_q2 (r : UnitKernel DkNNRealQ) (z : Vec ℝ) :
    Vec.q2 (semanticAct r z) = Vec.q2 z :=
  UnitKernel.q2_act (semanticUnitKernel r) z

/-- The transported action is a square-mass-preserving real map. -/
theorem semanticAct_preservesQ2 (r : UnitKernel DkNNRealQ) :
    PreservesQ2 (semanticAct r) :=
  semanticAct_q2 r

/-
[TODO: semantic-cf2d/signed-kernel] Source-level `Vec.star` and
`KernelFamily` require a ring because their core coordinate uses subtraction.
Keep the source in the nonnegative semiring until a signed DkReal layer is
introduced; do not manufacture subtraction merely to mirror the real target.
-/

end

end DkMath.Analysis.DkNNRealQ
