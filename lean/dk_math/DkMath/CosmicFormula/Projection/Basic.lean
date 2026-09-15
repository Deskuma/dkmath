/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: DkMath contributors.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

#print "file: DkMath.CosmicFormula.Projection.Basic"

/-!
# Cosmic Projection basic API

This is the production owner for the rational real map previously present in
`DkMath.Samples.Projection`.  The API stops at its algebraic domain: the
denominator `P + 1` must be nonzero.  No interval, prime, or continuum claim
is introduced here.
-/

namespace DkMath.CosmicFormula.Projection

noncomputable section

/-- The compactifying cosmic projection `P ↦ -P / (P + 1)`. -/
def Pi (P : ℝ) : ℝ := -P / (P + 1)

/-- The complementary gap coordinate `P ↦ 1 / (P + 1)`. -/
def U (P : ℝ) : ℝ := 1 / (P + 1)

/-- Projection distance from the boundary `-1` equals the gap coordinate. -/
theorem cosmicProjection_gap_eq (P : ℝ) (hP : P + 1 ≠ 0) :
    Pi P + 1 = U P := by
  simp only [Pi, U]
  field_simp [hP]
  ring

/-- The projection is an involution on its non-pole domain. -/
theorem cosmicProjection_inverse (P : ℝ) (hP : P + 1 ≠ 0) :
    Pi (Pi P) = P := by
  have hgap : Pi P + 1 ≠ 0 := by
    rw [cosmicProjection_gap_eq P hP]
    exact one_div_ne_zero hP
  simp only [Pi]
  field_simp [hP, hgap]
  ring

/-- The projection is injective away from its pole at `P = -1`. -/
theorem cosmicProjection_injective
    {P Q : ℝ}
    (hP : P + 1 ≠ 0) (hQ : Q + 1 ≠ 0)
    (h : Pi P = Pi Q) :
    P = Q := by
  calc
    P = Pi (Pi P) := (cosmicProjection_inverse P hP).symm
    _ = Pi (Pi Q) := by rw [h]
    _ = Q := cosmicProjection_inverse Q hQ

end

end DkMath.CosmicFormula.Projection
