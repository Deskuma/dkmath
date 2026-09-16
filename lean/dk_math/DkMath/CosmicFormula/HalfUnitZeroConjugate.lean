/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

#print "file: DkMath.CosmicFormula.HalfUnitZeroConjugate"

namespace DkMath.CosmicFormula.HalfUnitZeroConjugate

noncomputable section

/-- The half-unit at a real anchor q, which is the midpoint of 0 and q. -/
def halfUnit (q : ℝ) : ℝ :=
  q / 2

/-- The value of the zero-conjugate quadratic at its midpoint. -/
def halfUnitDepth (q : ℝ) : ℝ :=
  -(halfUnit q) ^ 2

/--
The real quadratic centered at the half-unit of q.

Its two zero-conjugate endpoints are 0 and q.  The definition is deliberately
prime-free: q is only a fine anchor and root separation.
-/
def zeroConjugateUniverse (q x : ℝ) : ℝ :=
  (x - halfUnit q) ^ 2 - (halfUnit q) ^ 2

/-- The zero-conjugate quadratic is the product of its two endpoint factors. -/
theorem zeroConjugateUniverse_eq_mul (q x : ℝ) :
    zeroConjugateUniverse q x = x * (x - q) := by
  unfold zeroConjugateUniverse halfUnit
  ring

/-- The left endpoint is a zero of the zero-conjugate quadratic. -/
@[simp] theorem zeroConjugateUniverse_zero (q : ℝ) :
    zeroConjugateUniverse q 0 = 0 := by
  rw [zeroConjugateUniverse_eq_mul]
  simp

/-- The anchor endpoint is a zero of the zero-conjugate quadratic. -/
@[simp] theorem zeroConjugateUniverse_anchor (q : ℝ) :
    zeroConjugateUniverse q q = 0 := by
  rw [zeroConjugateUniverse_eq_mul]
  simp

/-- The zero set consists exactly of the two endpoint roots, including q = 0. -/
theorem zeroConjugateUniverse_eq_zero_iff (q x : ℝ) :
    zeroConjugateUniverse q x = 0 ↔ x = 0 ∨ x = q := by
  rw [zeroConjugateUniverse_eq_mul]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hx | hx
    · exact Or.inl hx
    · exact Or.inr (sub_eq_zero.mp hx)
  · rintro (rfl | rfl)
    · simp
    · simp

/-- At the midpoint, the quadratic has exactly the declared depth value. -/
@[simp] theorem zeroConjugateUniverse_halfUnit (q : ℝ) :
    zeroConjugateUniverse q (halfUnit q) = halfUnitDepth q := by
  rw [zeroConjugateUniverse_eq_mul]
  unfold halfUnitDepth halfUnit
  ring

/-- Transparent scalar form of the midpoint depth. -/
theorem halfUnitDepth_eq (q : ℝ) :
    halfUnitDepth q = -(q / 2) ^ 2 := by
  rfl

/-- Reflection about q/2 preserves the zero-conjugate quadratic. -/
theorem zeroConjugateUniverse_reflection (q x : ℝ) :
    zeroConjugateUniverse q (q - x) = zeroConjugateUniverse q x := by
  rw [zeroConjugateUniverse_eq_mul, zeroConjugateUniverse_eq_mul]
  ring

end

end DkMath.CosmicFormula.HalfUnitZeroConjugate
