/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CosmicFormula.SquareGnomon

#print "file: DkMath.CosmicFormula.QuadraticCenteredBridge"

/-! Thin algebraic adapters to existing squareGnomon; no new delta or derivative. -/
namespace DkMath.CosmicFormula

/-- Expand the existing squareGnomon at degree two, over a commutative ring. -/
theorem quadratic_forward_factor {R : Type*} [CommRing R] (x h : R) :
    (x + h) ^ 2 - x ^ 2 = h * (2 * x + h) := by
  have he := SquareGnomon.core_add_squareGnomon_eq_next_square x h
  rw [SquareGnomon.squareGnomon_eq_mul_two_mul_add] at he
  rw [← he]
  ring

theorem quadratic_forward_backward {R : Type*} [CommRing R] (x h : R) :
    (x + h) ^ 2 - x ^ 2 = 2 * h * x + h ^ 2 ∧
    x ^ 2 - (x - h) ^ 2 = 2 * h * x - h ^ 2 := by
  constructor
  · rw [quadratic_forward_factor]; ring
  · have he := quadratic_forward_factor (x - h) h
    simpa only [sub_add_cancel] using he.trans (by ring)

theorem quadratic_forward_div {K : Type*} [Field K] (x h : K) (hh : h ≠ 0) :
    ((x + h) ^ 2 - x ^ 2) / h = 2 * x + h := by
  rw [quadratic_forward_factor]
  exact mul_div_cancel_left₀ _ hh

/-- Half-step coordinates are algebraic field coordinates, not divisibility coordinates. -/
theorem quadratic_centered_half {K : Type*} [Field K] [CharZero K] (x h : K) :
    (x + h / 2) ^ 2 - (x - h / 2) ^ 2 = 2 * h * x := by
  field_simp
  ring

end DkMath.CosmicFormula
