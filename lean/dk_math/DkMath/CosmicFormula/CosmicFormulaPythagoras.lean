/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib
import DkMath.CosmicFormula.CosmicFormulaBasic

#print "file: DkMath.CosmicFormula.CosmicFormulaPythagoras"

/-!
# Pythagorean Theorem as Cosmic Formula Difference Structure

This file formalizes the Pythagorean theorem through the lens of the Cosmic Formula,
interpreting it as a difference structure.

## Overview

The classical Pythagorean theorem `a² + b² = c²` can be reinterpreted through
difference structures:
- `c² - a² = b²` (斜辺平方から一辺平方を引くと他辺平方)
- `c² - b² = a²` (斜辺平方から他辺平方を引くと一辺平方)

When we set `c = a + u`, we obtain the cosmic formula representation:
- `b² = (a+u)² - a² = 2au + u²`

This connects to the unit cosmic formula `(x+u)² - x(x+2u) = u²`.

## Main Definitions

- `IsPythagoreanTriple a b c`: Predicate for Pythagorean triples
- `PythagoreanDifference`: The difference structure `c² - a²` or `c² - b²`

## Main Theorems

- `pythagoras_as_difference`: `a² + b² = c²` ↔ `c² - a² = b²`
- `pythagoras_cosmic_form`: When `c = a + u`, then `b² = 2au + u²`
- `pythagoras_cosmic_unit_connection`: Connection to unit cosmic formula

## References

- Research note: `69e72cfc_2026-0421-075513_ピタゴラスの差分解釈+126404-367.md`
- Branch: `refact/ABC-Erdos1196-260419-v5`
- Date: 2026-04-27

-/

namespace DkMath.CosmicFormula.Pythagoras

/-! ## Pythagorean Triple Definitions -/

/-- A predicate stating that `(a, b, c)` forms a Pythagorean triple. -/
def IsPythagoreanTriple (a b c : ℝ) : Prop :=
  a^2 + b^2 = c^2

/-- Alias for non-negative real Pythagorean triples. -/
def IsPythagoreanTriplePos (a b c : ℝ) : Prop :=
  0 < a ∧ 0 < b ∧ 0 < c ∧ IsPythagoreanTriple a b c

/-! ## Difference Structure Interpretations -/

/-- The difference `c² - a²` as a generating structure for `b²`. -/
def PythagoreanDifference₁ (a c : ℝ) : ℝ := c^2 - a^2

/-- The difference `c² - b²` as a generating structure for `a²`. -/
def PythagoreanDifference₂ (b c : ℝ) : ℝ := c^2 - b^2

/-! ## Cosmic Formula Parametrization -/

/-- When the hypotenuse `c` is expressed as `a + u`, the other side squared. -/
def PythagoreanCosmicForm (a u : ℝ) : ℝ := 2 * a * u + u^2

/-! ## Basic Theorems -/

/-- The classical Pythagorean theorem is equivalent to the difference form. -/
theorem pythagoras_as_difference (a b c : ℝ) :
    IsPythagoreanTriple a b c ↔ c^2 - a^2 = b^2 ∧ c^2 - b^2 = a^2 := by
  unfold IsPythagoreanTriple
  constructor
  · intro h
    constructor
    · linarith
    · linarith
  · intro ⟨h1, h2⟩
    linarith

/-- The difference structure `c² - a²` equals `b²` for Pythagorean triples. -/
theorem pythagorean_diff_eq_square (a b c : ℝ) (h : IsPythagoreanTriple a b c) :
    PythagoreanDifference₁ a c = b^2 := by
  unfold IsPythagoreanTriple PythagoreanDifference₁ at *
  linarith

/-- The difference structure `c² - b²` equals `a²` for Pythagorean triples. -/
theorem pythagorean_diff_eq_square' (a b c : ℝ) (h : IsPythagoreanTriple a b c) :
    PythagoreanDifference₂ b c = a^2 := by
  unfold IsPythagoreanTriple PythagoreanDifference₂ at *
  linarith

/-! ## Cosmic Formula Representation -/

/-- When `c = a + u`, the Pythagorean difference becomes the cosmic form. -/
theorem pythagoras_cosmic_form (a u : ℝ) :
    (a + u)^2 - a^2 = PythagoreanCosmicForm a u := by
  unfold PythagoreanCosmicForm
  ring

/-- The cosmic form can be factored as `u(2a + u)`. -/
theorem pythagoras_cosmic_form_factor (a u : ℝ) :
    PythagoreanCosmicForm a u = u * (2 * a + u) := by
  unfold PythagoreanCosmicForm
  ring

/-- Pythagorean theorem in cosmic form: if `c = a + u`, then `b² = 2au + u²`. -/
theorem pythagoras_in_cosmic_form (a b u : ℝ) (h : IsPythagoreanTriple a b (a + u)) :
    b^2 = PythagoreanCosmicForm a u := by
  have : (a + u)^2 - a^2 = b^2 := by
    unfold IsPythagoreanTriple at h
    linarith
  rw [pythagoras_cosmic_form] at this
  exact this.symm

/-! ## Connection to Unit Cosmic Formula -/

/-- The Pythagorean cosmic form `2au + u²` appears as the difference `(a+u)² - a²`,
    which is distinct from but related to the unit cosmic formula `(x+u)² - x(x+2u) = u²`.
    The Pythagorean form represents the "Beam" structure `2au + u²`,
    while the cosmic formula collapses to `u²`. -/
theorem pythagoras_cosmic_unit_relation (a u : ℝ) :
    PythagoreanCosmicForm a u = (a + u)^2 - a^2 ∧
    DkMath.CosmicFormula.Basic.cosmic_formula_unit a u = u^2 := by
  constructor
  · unfold PythagoreanCosmicForm
    ring
  · exact DkMath.CosmicFormula.Basic.cosmic_formula_unit_theorem a u

/-- In the Pythagorean setting, `b² = u²` when cosmic formula is satisfied differently.
    This shows the special case where the cosmic formula collapses to `u²`. -/
theorem pythagoras_special_cosmic_case (u : ℝ) :
    ∃ x, (x + u)^2 - x * (x + 2*u) = u^2 := by
  use 0  -- any x works, but 0 is simplest
  ring

/-! ## Alternative Representations -/

/-- The short side squared as a difference of two squares. -/
theorem short_side_as_diff_of_squares (a b c : ℝ) (h : IsPythagoreanTriple a b c) :
    b^2 = (c - a) * (c + a) := by
  have : c^2 - a^2 = b^2 := by
    unfold IsPythagoreanTriple at h
    linarith
  calc b^2 = c^2 - a^2 := this.symm
    _ = (c - a) * (c + a) := by ring

/-- The short side squared as a difference of two squares (symmetric). -/
theorem short_side_as_diff_of_squares' (a b c : ℝ) (h : IsPythagoreanTriple a b c) :
    a^2 = (c - b) * (c + b) := by
  have : c^2 - b^2 = a^2 := by
    unfold IsPythagoreanTriple at h
    linarith
  calc a^2 = c^2 - b^2 := this.symm
    _ = (c - b) * (c + b) := by ring

/-! ## Pythagorean Difference as "Gap" and "Beam" Interpretation -/

/-- When `c = a + u`, the difference `u` is the "gap" and `2a + u` is the "beam". -/
theorem pythagoras_gap_beam_interpretation (a u : ℝ) :
    ∃ (gap beam : ℝ), gap = u ∧ beam = 2 * a + u ∧ PythagoreanCosmicForm a u = gap * beam := by
  use u, 2 * a + u
  constructor
  · rfl
  constructor
  · rfl
  · exact pythagoras_cosmic_form_factor a u

/-! ## Integer Pythagorean Triples -/

/-- The integer version of Pythagorean triple predicate. -/
def IsPythagoreanTripleInt (a b c : ℤ) : Prop :=
  a^2 + b^2 = c^2

/-- Casting integer Pythagorean triples to real preserves the property. -/
theorem int_pythagoras_to_real (a b c : ℤ) :
    IsPythagoreanTripleInt a b c → IsPythagoreanTriple (a : ℝ) (b : ℝ) (c : ℝ) := by
  intro h
  unfold IsPythagoreanTripleInt at h
  unfold IsPythagoreanTriple
  norm_cast

/-! ## Classical Pythagorean Triple Examples -/

/-- The (3,4,5) triangle is a Pythagorean triple. -/
example : IsPythagoreanTripleInt 3 4 5 := by
  unfold IsPythagoreanTripleInt
  norm_num

/-- The (5,12,13) triangle is a Pythagorean triple. -/
example : IsPythagoreanTripleInt 5 12 13 := by
  unfold IsPythagoreanTripleInt
  norm_num

/-- The (8,15,17) triangle is a Pythagorean triple. -/
example : IsPythagoreanTripleInt 8 15 17 := by
  unfold IsPythagoreanTripleInt
  norm_num

/-! ## Parametrization via m and n -/

/-- The classical parametrization of Pythagorean triples. -/
def PythagoreanParametrization (m n : ℤ) : ℤ × ℤ × ℤ :=
  (m^2 - n^2, 2*m*n, m^2 + n^2)

/-- The parametrization produces valid Pythagorean triples. -/
theorem parametrization_is_pythagoras (m n : ℤ) :
    let (a, b, c) := PythagoreanParametrization m n
    IsPythagoreanTripleInt a b c := by
  unfold PythagoreanParametrization IsPythagoreanTripleInt
  simp
  ring

/-! ## Cosmic Formula Interpretation of Parametrization -/

/-- The side `a = m² - n²` is already a difference of squares (cosmic structure). -/
theorem parametrization_a_is_difference (m n : ℤ) :
    let (a, _, _) := PythagoreanParametrization m n
    a = m^2 - n^2 := by rfl

/-- This shows that the classical parametrization inherently uses difference structures. -/
theorem parametrization_embeds_cosmic_structure (m n : ℤ) :
    let (a, b, c) := PythagoreanParametrization m n
    c^2 - a^2 = b^2 := by
  unfold PythagoreanParametrization
  simp
  ring

end DkMath.CosmicFormula.Pythagoras
