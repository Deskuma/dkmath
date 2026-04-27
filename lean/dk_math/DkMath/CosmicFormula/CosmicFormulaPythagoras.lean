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

/-- A predicate stating that `(a, b, c)` forms a Pythagorean triple over a commutative ring. -/
def IsPythagoreanTripleOver {R : Type*} [CommRing R] (a b c : R) : Prop :=
  a^2 + b^2 = c^2

/-- A predicate stating that `(a, b, c)` forms a Pythagorean triple (real number version). -/
abbrev IsPythagoreanTriple (a b c : ℝ) : Prop :=
  IsPythagoreanTripleOver a b c

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
  unfold IsPythagoreanTriple IsPythagoreanTripleOver
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
  unfold IsPythagoreanTriple IsPythagoreanTripleOver PythagoreanDifference₁ at *
  linarith

/-- The difference structure `c² - b²` equals `a²` for Pythagorean triples. -/
theorem pythagorean_diff_eq_square' (a b c : ℝ) (h : IsPythagoreanTriple a b c) :
    PythagoreanDifference₂ b c = a^2 := by
  unfold IsPythagoreanTriple IsPythagoreanTripleOver PythagoreanDifference₂ at *
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
    unfold IsPythagoreanTriple IsPythagoreanTripleOver at h
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
    unfold IsPythagoreanTriple IsPythagoreanTripleOver at h
    linarith
  calc b^2 = c^2 - a^2 := this.symm
    _ = (c - a) * (c + a) := by ring

/-- The short side squared as a difference of two squares (symmetric). -/
theorem short_side_as_diff_of_squares' (a b c : ℝ) (h : IsPythagoreanTriple a b c) :
    a^2 = (c - b) * (c + b) := by
  have : c^2 - b^2 = a^2 := by
    unfold IsPythagoreanTriple IsPythagoreanTripleOver at h
    linarith
  calc a^2 = c^2 - b^2 := this.symm
    _ = (c - b) * (c + b) := by ring

/-! ## Pythagorean Difference as "Gap" and "Beam" Interpretation -/

/-- The boundary gap: the difference between hypotenuse and a side. -/
def boundaryGap {R : Type*} [Ring R] (a c : R) : R := c - a

/-- The Pythagorean beam: the sum of hypotenuse and a side. -/
def pythagoreanBeam {R : Type*} [Ring R] (a c : R) : R := c + a

/-- The difference of squares factors as Gap × Beam. -/
theorem sq_sub_sq_gap_beam {R : Type*} [CommRing R] (a c : R) :
    c ^ 2 - a ^ 2 = boundaryGap a c * pythagoreanBeam a c := by
  unfold boundaryGap pythagoreanBeam
  ring

/-- When c = a + u, the square difference equals u times the beam. -/
theorem sq_diff_of_gap {R : Type*} [CommRing R] (a u : R) :
    (a + u) ^ 2 - a ^ 2 = u * (2 * a + u) := by
  ring

/-- The Gap-Beam factorization is equivalent to the boundary gap theorem. -/
theorem gap_beam_factorization {R : Type*} [CommRing R] (a u : R) :
    (a + u) ^ 2 - a ^ 2 = boundaryGap a (a + u) * pythagoreanBeam a (a + u) := by
  rw [sq_sub_sq_gap_beam]

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
  unfold IsPythagoreanTripleInt IsPythagoreanTriple IsPythagoreanTripleOver at *
  exact_mod_cast h

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

/-! ## Cosmic Link Condition: 宇宙式リンク条件

The "cosmic link condition" represents Pythagorean triples in the form:
- `a = α * u₁`
- `b = β * u₂`
- `c = γ * u₃`

where `α, β, γ` are scaling factors and `u₁, u₂, u₃` are unit representatives
from different "cosmic unit systems".

The link condition states: `α² * u₁² + β² * u₂² = γ² * u₃²`
-/

/-- The cosmic link condition: a Pythagorean relation expressed through
    scaled unit representatives (general version over a commutative ring). -/
def CosmicLinkCondition {R : Type*} [CommRing R] (α β γ u₁ u₂ u₃ : R) : Prop :=
  α^2 * u₁^2 + β^2 * u₂^2 = γ^2 * u₃^2

/-- Real number version of the cosmic link condition. -/
abbrev CosmicLinkConditionReal (α β γ u₁ u₂ u₃ : ℝ) : Prop :=
  CosmicLinkCondition α β γ u₁ u₂ u₃

/-- Integer version of the cosmic link condition. -/
abbrev CosmicLinkConditionInt (α β γ u₁ u₂ u₃ : ℤ) : Prop :=
  CosmicLinkCondition α β γ u₁ u₂ u₃

/-- If the cosmic link condition holds, then `(αu₁, βu₂, γu₃)` forms a Pythagorean triple. -/
theorem cosmic_link_to_pythagoras {R : Type*} [CommRing R] (α β γ u₁ u₂ u₃ : R)
    (h : CosmicLinkCondition α β γ u₁ u₂ u₃) :
    IsPythagoreanTripleOver (α * u₁) (β * u₂) (γ * u₃) := by
  unfold CosmicLinkCondition IsPythagoreanTripleOver at *
  calc (α * u₁) ^ 2 + (β * u₂) ^ 2
      = α ^ 2 * u₁ ^ 2 + β ^ 2 * u₂ ^ 2 := by ring
    _ = γ ^ 2 * u₃ ^ 2 := h
    _ = (γ * u₃) ^ 2 := by ring

/-- Conversely, any Pythagorean triple can be expressed via the cosmic link condition. -/
theorem pythagoras_to_cosmic_link {R : Type*} [CommRing R] (a b c : R)
    (h : IsPythagoreanTripleOver a b c) :
    CosmicLinkCondition a b c 1 1 1 := by
  unfold CosmicLinkCondition IsPythagoreanTripleOver at *
  simp only [one_pow, mul_one]
  exact h

/-- The simplest cosmic link: all units are 1. -/
theorem cosmic_link_unit_one {R : Type*} [CommRing R] (α β γ : R) :
    CosmicLinkCondition α β γ 1 1 1 ↔ α^2 + β^2 = γ^2 := by
  unfold CosmicLinkCondition
  simp

/-- The parametrization satisfies the cosmic link condition. -/
theorem parametrization_cosmic_link (m n : ℤ) :
    let (a, b, c) := PythagoreanParametrization m n
    CosmicLinkCondition a b c 1 1 1 := by
  unfold PythagoreanParametrization CosmicLinkCondition
  simp
  ring

/-! ## Cosmic Pythagorean Triple Structure

A bundled structure representing a Pythagorean triple in the cosmic formula framework.
-/

/-- A Pythagorean triple expressed in cosmic formula form with scaling factors
    and unit representatives. -/
structure CosmicPythagoreanTriple (R : Type*) [Ring R] where
  /-- Scaling factor for side a -/
  α : R
  /-- Scaling factor for side b -/
  β : R
  /-- Scaling factor for hypotenuse c -/
  γ : R
  /-- Unit representative for side a -/
  u₁ : R
  /-- Unit representative for side b -/
  u₂ : R
  /-- Unit representative for hypotenuse c -/
  u₃ : R

namespace CosmicPythagoreanTriple

variable {R : Type*} [CommRing R]

/-- Side a of the triangle -/
def a (T : CosmicPythagoreanTriple R) : R := T.α * T.u₁

/-- Side b of the triangle -/
def b (T : CosmicPythagoreanTriple R) : R := T.β * T.u₂

/-- Hypotenuse c of the triangle -/
def c (T : CosmicPythagoreanTriple R) : R := T.γ * T.u₃

/-- The cosmic link condition for a bundled triple. -/
def IsLinked (T : CosmicPythagoreanTriple R) : Prop :=
  T.α^2 * T.u₁^2 + T.β^2 * T.u₂^2 = T.γ^2 * T.u₃^2

/-! ### Gap and Beam for Cosmic Triples

The Gap (c - a) and Beam (c + a) provide the factorization of b².
-/

/-- The gap between the hypotenuse and side a. -/
def gapA (T : CosmicPythagoreanTriple R) : R := T.c - T.a

/-- The beam: the sum of hypotenuse and side a. -/
def beamA (T : CosmicPythagoreanTriple R) : R := T.c + T.a

/-- If a triple is linked, it satisfies the Pythagorean relation. -/
theorem linked_satisfies_pythagoras (T : CosmicPythagoreanTriple R) (h : T.IsLinked) :
    IsPythagoreanTripleOver T.a T.b T.c := by
  unfold IsPythagoreanTripleOver IsLinked a b c at *
  calc (T.α * T.u₁) ^ 2 + (T.β * T.u₂) ^ 2
      = T.α ^ 2 * T.u₁ ^ 2 + T.β ^ 2 * T.u₂ ^ 2 := by ring
    _ = T.γ ^ 2 * T.u₃ ^ 2 := h
    _ = (T.γ * T.u₃) ^ 2 := by ring

/-- For a linked triple, b² equals Gap × Beam. -/
theorem b_sq_eq_gapA_mul_beamA (T : CosmicPythagoreanTriple R) (h : T.IsLinked) :
    T.b ^ 2 = gapA T * beamA T := by
  have pyth := linked_satisfies_pythagoras T h
  unfold IsPythagoreanTripleOver at pyth
  unfold gapA beamA
  calc T.b ^ 2
      = T.c ^ 2 - T.a ^ 2 := by
          have h := pyth
          exact (sub_eq_of_eq_add' h.symm).symm
    _ = (T.c - T.a) * (T.c + T.a) := by ring

/-- The standard representation with unit representatives all equal to 1. -/
def standard (α β γ : R) : CosmicPythagoreanTriple R :=
  { α := α, β := β, γ := γ, u₁ := 1, u₂ := 1, u₃ := 1 }

/-- The standard representation is linked iff the scaling factors satisfy Pythagoras. -/
theorem standard_linked_iff (α β γ : R) :
    (standard α β γ).IsLinked ↔ α^2 + β^2 = γ^2 := by
  unfold standard IsLinked
  simp only [one_pow, mul_one]

/-! ## Representation Freedom (Gauge Symmetry)

The cosmic link representation has gauge freedom: the same observed edge
can be expressed with different (α, u) pairs. This section formalizes
this representational freedom.
-/

/-- Rescaling preserves the observed edge in a field. -/
theorem observed_edge_rescale {K : Type*} [Field K]
    (α u k : K) (hk : k ≠ 0) :
    (α * k) * (u / k) = α * u := by
  field_simp [hk]

/-- Rescaling preserves the cosmic link condition in a field. -/
theorem cosmic_link_rescale {K : Type*} [Field K]
    (α β γ u₁ u₂ u₃ k : K) (hk : k ≠ 0)
    (h : @CosmicLinkCondition K _ α β γ u₁ u₂ u₃) :
    @CosmicLinkCondition K _ (α * k) (β * k) (γ * k) (u₁ / k) (u₂ / k) (u₃ / k) := by
  unfold CosmicLinkCondition at *
  -- After clearing denominators, the goal reduces exactly to the original link condition.
  field_simp [hk]
  exact h

/-- Rescaling each edge separately preserves the cosmic link condition.
    This represents the full gauge freedom of the three-unit-universe system. -/
theorem cosmic_link_rescale_each {K : Type*} [Field K]
    (α β γ u₁ u₂ u₃ k₁ k₂ k₃ : K)
    (hk₁ : k₁ ≠ 0) (hk₂ : k₂ ≠ 0) (hk₃ : k₃ ≠ 0)
    (h : @CosmicLinkCondition K _ α β γ u₁ u₂ u₃) :
    @CosmicLinkCondition K _
      (α * k₁) (β * k₂) (γ * k₃)
      (u₁ / k₁) (u₂ / k₂) (u₃ / k₃) := by
  unfold CosmicLinkCondition at *
  field_simp [hk₁, hk₂, hk₃]
  exact h

/-- Two representations are equivalent if they produce the same edges. -/
def EquivRepresentation {R : Type*} [CommRing R]
    (T₁ T₂ : CosmicPythagoreanTriple R) : Prop :=
  T₁.a = T₂.a ∧ T₁.b = T₂.b ∧ T₁.c = T₂.c

/-! ### Equivalence Relation Properties

`EquivRepresentation` forms an equivalence relation on cosmic Pythagorean triples.
-/

/-- Reflexivity: a representation is equivalent to itself. -/
theorem equivRepresentation_refl {R : Type*} [CommRing R]
    (T : CosmicPythagoreanTriple R) :
    EquivRepresentation T T := by
  unfold EquivRepresentation
  exact ⟨rfl, rfl, rfl⟩

/-- Symmetry: if T₁ is equivalent to T₂, then T₂ is equivalent to T₁. -/
theorem equivRepresentation_symm {R : Type*} [CommRing R]
    {T₁ T₂ : CosmicPythagoreanTriple R}
    (h : EquivRepresentation T₁ T₂) :
    EquivRepresentation T₂ T₁ := by
  rcases h with ⟨ha, hb, hc⟩
  exact ⟨ha.symm, hb.symm, hc.symm⟩

/-- Transitivity: if T₁ ~ T₂ and T₂ ~ T₃, then T₁ ~ T₃. -/
theorem equivRepresentation_trans {R : Type*} [CommRing R]
    {T₁ T₂ T₃ : CosmicPythagoreanTriple R}
    (h12 : EquivRepresentation T₁ T₂)
    (h23 : EquivRepresentation T₂ T₃) :
    EquivRepresentation T₁ T₃ := by
  rcases h12 with ⟨ha12, hb12, hc12⟩
  rcases h23 with ⟨ha23, hb23, hc23⟩
  exact ⟨ha12.trans ha23, hb12.trans hb23, hc12.trans hc23⟩

/-! ### Rescaling Operations

Operations for rescaling the representation while preserving the observed edges.
-/

/-- Rescale each edge separately with different scale factors.
    This represents the full gauge freedom: (K×)³ action. -/
def rescaleEach {K : Type*} [Field K]
    (T : CosmicPythagoreanTriple K)
    (k₁ k₂ k₃ : K) : CosmicPythagoreanTriple K :=
  { α := T.α * k₁
    β := T.β * k₂
    γ := T.γ * k₃
    u₁ := T.u₁ / k₁
    u₂ := T.u₂ / k₂
    u₃ := T.u₃ / k₃ }

/-- Rescaling each edge produces an equivalent representation. -/
theorem rescaleEach_equiv {K : Type*} [Field K]
    (T : CosmicPythagoreanTriple K)
    (k₁ k₂ k₃ : K)
    (hk₁ : k₁ ≠ 0) (hk₂ : k₂ ≠ 0) (hk₃ : k₃ ≠ 0) :
    EquivRepresentation T (rescaleEach T k₁ k₂ k₃) := by
  unfold EquivRepresentation rescaleEach a b c
  simp only
  constructor
  · field_simp [hk₁]
  constructor
  · field_simp [hk₂]
  · field_simp [hk₃]

/-- Rescaling preserves the linked property. -/
theorem rescaleEach_isLinked {K : Type*} [Field K]
    (T : CosmicPythagoreanTriple K)
    (k₁ k₂ k₃ : K)
    (hk₁ : k₁ ≠ 0) (hk₂ : k₂ ≠ 0) (hk₃ : k₃ ≠ 0)
    (h : T.IsLinked) :
    (rescaleEach T k₁ k₂ k₃).IsLinked := by
  unfold rescaleEach IsLinked
  exact cosmic_link_rescale_each T.α T.β T.γ T.u₁ T.u₂ T.u₃ k₁ k₂ k₃ hk₁ hk₂ hk₃ h

end CosmicPythagoreanTriple

end DkMath.CosmicFormula.Pythagoras
