/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib
import DkMath.CosmicFormula.CosmicFormulaPythagoras

#print "file: DkMath.CosmicFormula.CosmicFormulaPythagorasExamples"

/-!
# Examples of Pythagorean Triples in Cosmic Formula Framework

This file provides concrete examples of Pythagorean triples expressed through
the cosmic link condition and the `CosmicPythagoreanTriple` structure.

## Classical Examples

We demonstrate that well-known Pythagorean triples like (3,4,5), (5,12,13),
and (8,15,17) can be expressed as cosmic links with various unit representatives.

## Minimal Cosmic Link

The simplest case is when all unit representatives are 1:
- `u₁ = u₂ = u₃ = 1`
- `α = 3, β = 4, γ = 5`

This gives the (3,4,5) triangle.

-/

namespace DkMath.CosmicFormula.Pythagoras.Examples

open CosmicPythagoreanTriple

/-! ## (3,4,5) Triangle - The Minimal Example -/

/-- The (3,4,5) triangle satisfies the cosmic link condition with unit representatives. -/
example : CosmicLinkConditionInt 3 4 5 1 1 1 := by
  unfold CosmicLinkConditionInt
  norm_num

/-- The (3,4,5) triangle as a standard cosmic triple. -/
def triple_3_4_5 : CosmicPythagoreanTriple ℤ :=
  standard 3 4 5

/-- The (3,4,5) triple is linked. -/
example : triple_3_4_5.IsLinked := by
  unfold triple_3_4_5
  rw [standard_linked_iff]
  norm_num

/-- Verification that (3,4,5) gives the correct side values. -/
example : triple_3_4_5.a = 3 ∧ triple_3_4_5.b = 4 ∧ triple_3_4_5.c = 5 := by
  decide

/-! ## (5,12,13) Triangle -/

/-- The (5,12,13) triangle satisfies the cosmic link condition. -/
example : CosmicLinkConditionInt 5 12 13 1 1 1 := by
  unfold CosmicLinkConditionInt
  norm_num

/-- The (5,12,13) triangle as a standard cosmic triple. -/
def triple_5_12_13 : CosmicPythagoreanTriple ℤ :=
  standard 5 12 13

/-- The (5,12,13) triple is linked. -/
example : triple_5_12_13.IsLinked := by
  unfold triple_5_12_13
  rw [standard_linked_iff]
  norm_num

/-! ## (8,15,17) Triangle -/

/-- The (8,15,17) triangle satisfies the cosmic link condition. -/
example : CosmicLinkConditionInt 8 15 17 1 1 1 := by
  unfold CosmicLinkConditionInt
  norm_num

/-- The (8,15,17) triangle as a standard cosmic triple. -/
def triple_8_15_17 : CosmicPythagoreanTriple ℤ :=
  standard 8 15 17

/-- The (8,15,17) triple is linked. -/
example : triple_8_15_17.IsLinked := by
  unfold triple_8_15_17
  rw [standard_linked_iff]
  norm_num

/-! ## Scaled Cosmic Links

The cosmic framework allows representing the same geometric triangle
with different unit representatives. For example, (6,8,10) is a scaled
version of (3,4,5).
-/

/-- The (6,8,10) triangle as a scaled version with common factor 2. -/
def triple_6_8_10_scaled : CosmicPythagoreanTriple ℤ :=
  { α := 3, β := 4, γ := 5, u₁ := 2, u₂ := 2, u₃ := 2 }

/-- The scaled triple (6,8,10) is linked. -/
example : triple_6_8_10_scaled.IsLinked := by
  unfold triple_6_8_10_scaled IsLinked
  norm_num

/-- Verification of side values for the scaled triple. -/
example : triple_6_8_10_scaled.a = 6 ∧
          triple_6_8_10_scaled.b = 8 ∧
          triple_6_8_10_scaled.c = 10 := by
  decide

/-! ## Alternative Unit Representations

We can also represent the same triangle with different choices of unit
representatives, demonstrating the flexibility of the cosmic framework.
-/

/-- The (3,4,5) triangle with non-uniform unit representatives. -/
def triple_3_4_5_alt : CosmicPythagoreanTriple ℤ :=
  { α := 1, β := 2, γ := 1, u₁ := 3, u₂ := 2, u₃ := 5 }

/-- The alternative representation is linked. -/
example : triple_3_4_5_alt.IsLinked := by
  unfold triple_3_4_5_alt IsLinked
  norm_num

/-- Verification that the alternative gives the same triangle. -/
example : triple_3_4_5_alt.a = 3 ∧
          triple_3_4_5_alt.b = 4 ∧
          triple_3_4_5_alt.c = 5 := by
  decide

/-! ## Parametrization Examples

Using the classical parametrization (m²-n², 2mn, m²+n²).
-/

section ParametrizationExamples

/-- For m=2, n=1, we get the (3,4,5) triple. -/
example : let (a, b, c) := PythagoreanParametrization 2 1
          CosmicLinkConditionInt a b c 1 1 1 := by
  unfold PythagoreanParametrization CosmicLinkConditionInt
  norm_num

/-- For m=3, n=2, we get the (5,12,13) triple. -/
example : let (a, b, c) := PythagoreanParametrization 3 2
          CosmicLinkConditionInt a b c 1 1 1 := by
  unfold PythagoreanParametrization CosmicLinkConditionInt
  norm_num

/-- For m=4, n=1, we get the (15,8,17) triple (note: a and b swapped). -/
example : let (a, b, c) := PythagoreanParametrization 4 1
          a = 15 ∧ b = 8 ∧ c = 17 := by
  decide

set_option linter.style.longLine false
-- 2026/04/27 15:47
-- ※ここで VSCode 上のエディタでは Error が出る。
-- が、Lean 4 のコンパイルは通る。ビルドの方が正しい。と、みなす。
-- Lean 4 Web での確認も行い、Error は出ないことを確認済み。

/- VSCode Error Message
Unknown constant `DkMath.CosmicFormula.Pythagoras.Examples._example.match_1`Lean 4(lean.unknownIdentifier)
A docComment parses a "documentation comment" like /-- foo -/. This is not treated like a regular comment (that is, as whitespace); it is parsed and forms part of the syntax tree structure.

At parse time, docComment checks the value of the doc.verso option. If it is true, the contents are parsed as Verso markup. If not, the contents are treated as plain text or Markdown. Use plainDocComment to always treat the contents as plain text.

A plain text doc comment node contains a /-- atom and then the remainder of the comment, foo -/ in this example. Use TSyntax.getDocString to extract the body text from a doc string syntax node. A Verso comment node contains the /-- atom, the document's syntax tree, and a closing -/ atom.
-/

/- Build Log
ℹ [8375/8470] Replayed DkMath.CosmicFormula.Basic
info: DkMath/CosmicFormula/Basic.lean:29:0: file: DkMath.CosmicFormula.Basic
ℹ [8376/8470] Replayed DkMath.CosmicFormula.CosmicFormulaPythagoras
info: DkMath/CosmicFormula/CosmicFormulaPythagoras.lean:10:0: file: DkMath.CosmicFormula.CosmicFormulaPythagoras
ℹ [8377/8470] Replayed DkMath.CosmicFormula.CosmicFormulaPythagorasExamples
info: DkMath/CosmicFormula/CosmicFormulaPythagorasExamples.lean:10:0: file: DkMath.CosmicFormula.CosmicFormulaPythagorasExamples
ℹ [8378/8470] Replayed DkMath.CosmicFormula
info: DkMath/CosmicFormula.lean:12:0: file: DkMath.CosmicFormula
-/
set_option linter.style.longLine true

end ParametrizationExamples

/-! ## Cosmic Difference Structure Examples

Demonstrating the difference structure `c² - a² = b²` in specific examples.
-/

/-- For (3,4,5): 5² - 3² = 4² -/
example : (5 : ℤ)^2 - 3^2 = 4^2 := by norm_num

/-- For (5,12,13): 13² - 5² = 12² -/
example : (13 : ℤ)^2 - 5^2 = 12^2 := by norm_num

/-- For (8,15,17): 17² - 8² = 15² -/
example : (17 : ℤ)^2 - 8^2 = 15^2 := by norm_num

/-! ## Cosmic Form: c = a + u Structure

Demonstrating the cosmic form b² = 2au + u² for specific examples.
-/

/-- For (3,4,5): c = a + u gives u = 2, and b² = 2au + u² -/
example : let a : ℤ := 3
          let c : ℤ := 5
          let u : ℤ := c - a
          let b_squared : ℤ := 2 * a * u + u^2
          b_squared = 4^2 := by
  norm_num

/-- For (5,12,13): c = a + u gives u = 8, and b² = 2au + u² -/
example : let a : ℤ := 5
          let c : ℤ := 13
          let u : ℤ := c - a
          let b_squared : ℤ := 2 * a * u + u^2
          b_squared = 12^2 := by
  norm_num

/-- For (8,15,17): c = a + u gives u = 9, and b² = 2au + u² -/
example : let a : ℤ := 8
          let c : ℤ := 17
          let u : ℤ := c - a
          let b_squared : ℤ := 2 * a * u + u^2
          b_squared = 15^2 := by
  norm_num

/-! ## Gap and Beam Factorization

Demonstrating b² = u × (2a + u) for specific examples.
-/

/-- For (3,4,5): 4² = 2 × (2×3 + 2) = 2 × 8 -/
example : (4 : ℤ)^2 = 2 * (2 * 3 + 2) := by norm_num

/-- For (5,12,13): 12² = 8 × (2×5 + 8) = 8 × 18 -/
example : (12 : ℤ)^2 = 8 * (2 * 5 + 8) := by norm_num

/-- For (8,15,17): 15² = 9 × (2×8 + 9) = 9 × 25 -/
example : (15 : ℤ)^2 = 9 * (2 * 8 + 9) := by norm_num

end DkMath.CosmicFormula.Pythagoras.Examples
