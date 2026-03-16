/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib

/-!
This file records a DkMath sample family of solutions to

  a^2 + b^2 + c^2 = d^2.

The construction is induced from the cosmic square-gap identity

  (P + 1)^2 - (P - 1)^2 = 4P

together with the specialization

  P = m^2 + n^2.

Then the square-gap becomes

  4P = (2m)^2 + (2n)^2,

hence

  (m^2 + n^2 - 1)^2 + (2m)^2 + (2n)^2 = (m^2 + n^2 + 1)^2.
-/

namespace DkMath

/-- Cosmic square-gap identity. -/
theorem square_gap_of_P (P : ℤ) :
    (P + 1) ^ 2 - (P - 1) ^ 2 = 4 * P := by
  ring

/-- Expands `4 * (m^2 + n^2)` as a sum of two even squares. -/
theorem four_mul_sum_two_squares (m n : ℤ) :
    4 * (m ^ 2 + n ^ 2) = (2 * m) ^ 2 + (2 * n) ^ 2 := by
  ring

/--
A DkMath sample family:
`a = 2m`, `b = 2n`, `c = m^2 + n^2 - 1`, `d = m^2 + n^2 + 1`
gives `a^2 + b^2 + c^2 = d^2`.
-/
theorem sum_three_squares_eq_square_cosmic (m n : ℤ) :
    let a := 2 * m
    let b := 2 * n
    let c := m ^ 2 + n ^ 2 - 1
    let d := m ^ 2 + n ^ 2 + 1
    a ^ 2 + b ^ 2 + c ^ 2 = d ^ 2 := by
  dsimp
  ring

/-- Existence form of the same family. -/
theorem exists_sum_three_squares_eq_square (m n : ℤ) :
    ∃ a b c d : ℤ, a ^ 2 + b ^ 2 + c ^ 2 = d ^ 2 := by
  refine ⟨2 * m, 2 * n, m ^ 2 + n ^ 2 - 1, m ^ 2 + n ^ 2 + 1, ?_⟩
  -- ⊢ (2 * m) ^ 2 + (2 * n) ^ 2 + (m ^ 2 + n ^ 2 - 1) ^ 2 = (m ^ 2 + n ^ 2 + 1) ^ 2
  ring

end DkMath
