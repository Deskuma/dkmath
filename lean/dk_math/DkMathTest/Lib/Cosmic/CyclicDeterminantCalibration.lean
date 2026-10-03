/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Cosmic.CyclicDeterminant
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum

namespace DkMathTest.CyclicDeterminant

open DkMath.CosmicFormula Matrix

/-- Length one is `z-u`, since the cyclic shift coincides with the identity. -/
theorem length_one {R : Type*} [CommRing R] (z u : R) :
    cyclicPencil 0 z u 0 0 = z - u ∧ (cyclicPencil 0 z u).det = z - u := by
  constructor
  · simp [cyclicPencil, cyclicShift]
  · simpa using det_cyclicPencil 0 z u

/-- Even cycle length has a minus sign, not a parity-dependent plus sign. -/
example {R : Type*} [CommRing R] (z u : R) :
    (cyclicPencil 1 z u).det = z ^ 2 - u ^ 2 := det_cyclicPencil 1 z u

example : (cyclicPencil 2 (3 : ℤ) 1).det = 26 := by
  rw [det_cyclicPencil]
  norm_num

example : (cyclicPencil 3 (3 : ℤ) 1).det = 80 := by
  rw [det_cyclicPencil]
  norm_num

/-- The zero gap annihilates the full determinant in every rank. -/
theorem zero_gap {R : Type*} [CommRing R] (n : ℕ) (u : R) :
    (cyclicPencil n (0 + u) u).det = 0 := by
  rw [det_cyclicPencil_eq_mul_GN, zero_mul]

/-- The GN shell itself need not vanish at zero gap. -/
example : (cyclicPencil 2 (0 + 1 : ℤ) 1).det = 0 ∧ GTail 3 1 (0 : ℤ) 1 = 3 := by
  constructor
  · exact zero_gap 2 1
  · norm_num [GTail, Finset.sum_range_succ]

/-- A nonunit gap separates the entire determinant from its GN shell. -/
theorem full_carrier_vs_shell :
    (cyclicPencil 2 (2 + 1 : ℤ) 1).det = 26 ∧ GTail 3 1 (2 : ℤ) 1 = 13 := by
  constructor
  · rw [det_cyclicPencil]; norm_num
  · norm_num [GTail, Finset.sum_range_succ]

example : (cyclicPencil 3 (2 : ZMod 4) 1).det = 3 := by
  rw [det_cyclicPencil]
  decide

/-- The empty determinant is one, so the power-difference claim needs positive length. -/
theorem empty_boundary :
    (1 : Matrix (Fin 0) (Fin 0) ℤ).det = 1 ∧ (3 : ℤ) ^ 0 - 1 ^ 0 = 0 := by
  simp

end DkMathTest.CyclicDeterminant
