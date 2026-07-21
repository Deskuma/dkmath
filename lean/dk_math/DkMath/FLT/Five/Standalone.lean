/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.

Single-file seed for Lean Comparator Live.
This file imports Mathlib only and must not depend on DkMath modules.
-/

import Mathlib

#print "file: DkMath.FLT.Five.Standalone"

namespace DkMath.FLT.Five.Standalone

/-!
# Mathlib-only GN5 seed

This deliberately small namespace repeats the basic equation and cyclotomic
factorization without importing any DkMath module.  It is a comparison and portability
surface, not the public proof of `DkMath.FLT.Five.FLT5Target`.
-/

/-- The exponent-five Fermat equation. -/
def Fermat5Equation (x y z : ℕ) : Prop :=
  x ^ 5 + y ^ 5 = z ^ 5

/-- The exponent-five GN polynomial in local gap coordinates. -/
def GN5 (g y : ℕ) : ℕ :=
  g ^ 4
    + 5 * g ^ 3 * y
    + 10 * g ^ 2 * y ^ 2
    + 10 * g * y ^ 3
    + 5 * y ^ 4

/-- The standalone fifth-power body decomposition. -/
theorem add_pow_five_eq_add_mul_GN5 (g y : ℕ) :
    (g + y) ^ 5 = y ^ 5 + g * GN5 g y := by
  unfold GN5
  ring

/-- The standalone subtraction form. -/
theorem add_pow_five_sub_eq_mul_GN5 (g y : ℕ) :
    (g + y) ^ 5 - y ^ 5 = g * GN5 g y := by
  rw [add_pow_five_eq_add_mul_GN5]
  omega

/-- Concrete smoke test for the standalone seed. -/
theorem GN5_one_one : GN5 1 1 = 31 := by
  norm_num [GN5]

end DkMath.FLT.Five.Standalone
