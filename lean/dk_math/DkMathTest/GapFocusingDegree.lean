/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.GapFocusing.Degree
import Mathlib.Data.ZMod.Basic

#print "file: DkMathTest.GapFocusingDegree"

open DkMath.CosmicFormula
open DkMath.NumberTheory.GapFocusing
open Polynomial

/-! Durable calibration of the polynomial and evaluated-value boundaries. -/

/-- Prime polynomial degree gives irreducibility over the integers. -/
example : Irreducible (kernelPolynomial 11) :=
  (kernelPolynomial_irreducible_iff_prime (d := 11) (by decide)).mpr (by decide)

/-- The same polynomial remains irreducible over the rationals. -/
example : Irreducible (GN 11 (X : ℚ[X]) 1) :=
  (GN_polynomial_rat_irreducible_iff_prime (d := 11) (by decide)).mpr (by decide)

/-- Evaluating that irreducible polynomial can produce a composite value. -/
theorem degree_eleven_composite_value : GN 11 (1 : ℕ) 1 = 23 * 89 := by
  calc
    _ = 2 ^ 11 - 1 := DkMath.NumberTheory.GN_one_one_eq_two_pow_sub_one 11
    _ = _ := by norm_num

example : ¬ Nat.Prime (GN 11 (1 : ℕ) 1) := by
  rw [degree_eleven_composite_value]
  exact Nat.not_prime_mul (by decide) (by decide)

/-- Degree six retains all three nontrivial cyclotomic layers. -/
example :
    kernelPolynomial 6 =
      (X + 2 : ℤ[X]) * (cyclotomic 3 ℤ).comp (X + 1) *
        (cyclotomic 6 ℤ).comp (X + 1) := by
  exact kernelPolynomial_two_mul_prime (p := 3) (by decide) (by decide)

/-- At `p = 2`, the divisor set has two distinct residual layers. -/
example : (4 : ℕ).divisors.erase 1 = {2, 4} := by decide

/-- The `2p` composition works with a zero gap in a ring with zero divisors. -/
example :
    GN 3 (0 : ZMod 4) 1 * ((0 + 1 : ZMod 4) ^ 3 + 1 ^ 3) =
      (0 + 2 * 1 : ZMod 4) * GN 3 (0 * (0 + 2 * 1 : ZMod 4)) (1 ^ 2) := by
  exact GN_two_mul_degree_orders 3 0 1

#print axioms kernelPolynomial_eq_prod_cyclotomic
#print axioms kernelPolynomial_irreducible_iff_prime
#print axioms GN_polynomial_rat_irreducible_iff_prime
#print axioms kernelPolynomial_two_mul_prime
#print axioms two_mul_prime_cyclotomic_layer_degrees
#print axioms GN_two_mul_degree_orders
