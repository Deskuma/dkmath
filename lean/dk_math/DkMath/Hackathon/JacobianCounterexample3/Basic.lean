/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.Algebra.MvPolynomial.Eval

namespace DkMath.Hackathon.JacobianCounterexample3

/-- The three variables of the counterexample, ordered as `x`, `y`, and `z`. -/
abbrev Var3 := Fin 3

/-- Polynomials in three variables with rational coefficients. -/
abbrev Poly3Q := MvPolynomial Var3 ℚ

/-- Rational points with coordinates ordered as `x`, `y`, and `z`. -/
abbrev Point3Q := Var3 → ℚ

end DkMath.Hackathon.JacobianCounterexample3
