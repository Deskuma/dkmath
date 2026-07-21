/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Hackathon.JacobianCounterexample3.PolynomialMap
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

namespace DkMath.Hackathon.JacobianCounterexample3

noncomputable section

/-- The formal Jacobian obtained by differentiating the polynomial map. -/
def jacobianMatrixQ : Matrix (Fin 3) (Fin 3) Poly3Q :=
  fun i j ↦ MvPolynomial.pderiv j (counterexamplePoly i)

/-- The componentwise normal form of the formal Jacobian. -/
def explicitJacobianQ : Matrix (Fin 3) (Fin 3) Poly3Q :=
  !![
    3 * y * (1 + x * y) ^ 2 * z + y ^ 3 * (7 + 6 * x * y),
      3 * x * (1 + x * y) ^ 2 * z
        + 2 * y * (1 + x * y) * (4 + 3 * x * y)
        + x * y ^ 2 * (7 + 6 * x * y),
      (1 + x * y) ^ 3;
    3 * (1 + x * y) ^ 2 * z
        + 6 * x * y * (1 + x * y) * z
        + 3 * y ^ 2 * (4 + 3 * x * y)
        + 9 * x * y ^ 3,
      1 + 6 * x ^ 2 * (1 + x * y) * z
        + 6 * x * y * (4 + 3 * x * y)
        + 9 * x ^ 2 * y ^ 2,
      3 * x * (1 + x * y) ^ 2;
    2 - 6 * x * y - 3 * x ^ 2 * z,
      -3 * x ^ 2,
      -x ^ 3]

private theorem pderiv_two (i : Var3) :
    MvPolynomial.pderiv i (2 : Poly3Q) = 0 := by
  rw [show (2 : Poly3Q) = MvPolynomial.C (2 : ℚ) by rfl]
  exact MvPolynomial.pderiv_C

private theorem pderiv_three (i : Var3) :
    MvPolynomial.pderiv i (3 : Poly3Q) = 0 := by
  rw [show (3 : Poly3Q) = MvPolynomial.C (3 : ℚ) by rfl]
  exact MvPolynomial.pderiv_C

private theorem pderiv_four (i : Var3) :
    MvPolynomial.pderiv i (4 : Poly3Q) = 0 := by
  rw [show (4 : Poly3Q) = MvPolynomial.C (4 : ℚ) by rfl]
  exact MvPolynomial.pderiv_C

/-- The formal derivatives agree with the displayed componentwise Jacobian. -/
theorem jacobianMatrixQ_eq_explicit :
    jacobianMatrixQ = explicitJacobianQ := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [jacobianMatrixQ, explicitJacobianQ, counterexamplePoly,
      counterexampleP, counterexampleQ, counterexampleR, x, y, z,
      pderiv_two, pderiv_three, pderiv_four] <;>
    ring_nf

end

end DkMath.Hackathon.JacobianCounterexample3
