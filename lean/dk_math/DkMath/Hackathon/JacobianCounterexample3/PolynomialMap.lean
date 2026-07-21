/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Hackathon.JacobianCounterexample3.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

namespace DkMath.Hackathon.JacobianCounterexample3

noncomputable section

/-- The first coordinate variable. -/
def x : Poly3Q := MvPolynomial.X 0

/-- The second coordinate variable. -/
def y : Poly3Q := MvPolynomial.X 1

/-- The third coordinate variable. -/
def z : Poly3Q := MvPolynomial.X 2

/-- The first component `(1 + xy)^3 z + y^2 (1 + xy) (4 + 3xy)`. -/
def counterexampleP : Poly3Q :=
  (1 + x * y) ^ 3 * z + y ^ 2 * (1 + x * y) * (4 + 3 * x * y)

/-- The second component `y + 3x(1 + xy)^2 z + 3xy^2(4 + 3xy)`. -/
def counterexampleQ : Poly3Q :=
  y + 3 * x * (1 + x * y) ^ 2 * z + 3 * x * y ^ 2 * (4 + 3 * x * y)

/-- The third component `2x - 3x^2y - x^3z`. -/
def counterexampleR : Poly3Q :=
  2 * x - 3 * x ^ 2 * y - x ^ 3 * z

/-- The three polynomial components of the counterexample map. -/
def counterexamplePoly : Fin 3 → Poly3Q :=
  ![counterexampleP, counterexampleQ, counterexampleR]

/-- Evaluation of the counterexample polynomial map at a rational point. -/
def evalCounterexampleQ (p : Point3Q) : Point3Q :=
  fun i ↦ MvPolynomial.eval p (counterexamplePoly i)

end

end DkMath.Hackathon.JacobianCounterexample3
