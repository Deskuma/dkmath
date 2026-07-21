/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Hackathon.JacobianCounterexample3.Jacobian
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

namespace DkMath.Hackathon.JacobianCounterexample3

noncomputable section

/-- The determinant of the formal Jacobian is the constant polynomial `-2`. -/
theorem jacobianMatrixQ_det_eq_neg_two :
    jacobianMatrixQ.det = MvPolynomial.C (-2 : ℚ) := by
  rw [jacobianMatrixQ_eq_explicit]
  rw [Matrix.det_fin_three]
  simp [explicitJacobianQ]
  ring_nf
  rfl

/-- The formal Jacobian determinant is nonzero. -/
theorem jacobianMatrixQ_det_ne_zero :
    jacobianMatrixQ.det ≠ 0 := by
  rw [jacobianMatrixQ_det_eq_neg_two]
  norm_num

end

end DkMath.Hackathon.JacobianCounterexample3
