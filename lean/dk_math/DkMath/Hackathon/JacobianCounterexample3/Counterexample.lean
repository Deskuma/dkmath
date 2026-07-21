/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Hackathon.JacobianCounterexample3.Collision
import DkMath.Hackathon.JacobianCounterexample3.Determinant

namespace DkMath.Hackathon.JacobianCounterexample3

/-- The explicit rational collision shows that the polynomial map is not injective. -/
theorem evalCounterexampleQ_notInjective :
    ¬ Function.Injective evalCounterexampleQ := by
  intro hinj
  apply p0Q_ne_p1Q
  apply hinj
  rw [eval_p0Q, eval_p1Q]

/-- The noninjective rational polynomial map has no left inverse. -/
theorem evalCounterexampleQ_noLeftInverse :
    ¬ ∃ G : Point3Q → Point3Q,
      Function.LeftInverse G evalCounterexampleQ := by
  rintro ⟨G, hG⟩
  exact evalCounterexampleQ_notInjective hG.injective

/--
A rational polynomial map with constant nonzero formal Jacobian determinant
and an explicit collision.
-/
theorem jacobianCounterexampleCertificateQ :
    jacobianMatrixQ.det = MvPolynomial.C (-2 : ℚ) ∧
    jacobianMatrixQ.det ≠ 0 ∧
    ¬ Function.Injective evalCounterexampleQ := by
  exact ⟨jacobianMatrixQ_det_eq_neg_two,
    jacobianMatrixQ_det_ne_zero,
    evalCounterexampleQ_notInjective⟩

end DkMath.Hackathon.JacobianCounterexample3
