/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Hackathon.JacobianCounterexample3.PolynomialMap
import Mathlib.Tactic

namespace DkMath.Hackathon.JacobianCounterexample3

/-- The first rational point in the explicit three-point collision. -/
def p0Q : Point3Q := ![(0 : ℚ), 0, -(1 / 4)]

/-- The second rational point in the explicit three-point collision. -/
def p1Q : Point3Q := ![(1 : ℚ), -(3 / 2), 13 / 2]

/-- The third rational point in the explicit three-point collision. -/
def p2Q : Point3Q := ![(-1 : ℚ), 3 / 2, 13 / 2]

/-- The common image of the three explicit rational points. -/
def targetQ : Point3Q := ![-(1 / 4 : ℚ), 0, 0]

theorem eval_p0Q :
    evalCounterexampleQ p0Q = targetQ := by
  ext i
  fin_cases i <;>
    simp [evalCounterexampleQ, counterexamplePoly, counterexampleP,
      counterexampleQ, counterexampleR, p0Q, targetQ, x, y, z]

theorem eval_p1Q :
    evalCounterexampleQ p1Q = targetQ := by
  ext i
  fin_cases i <;>
    simp [evalCounterexampleQ, counterexamplePoly, counterexampleP,
      counterexampleQ, counterexampleR, p1Q, targetQ, x, y, z] <;>
    norm_num

theorem eval_p2Q :
    evalCounterexampleQ p2Q = targetQ := by
  ext i
  fin_cases i <;>
    simp [evalCounterexampleQ, counterexamplePoly, counterexampleP,
      counterexampleQ, counterexampleR, p2Q, targetQ, x, y, z] <;>
    norm_num

theorem p0Q_ne_p1Q : p0Q ≠ p1Q := by
  intro h
  have h0 := congrFun h 0
  norm_num [p0Q, p1Q] at h0

theorem p0Q_ne_p2Q : p0Q ≠ p2Q := by
  intro h
  have h0 := congrFun h 0
  norm_num [p0Q, p2Q] at h0

theorem p1Q_ne_p2Q : p1Q ≠ p2Q := by
  intro h
  have h0 := congrFun h 0
  norm_num [p1Q, p2Q] at h0

/-- The compact certificate that the three distinct points have one common image. -/
theorem three_point_collision_Q :
    p0Q ≠ p1Q ∧ p0Q ≠ p2Q ∧ p1Q ≠ p2Q ∧
      evalCounterexampleQ p0Q = targetQ ∧
      evalCounterexampleQ p1Q = targetQ ∧
      evalCounterexampleQ p2Q = targetQ := by
  exact ⟨p0Q_ne_p1Q, p0Q_ne_p2Q, p1Q_ne_p2Q,
    eval_p0Q, eval_p1Q, eval_p2Q⟩

end DkMath.Hackathon.JacobianCounterexample3
