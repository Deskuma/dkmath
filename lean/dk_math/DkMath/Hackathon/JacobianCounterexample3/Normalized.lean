/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Hackathon.JacobianCounterexample3.ComplexLift
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

namespace DkMath.Hackathon.JacobianCounterexample3

noncomputable section

/-- Scale the first output coordinate by `-1/2`. -/
def normalizeOutputC (p : Point3C) : Point3C :=
  ![(-1 / 2 : ℂ) * p 0, p 1, p 2]

/-- The common collision target after output normalization. -/
def normalizedTargetC : Point3C := normalizeOutputC targetC

/-- The complex polynomial map with its first output coordinate scaled by `-1/2`. -/
def normalizedCounterexamplePolyC : Fin 3 → Poly3C :=
  ![MvPolynomial.C (-1 / 2 : ℂ) * counterexamplePolyC 0,
    counterexamplePolyC 1,
    counterexamplePolyC 2]

/-- Actual polynomial evaluation of the normalized complex map. -/
def evalNormalizedCounterexampleC (p : Point3C) : Point3C :=
  fun i ↦ MvPolynomial.eval p (normalizedCounterexamplePolyC i)

/-- Normalized evaluation is output scaling of the original evaluation. -/
theorem evalNormalizedCounterexampleC_eq_normalizeOutput (p : Point3C) :
    evalNormalizedCounterexampleC p =
      normalizeOutputC (evalCounterexampleC p) := by
  funext i
  fin_cases i <;>
    simp [evalNormalizedCounterexampleC, normalizedCounterexamplePolyC,
      normalizeOutputC, evalCounterexampleC]

theorem normalized_eval_p0C :
    evalNormalizedCounterexampleC p0C = normalizedTargetC := by
  rw [evalNormalizedCounterexampleC_eq_normalizeOutput, normalizedTargetC,
    eval_p0C]

theorem normalized_eval_p1C :
    evalNormalizedCounterexampleC p1C = normalizedTargetC := by
  rw [evalNormalizedCounterexampleC_eq_normalizeOutput, normalizedTargetC,
    eval_p1C]

theorem normalized_eval_p2C :
    evalNormalizedCounterexampleC p2C = normalizedTargetC := by
  rw [evalNormalizedCounterexampleC_eq_normalizeOutput, normalizedTargetC,
    eval_p2C]

/-- Three distinct complex points in one fiber of the normalized map. -/
theorem normalized_three_point_collision_C :
    p0C ≠ p1C ∧ p0C ≠ p2C ∧ p1C ≠ p2C ∧
      evalNormalizedCounterexampleC p0C = normalizedTargetC ∧
      evalNormalizedCounterexampleC p1C = normalizedTargetC ∧
      evalNormalizedCounterexampleC p2C = normalizedTargetC := by
  exact ⟨p0C_ne_p1C, p0C_ne_p2C, p1C_ne_p2C,
    normalized_eval_p0C, normalized_eval_p1C, normalized_eval_p2C⟩

/-- The formal Jacobian obtained from the normalized polynomial map. -/
def normalizedJacobianMatrixC : Matrix (Fin 3) (Fin 3) Poly3C :=
  fun i j ↦ MvPolynomial.pderiv j (normalizedCounterexamplePolyC i)

/-- The diagonal matrix implementing output-coordinate scaling on Jacobian rows. -/
def outputScaleDiagonalC : Matrix (Fin 3) (Fin 3) Poly3C :=
  Matrix.diagonal
    ![MvPolynomial.C (-1 / 2 : ℂ), 1, 1]

/-- The normalized formal Jacobian is obtained by scaling the first Jacobian row. -/
theorem normalizedJacobianMatrixC_eq_scale_mul :
    normalizedJacobianMatrixC = outputScaleDiagonalC * jacobianMatrixC := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [normalizedJacobianMatrixC, normalizedCounterexamplePolyC,
      outputScaleDiagonalC, jacobianMatrixC, Matrix.mul_apply,
      Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]

/-- The output-scaling diagonal matrix has determinant `-1/2`. -/
theorem outputScaleDiagonalC_det :
    outputScaleDiagonalC.det = MvPolynomial.C (-1 / 2 : ℂ) := by
  rw [Matrix.det_fin_three]
  simp [outputScaleDiagonalC]

/-- The normalized formal Jacobian has determinant one. -/
theorem normalizedJacobianMatrixC_det_eq_one :
    normalizedJacobianMatrixC.det = MvPolynomial.C (1 : ℂ) := by
  rw [normalizedJacobianMatrixC_eq_scale_mul]
  rw [Matrix.det_mul]
  rw [outputScaleDiagonalC_det]
  rw [jacobianMatrixC_det_eq_neg_two]
  rw [← MvPolynomial.C_mul]
  norm_num

/-- The normalized formal Jacobian determinant is nonzero. -/
theorem normalizedJacobianMatrixC_det_ne_zero :
    normalizedJacobianMatrixC.det ≠ 0 := by
  rw [normalizedJacobianMatrixC_det_eq_one]
  norm_num

/-- The normalized complex polynomial map is not injective. -/
theorem evalNormalizedCounterexampleC_notInjective :
    ¬ Function.Injective evalNormalizedCounterexampleC := by
  intro hinj
  apply p0C_ne_p1C
  apply hinj
  rw [normalized_eval_p0C, normalized_eval_p1C]

/-- The noninjective normalized polynomial map has no left inverse. -/
theorem evalNormalizedCounterexampleC_noLeftInverse :
    ¬ ∃ G : Point3C → Point3C,
      Function.LeftInverse G evalNormalizedCounterexampleC := by
  rintro ⟨G, hG⟩
  exact evalNormalizedCounterexampleC_notInjective hG.injective

/--
A complex polynomial map with formal Jacobian determinant one and an explicit
three-point collision.
-/
theorem normalizedJacobianCounterexampleCertificateC :
    normalizedJacobianMatrixC.det = MvPolynomial.C (1 : ℂ) ∧
    normalizedJacobianMatrixC.det ≠ 0 ∧
    ¬ Function.Injective evalNormalizedCounterexampleC := by
  exact ⟨normalizedJacobianMatrixC_det_eq_one,
    normalizedJacobianMatrixC_det_ne_zero,
    evalNormalizedCounterexampleC_notInjective⟩

end

end DkMath.Hackathon.JacobianCounterexample3
