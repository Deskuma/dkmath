/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Hackathon.JacobianCounterexample3.Counterexample
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

namespace DkMath.Hackathon.JacobianCounterexample3

noncomputable section

/-- Polynomials in three variables with complex coefficients. -/
abbrev Poly3C := MvPolynomial Var3 ℂ

/-- Complex points with coordinates ordered as `x`, `y`, and `z`. -/
abbrev Point3C := Var3 → ℂ

/-- The canonical coefficient embedding from `ℚ` into `ℂ`. -/
def qToC : ℚ →+* ℂ := algebraMap ℚ ℂ

/-- Coefficientwise transport of three-variable polynomials from `ℚ` to `ℂ`. -/
def polyMapQC : Poly3Q →+* Poly3C := MvPolynomial.map qToC

/-- Coordinatewise transport of a rational point into complex space. -/
def castPointQC (p : Point3Q) : Point3C := fun i ↦ qToC (p i)

def p0C : Point3C := castPointQC p0Q
def p1C : Point3C := castPointQC p1Q
def p2C : Point3C := castPointQC p2Q
def targetC : Point3C := castPointQC targetQ

/-- The rational counterexample polynomials transported coefficientwise to `ℂ`. -/
def counterexamplePolyC : Fin 3 → Poly3C :=
  fun i ↦ polyMapQC (counterexamplePoly i)

/-- Actual polynomial evaluation of the transported map over `ℂ`. -/
def evalCounterexampleC (p : Point3C) : Point3C :=
  fun i ↦ MvPolynomial.eval p (counterexamplePolyC i)

/-- Evaluation commutes with transport from rational to complex coefficients. -/
theorem evalCounterexampleC_castPointQC (p : Point3Q) :
    evalCounterexampleC (castPointQC p) =
      castPointQC (evalCounterexampleQ p) := by
  funext i
  simp only [evalCounterexampleC, castPointQC, counterexamplePolyC,
    polyMapQC, evalCounterexampleQ, MvPolynomial.eval_map]
  change MvPolynomial.eval₂ qToC (qToC ∘ p) (counterexamplePoly i) =
    qToC (MvPolynomial.eval p (counterexamplePoly i))
  exact (MvPolynomial.eval₂_comp qToC p (counterexamplePoly i)).symm

theorem eval_p0C : evalCounterexampleC p0C = targetC := by
  rw [p0C, targetC, evalCounterexampleC_castPointQC, eval_p0Q]

theorem eval_p1C : evalCounterexampleC p1C = targetC := by
  rw [p1C, targetC, evalCounterexampleC_castPointQC, eval_p1Q]

theorem eval_p2C : evalCounterexampleC p2C = targetC := by
  rw [p2C, targetC, evalCounterexampleC_castPointQC, eval_p2Q]

theorem p0C_ne_p1C : p0C ≠ p1C := by
  intro h
  have h0 := congrFun h 0
  norm_num [p0C, p1C, castPointQC, qToC, p0Q, p1Q] at h0

theorem p0C_ne_p2C : p0C ≠ p2C := by
  intro h
  have h0 := congrFun h 0
  norm_num [p0C, p2C, castPointQC, qToC, p0Q, p2Q] at h0

theorem p1C_ne_p2C : p1C ≠ p2C := by
  intro h
  have h0 := congrFun h 0
  norm_num [p1C, p2C, castPointQC, qToC, p1Q, p2Q] at h0

/-- Three distinct complex points in one fiber of the transported map. -/
theorem three_point_collision_C :
    p0C ≠ p1C ∧ p0C ≠ p2C ∧ p1C ≠ p2C ∧
      evalCounterexampleC p0C = targetC ∧
      evalCounterexampleC p1C = targetC ∧
      evalCounterexampleC p2C = targetC := by
  exact ⟨p0C_ne_p1C, p0C_ne_p2C, p1C_ne_p2C,
    eval_p0C, eval_p1C, eval_p2C⟩

/-- The formal Jacobian of the transported complex polynomial map. -/
def jacobianMatrixC : Matrix (Fin 3) (Fin 3) Poly3C :=
  fun i j ↦ MvPolynomial.pderiv j (counterexamplePolyC i)

/-- Formal differentiation commutes with coefficient transport to `ℂ`. -/
theorem jacobianMatrixC_eq_map :
    jacobianMatrixC = polyMapQC.mapMatrix jacobianMatrixQ := by
  funext i j
  simp [jacobianMatrixC, counterexamplePolyC, polyMapQC,
    jacobianMatrixQ, MvPolynomial.pderiv_map]

/-- The complex formal Jacobian has constant determinant `-2`. -/
theorem jacobianMatrixC_det_eq_neg_two :
    jacobianMatrixC.det = MvPolynomial.C (-2 : ℂ) := by
  rw [jacobianMatrixC_eq_map]
  rw [← RingHom.map_det]
  rw [jacobianMatrixQ_det_eq_neg_two]
  simp [polyMapQC, qToC]

/-- The complex formal Jacobian determinant is nonzero. -/
theorem jacobianMatrixC_det_ne_zero : jacobianMatrixC.det ≠ 0 := by
  rw [jacobianMatrixC_det_eq_neg_two]
  norm_num

/-- The transported complex polynomial map is not injective. -/
theorem evalCounterexampleC_notInjective :
    ¬ Function.Injective evalCounterexampleC := by
  intro hinj
  apply p0C_ne_p1C
  apply hinj
  rw [eval_p0C, eval_p1C]

/-- The noninjective complex polynomial map has no left inverse. -/
theorem evalCounterexampleC_noLeftInverse :
    ¬ ∃ G : Point3C → Point3C,
      Function.LeftInverse G evalCounterexampleC := by
  rintro ⟨G, hG⟩
  exact evalCounterexampleC_notInjective hG.injective

/--
A complex polynomial map with constant nonzero formal Jacobian determinant
and an explicit collision.
-/
theorem jacobianCounterexampleCertificateC :
    jacobianMatrixC.det = MvPolynomial.C (-2 : ℂ) ∧
    jacobianMatrixC.det ≠ 0 ∧
    ¬ Function.Injective evalCounterexampleC := by
  exact ⟨jacobianMatrixC_det_eq_neg_two,
    jacobianMatrixC_det_ne_zero,
    evalCounterexampleC_notInjective⟩

end

end DkMath.Hackathon.JacobianCounterexample3
