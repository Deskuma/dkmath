/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.GTailSevenNormReadout

#print "file: DkMathTest.NumberTheory.GTailSevenNormReadout"

/-! Typed coordinate, sign, boundary and information-loss regressions. -/

namespace DkMathTest.NumberTheory.GTailSevenNormReadout

open DkMath.NumberTheory.TraceOneQuadratic DkMath.Lib.NumberTheory DkMath.CosmicFormula

example : gtailSevenNormCoord 5 8 = (⟨5, 8⟩ : TraceOneInt (-1)) :=
  gtailSevenNormCoord_eq 5 8

example : norm (gtailSevenNormCoord 0 0) = 0 := by
  rw [norm_gtailSevenNormCoord]
  norm_num

example : norm (gtailSevenNormCoord 1 0) = 1 := by
  rw [norm_gtailSevenNormCoord]
  norm_num

example : norm (gtailSevenNormCoord 0 1) = 1 := by
  rw [norm_gtailSevenNormCoord]
  norm_num

example : norm (gtailSevenNormCoord 5 8) = 129 := by
  rw [norm_gtailSevenNormCoord]
  norm_num

example : norm ((gtailSevenNormCoord 5 8 : TraceOneInt (-1)) ^ 2) = 16641 := by
  rw [norm_gtailSevenNormCoord_sq]
  norm_num

example : (gtailSevenNormCoord 5 8 : TraceOneInt (-1)) ^ 2 = ⟨-39, 144⟩ := by decide

example : (43 : ℤ) ∣ norm (gtailSevenNormCoord 5 8) :=
  (dvd_quadratic_iff_dvd_gtailSevenNormCoord 43 5 8).mp (by decide)

-- Apply the typed Body receiver, then independently check its actual sum.
example : selectedBody 7 (Finset.Ico 1 7) (5 : ℤ) 8 = 60573240 := by
  have hbody := selectedBody_seven_interior_eq_norm_square 5 8
  rw [norm_gtailSevenNormCoord_sq] at hbody
  norm_num at hbody
  exact hbody

example : selectedBody 7 (Finset.Ico 1 7) (5 : ℤ) 8 = 60573240 ∧
    (60573240 : ℤ) = 7 * 5 * 8 * 13 * 16641 := by decide

-- Uncorrected Eisenstein coordinates have the opposite mixed sign.
example : norm (eisensteinCoord 5 8) = 49 ∧ norm (gtailSevenNormCoord 5 8) = 129 := by decide

-- Norm is not injective, even on explicit integral elements of norm one.
example : norm (⟨1, 0⟩ : TraceOneInt (-1)) = 1 ∧
    norm (⟨0, 1⟩ : TraceOneInt (-1)) = 1 ∧
    (⟨1, 0⟩ : TraceOneInt (-1)) ≠ ⟨0, 1⟩ := by decide

#print axioms gtailSevenNormCoord
#print axioms gtailSevenNormCoord_eq
#print axioms norm_gtailSevenNormCoord
#print axioms norm_gtailSevenNormCoord_sq
#print axioms dvd_quadratic_iff_dvd_gtailSevenNormCoord
#print axioms selectedBody_seven_interior_eq_norm_square

end DkMathTest.NumberTheory.GTailSevenNormReadout
