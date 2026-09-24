/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberGeometry
import DkMath.SilverRatio.Sqrt2Lemmas

open scoped InnerProductSpace

#print "file: DkMathTest.NumberGeometry.RadicalAxiomAudit"

#check DkMath.NumberGeometry.norm_sq_add_sqrt_smul
#check DkMath.NumberGeometry.norm_sq_add_sqrt_smul_of_inner_eq_zero
#check DkMath.NumberGeometry.pairMass_radical
#check DkMath.NumberGeometry.pairMass_radical_of_inner_eq_zero
#check DkMath.NumberGeometry.pairMass_radical_conj_sub
#check DkMath.NumberGeometry.pairMass_radical_conj_eq_iff_inner_eq_zero
#check DkMath.NumberGeometry.mem_massLevelSet_radical_of_inner_eq_zero
#check DkMath.SilverRatio.Sqrt2.sqrt2_sq

#print axioms DkMath.NumberGeometry.norm_sq_add_sqrt_smul
#print axioms DkMath.NumberGeometry.norm_sq_add_sqrt_smul_of_inner_eq_zero
#print axioms DkMath.NumberGeometry.pairMass_radical
#print axioms DkMath.NumberGeometry.pairMass_radical_of_inner_eq_zero
#print axioms DkMath.NumberGeometry.pairMass_radical_conj_sub
#print axioms DkMath.NumberGeometry.pairMass_radical_conj_eq_iff_inner_eq_zero
#print axioms DkMath.NumberGeometry.mem_massLevelSet_radical_of_inner_eq_zero

noncomputable section

abbrev e0 : DkMath.NumberGeometry.Point :=
  EuclideanSpace.single 0 (1 : ℝ)

abbrev e1 : DkMath.NumberGeometry.Point :=
  EuclideanSpace.single 1 (1 : ℝ)

/-- The two coordinate unit vectors give a concrete orthogonal sqrt(2) calibration. -/
theorem sqrt2_radical_calibration :
    ‖e0 + DkMath.SilverRatio.Sqrt2.sqrt2 • e1‖ ^ 2 = (3 : ℝ) := by
  have horth : ⟪e0, e1⟫_ℝ = 0 := by
    simp [e0, e1, EuclideanSpace.inner_single_right]
  have hsqrt :
      Real.sqrt (DkMath.SilverRatio.Sqrt2.sqrt2 ^ 2) =
        DkMath.SilverRatio.Sqrt2.sqrt2 := by
    exact Real.sqrt_sq (le_of_lt DkMath.SilverRatio.Sqrt2.sqrt2_pos)
  have h :=
    DkMath.NumberGeometry.norm_sq_add_sqrt_smul_of_inner_eq_zero e0 e1
      (m := DkMath.SilverRatio.Sqrt2.sqrt2 ^ 2)
      (sq_nonneg _)
      horth
  rw [hsqrt, DkMath.SilverRatio.Sqrt2.sqrt2_sq] at h
  norm_num at h
  simpa [e0, e1] using h
#print axioms sqrt2_radical_calibration

end
