/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.StructuralArithmetic.RadialScaling

/-!
# Cosmic-square analytic scaling

This module certifies one bounded square-case analytic image
`F(y) = sqrt (1 + y) - 1`, its dynamic logarithmic scale, and the exact
`Real.rpow` reconstruction on the positive domain.  The resulting scalar is
then fed to the fixed-index radial prime-coordinate image from Phase H.

The analytic identity is pointwise and does not assert a multiplicative map,
real prime factorization, or an identification with PowerGauge projection,
KUS transport, or the Cosmic Formula polynomial degree.
-/

namespace DkMath.NumberTheory.StructuralArithmetic

/-- The positive-branch square-case image `sqrt (1 + y) - 1`. -/
noncomputable def cosmicSquareImage (y : ℝ) : ℝ :=
  Real.sqrt (1 + y) - 1

/-- Positivity of the square-case image for positive input. -/
theorem cosmicSquareImage_pos {y : ℝ} (hy : 0 < y) :
    0 < cosmicSquareImage y := by
  have hs : 1 < Real.sqrt (1 + y) := by
    apply (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)).2
    nlinarith
  dsimp [cosmicSquareImage]
  linarith

/-- The square-case image satisfies its defining quadratic reconstruction. -/
theorem cosmicSquareImage_add_one_sq {y : ℝ} (hy : 0 ≤ y) :
    (cosmicSquareImage y + 1) ^ 2 = 1 + y := by
  dsimp [cosmicSquareImage]
  nlinarith [Real.sq_sqrt (by linarith : (0 : ℝ) ≤ 1 + y)]

/-- The logarithmic exponent reconstructs a positive target from a positive base. -/
theorem rpow_log_ratio
    {base target : ℝ}
    (hbase : 0 < base) (hbase1 : base ≠ 1) (htarget : 0 < target) :
    Real.rpow base (Real.log target / Real.log base) = target := by
  change base ^ (Real.log target / Real.log base) = target
  rw [Real.rpow_def_of_pos hbase]
  have hlog : Real.log base ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one hbase hbase1
  rw [mul_div_cancel₀ _ hlog, Real.exp_log htarget]

/-- The dynamic logarithmic scale for the square-case image. -/
noncomputable def cosmicSquareScale (y : ℝ) : ℝ :=
  Real.log (cosmicSquareImage y) / Real.log y

/-- Exact analytic reconstruction of the square-case image from its dynamic scale. -/
theorem cosmicSquareImage_rpow_scale
    {y : ℝ} (hy : 0 < y) (hy1 : y ≠ 1) :
    Real.rpow y (cosmicSquareScale y) = cosmicSquareImage y := by
  exact rpow_log_ratio hy hy1 (cosmicSquareImage_pos hy)

/-- At `y = 3`, the square-case image is exactly one. -/
@[simp] theorem cosmicSquareImage_three :
    cosmicSquareImage 3 = 1 := by
  norm_num [cosmicSquareImage]

/-- At `y = 3`, the dynamic logarithmic scale is zero, the radial-collapse boundary. -/
@[simp] theorem cosmicSquareScale_three :
    cosmicSquareScale 3 = 0 := by
  simp [cosmicSquareScale]

/-- Dynamic real prime-coordinate images driven by the square-case scale. -/
noncomputable def dynamicPrimeCoordinates (y : ℝ) (n : ℕ) : PrimeIndex → ℝ :=
  radialScalePrimeCoordinates (cosmicSquareScale y) n

/-- Dynamic prime coordinates preserve zero-pattern when the selected scale is nonzero. -/
theorem dynamicPrimeCoordinates_eq_zero_iff
    {y : ℝ} (hk : cosmicSquareScale y ≠ 0) (n : ℕ) (p : PrimeIndex) :
    dynamicPrimeCoordinates y n p = 0 ↔
      realPrimeExponentCoordinates n p = 0 := by
  exact radialScalePrimeCoordinates_eq_zero_iff hk n p

/-- Dynamic prime-coordinate support is preserved by a nonzero square-case scale. -/
theorem support_dynamicPrimeCoordinates
    {y : ℝ} (hk : cosmicSquareScale y ≠ 0) (n : ℕ) :
    Function.support (dynamicPrimeCoordinates y n) =
      Function.support (realPrimeExponentCoordinates n) := by
  exact support_radialScaleCoordinates hk (realPrimeExponentCoordinates n)

/-- The square-case image at thirty is the exact symbolic value `sqrt 31 - 1`. -/
@[simp] theorem cosmicSquareImage_thirty :
    cosmicSquareImage 30 = Real.sqrt 31 - 1 := by
  norm_num [cosmicSquareImage]

/-- The dynamic scale at thirty is nonzero, so its radial image preserves support. -/
theorem cosmicSquareScale_thirty_ne_zero :
    cosmicSquareScale 30 ≠ 0 := by
  intro hscale
  have hlog : Real.log (cosmicSquareImage 30) = 0 := by
    have hden : Real.log (30 : ℝ) ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
    have hz := (div_eq_zero_iff).mp (show
      Real.log (cosmicSquareImage 30) / Real.log (30 : ℝ) = 0 by
        simpa [cosmicSquareScale] using hscale)
    exact hz.resolve_right hden
  have hcases := (Real.log_eq_zero.mp hlog)
  rcases hcases with hzero | hone | hneg
  · exact (ne_of_gt (cosmicSquareImage_pos (y := (30 : ℝ)) (by norm_num))) hzero
  · rw [cosmicSquareImage_thirty] at hone
    have hsqrt : Real.sqrt (31 : ℝ) = 2 := by linarith
    have hsquare := Real.sq_sqrt (show (0 : ℝ) ≤ 31 by norm_num)
    rw [hsqrt] at hsquare
    norm_num at hsquare
  · have hpos := cosmicSquareImage_pos (y := (30 : ℝ)) (by norm_num)
    rw [hneg] at hpos
    norm_num at hpos

/-- Exact analytic reconstruction at thirty, without decimal approximation. -/
theorem thirty_rpow_cosmicSquareScale :
    Real.rpow 30 (cosmicSquareScale 30) = Real.sqrt 31 - 1 := by
  have h := cosmicSquareImage_rpow_scale (y := (30 : ℝ)) (by norm_num) (by norm_num)
  norm_num [cosmicSquareImage] at h ⊢
  exact h

/-- The thirty-driven prime-coordinate image has the original support. -/
theorem support_dynamicPrimeCoordinates_thirty (n : ℕ) :
    Function.support (dynamicPrimeCoordinates 30 n) =
      Function.support (realPrimeExponentCoordinates n) :=
  support_dynamicPrimeCoordinates cosmicSquareScale_thirty_ne_zero n

end DkMath.NumberTheory.StructuralArithmetic
