/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.MirrorRootOfUnity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.MirrorAngleBranch"

namespace DkMath.RH.CFBRCProjection

/-- A point on the complex unit circle written in real trigonometric coordinates. -/
noncomputable def unitCircleAt (φ : ℝ) : ℂ :=
  (Real.cos φ : ℂ) + Complex.I * (Real.sin φ : ℂ)

@[simp] theorem unitCircleAt_re (φ : ℝ) :
    (unitCircleAt φ).re = Real.cos φ := by
  simp only [unitCircleAt, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    zero_mul, one_mul, sub_zero, add_zero]

@[simp] theorem unitCircleAt_im (φ : ℝ) :
    (unitCircleAt φ).im = Real.sin φ := by
  simp only [unitCircleAt, Complex.add_im, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    zero_mul, one_mul, zero_add, add_zero]

/--
When the mirror multiplier is written as `cos φ + i sin φ`, the complex map
splits into two explicit real branch equations.
-/
theorem mirror_map_implies_trig_branch_equations
    {X Θ φ : ℝ}
    (hmap : mirrorLeft X Θ = unitCircleAt φ * mirrorRight X Θ) :
    (1 + Real.cos φ) * X + Real.sin φ * Θ = 0 ∧
      Real.sin φ * X + (1 - Real.cos φ) * Θ = 0 := by
  simpa only [unitCircleAt_re, unitCircleAt_im] using
    (mirror_map_implies_linear_branch_equations
      (X := X) (Θ := Θ) (ω := unitCircleAt φ) hmap)

/--
On a non-antipodal trigonometric branch, solve the first real equation for `X`.
-/
theorem mirror_branch_x_eq_trig_ratio
    {X Θ φ : ℝ}
    (hmap : mirrorLeft X Θ = unitCircleAt φ * mirrorRight X Θ)
    (hden : 1 + Real.cos φ ≠ 0) :
    X = (-Real.sin φ * Θ) / (1 + Real.cos φ) := by
  simpa only [unitCircleAt_re, unitCircleAt_im] using
    (mirror_branch_x_eq_ratio_mul_theta
      (X := X) (Θ := Θ) (ω := unitCircleAt φ)
      hmap (by simpa only [unitCircleAt_re] using hden))

/--
The standard half-angle identity in the exact orientation needed by the mirror
branch slope.
-/
theorem neg_sin_two_mul_div_one_add_cos_two_mul
    (φ : ℝ) (hcos : Real.cos φ ≠ 0) :
    (-Real.sin (2 * φ)) / (1 + Real.cos (2 * φ)) = -Real.tan φ := by
  rw [Real.sin_two_mul, Real.cos_two_mul, Real.tan_eq_sin_div_cos]
  field_simp [hcos]
  ring

/--
A mirror map whose multiplier has angle `2φ` lies on the half-angle tangent
branch, provided the half-angle is not antipodal.
-/
theorem mirror_branch_x_eq_neg_tan_mul_theta
    {X Θ φ : ℝ}
    (hmap : mirrorLeft X Θ = unitCircleAt (2 * φ) * mirrorRight X Θ)
    (hcos : Real.cos φ ≠ 0) :
    X = -Real.tan φ * Θ := by
  have hden : 1 + Real.cos (2 * φ) ≠ 0 := by
    rw [Real.cos_two_mul]
    have hsq : 0 < Real.cos φ ^ 2 := sq_pos_of_ne_zero hcos
    nlinarith
  have hx := mirror_branch_x_eq_trig_ratio hmap hden
  calc
    X = (-Real.sin (2 * φ) * Θ) / (1 + Real.cos (2 * φ)) := hx
    _ = ((-Real.sin (2 * φ)) / (1 + Real.cos (2 * φ))) * Θ := by
      ring
    _ = -Real.tan φ * Θ := by
      rw [neg_sin_two_mul_div_one_add_cos_two_mul φ hcos]

/-- Half-angle assigned to the `k`-th branch of degree `d`. -/
noncomputable def rootBranchHalfAngle (d k : ℕ) : ℝ :=
  Real.pi * (k : ℝ) / (d : ℝ)

/-- Unit-circle multiplier corresponding to the `k`-th degree-`d` branch. -/
noncomputable def indexedRootBranchUnit (d k : ℕ) : ℂ :=
  unitCircleAt (2 * rootBranchHalfAngle d k)

/--
Once a mirror multiplier is identified with the indexed unit-circle point, its
real branch is the expected explicit tangent line.
-/
theorem mirror_branch_x_eq_indexed_neg_tan_mul_theta
    {d k : ℕ} {X Θ : ℝ}
    (hmap : mirrorLeft X Θ = indexedRootBranchUnit d k * mirrorRight X Θ)
    (hcos : Real.cos (rootBranchHalfAngle d k) ≠ 0) :
    X = -Real.tan (rootBranchHalfAngle d k) * Θ := by
  exact
    mirror_branch_x_eq_neg_tan_mul_theta
      (X := X) (Θ := Θ) (φ := rootBranchHalfAngle d k)
      (by simpa [indexedRootBranchUnit] using hmap) hcos

end DkMath.RH.CFBRCProjection
