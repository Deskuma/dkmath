/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.StructuralArithmetic.PrimeCoordinates

/-!
# DHNT-style radial scaling and rebase distinction

`radialScaleCoordinates` is pointwise scalar multiplication on a fixed index
type.  A nonzero scalar changes coordinate magnitudes but preserves the whole
zero-pattern, while the zero scalar is the explicit collapse boundary.

This operation is distinct from `DkMath.KUS.ScaleSpec`: that API transports a
typed unit/blueprint support and may represent a rebase, subject to its
observation-compatibility hypotheses.  It is also distinct from the
natural-valued `PowerGauge` projection, which reduces exponents modulo a
period.  No real prime-factorization or `Real.log`/`Real.rpow` reconstruction
is asserted here.
-/

namespace DkMath.NumberTheory.StructuralArithmetic

/-- Radially scale a real coordinate vector while keeping its index type fixed. -/
def radialScaleCoordinates {ι : Type*} (k : ℝ) (v : ι → ℝ) : ι → ℝ :=
  fun i => k * v i

/-- Scaling by one leaves a fixed real coordinate vector unchanged. -/
@[simp] theorem radialScaleCoordinates_one {ι : Type*} (v : ι → ℝ) :
    radialScaleCoordinates 1 v = v := by
  funext i
  simp [radialScaleCoordinates]

/-- Scaling by zero collapses every real coordinate to zero. -/
@[simp] theorem radialScaleCoordinates_zero {ι : Type*} (v : ι → ℝ) :
    radialScaleCoordinates 0 v = fun _ => 0 := by
  funext i
  simp [radialScaleCoordinates]

/-- Successive radial scales compose by multiplication of their scalars. -/
theorem radialScaleCoordinates_mul {ι : Type*} (a b : ℝ) (v : ι → ℝ) :
    radialScaleCoordinates a (radialScaleCoordinates b v) =
      radialScaleCoordinates (a * b) v := by
  funext i
  simp [radialScaleCoordinates, mul_assoc]

/-- A nonzero radial scale preserves whether any fixed coordinate is zero. -/
theorem radialScaleCoordinates_eq_zero_iff
    {ι : Type*} {k : ℝ} (hk : k ≠ 0) (v : ι → ℝ) (i : ι) :
    radialScaleCoordinates k v i = 0 ↔ v i = 0 := by
  simp [radialScaleCoordinates, hk]

/-- The support of a real coordinate vector is unchanged by a nonzero radial scale. -/
theorem support_radialScaleCoordinates
    {ι : Type*} {k : ℝ} (hk : k ≠ 0) (v : ι → ℝ) :
    Function.support (radialScaleCoordinates k v) = Function.support v := by
  ext i
  simp [Function.mem_support, radialScaleCoordinates_eq_zero_iff hk v i]

/-- Real-valued images of the existing natural prime-exponent coordinates. -/
def realPrimeExponentCoordinates (n : ℕ) : PrimeIndex → ℝ :=
  fun p => (primeExponentCoordinates n p : ℝ)

/-- A radially scaled real-valued image of natural prime-exponent coordinates. -/
def radialScalePrimeCoordinates (k : ℝ) (n : ℕ) : PrimeIndex → ℝ :=
  radialScaleCoordinates k (realPrimeExponentCoordinates n)

/-- Nonzero radial scaling preserves the zero-pattern of real prime coordinates. -/
theorem radialScalePrimeCoordinates_eq_zero_iff
    {k : ℝ} (hk : k ≠ 0) (n : ℕ) (p : PrimeIndex) :
    radialScalePrimeCoordinates k n p = 0 ↔
      realPrimeExponentCoordinates n p = 0 := by
  exact radialScaleCoordinates_eq_zero_iff hk _ _

/-- A nonzero radial scale cannot erase a nonzero source coordinate. -/
theorem radialScale_ne_of_source_nonzero_target_zero
    {ι : Type*} {k : ℝ} (hk : k ≠ 0)
    {v w : ι → ℝ} {i : ι}
    (hvi : v i ≠ 0) (hwi : w i = 0) :
    radialScaleCoordinates k v ≠ w := by
  intro hEq
  have hi : radialScaleCoordinates k v i = w i := congrFun hEq i
  rw [hwi] at hi
  exact hvi ((radialScaleCoordinates_eq_zero_iff hk v i).mp hi)

end DkMath.NumberTheory.StructuralArithmetic
