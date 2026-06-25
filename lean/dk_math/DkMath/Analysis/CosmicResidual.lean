/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Analysis.Basic

#print "file: DkMath.Analysis.CosmicResidual"

/-!
# Cosmic residual and drift

This file separates an absolute residual from a two-observation drift.

The distinction matters: zero drift only says that two residuals agree, while
zero residual says that the common value is the intended value.
-/

namespace DkMath.Analysis

/--
The output left by the quadratic unit cosmic formula before subtracting the
expected gap value.
-/
def cosmicGap {R : Type*} [CommRing R] (x u : R) : R :=
  (x + u) ^ 2 - x * (x + 2 * u)

/-- The quadratic cosmic gap is exactly the square of the gap variable. -/
theorem cosmicGap_eq_sq {R : Type*} [CommRing R] (x u : R) :
    cosmicGap x u = u ^ 2 := by
  simp [cosmicGap]
  ring

/-- Absolute error of the quadratic cosmic gap against its expected output. -/
def cosmicResidual {R : Type*} [CommRing R] (x u : R) : R :=
  cosmicGap x u - u ^ 2

/-- The exact quadratic cosmic formula has zero absolute residual. -/
theorem cosmicResidual_eq_zero {R : Type*} [CommRing R] (x u : R) :
    cosmicResidual x u = 0 := by
  rw [cosmicResidual, cosmicGap_eq_sq]
  ring

/-- Difference between residuals observed at two body coordinates. -/
def cosmicDrift {R : Type*} [CommRing R] (x y u : R) : R :=
  cosmicResidual x u - cosmicResidual y u

/-- The exact quadratic cosmic formula has zero drift between any two observations. -/
theorem cosmicDrift_eq_zero {R : Type*} [CommRing R] (x y u : R) :
    cosmicDrift x y u = 0 := by
  simp [cosmicDrift, cosmicResidual_eq_zero]

/--
Residual measured against an output carrying a fixed additive bias.

This definition demonstrates why drift and absolute residual must remain
separate: a common bias is invisible to a two-point comparison.
-/
def outputBiasResidual {R : Type*} [CommRing R] (bias x u : R) : R :=
  cosmicGap x u - (u ^ 2 + bias)

/-- A fixed output bias appears as the constant residual `-bias`. -/
theorem outputBiasResidual_eq_neg_bias
    {R : Type*} [CommRing R] (bias x u : R) :
    outputBiasResidual bias x u = -bias := by
  rw [outputBiasResidual, cosmicGap_eq_sq]
  ring

/-- A common output bias still produces zero two-point drift. -/
theorem outputBiasResidual_sub_eq_zero
    {R : Type*} [CommRing R] (bias x y u : R) :
    outputBiasResidual bias x u - outputBiasResidual bias y u = 0 := by
  rw [outputBiasResidual_eq_neg_bias, outputBiasResidual_eq_neg_bias]
  ring

/-- Quadratic gap after perturbing the beam factor by `eta`. -/
def beamPerturbedGap {R : Type*} [CommRing R] (eta x u : R) : R :=
  (x + u) ^ 2 - x * (x + 2 * u + eta)

/-- Beam perturbation changes the ideal square gap by the linear term `eta * x`. -/
theorem beamPerturbedGap_eq
    {R : Type*} [CommRing R] (eta x u : R) :
    beamPerturbedGap eta x u = u ^ 2 - eta * x := by
  simp [beamPerturbedGap]
  ring

end DkMath.Analysis
