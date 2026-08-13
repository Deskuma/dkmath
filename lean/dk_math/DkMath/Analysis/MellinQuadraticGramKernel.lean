/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Analysis.MellinMultiplicativeApproxIdentity
import Mathlib.Tactic

/-!
# A fixed-ε quadratic Gram-kernel candidate

This module records the positive finite-family energy suggested by the
logarithmic average for the centered Mellin box.  It is deliberately kept
separate from the one-variable second-difference weight: the Gram diagonal
has argument `z + conj z`, while the latter has argument `z`.

Only fixed-ε identities are asserted here.  No limit, contour exchange,
finite-cutoff conjugate provider, or implication from Gram positivity to the
prime-side excess is supplied.
-/

namespace DkMath.Analysis

open MeasureTheory
open scoped Interval Topology

/-- The centered Mellin logarithmic multiplier at a fixed box width. -/
noncomputable def mellinQuadraticBoxMultiplier (ε : ℝ) (z : ℂ) : ℂ :=
  centeredMellinSpectralWeight (centeredMellinBoxApprox ε) z

/-- The current one-variable quadratic weight, retained as a separate surface. -/
noncomputable def mellinQuadraticBoxWeight (ε : ℝ) (z : ℂ) : ℂ :=
  z ^ 2 * mellinQuadraticBoxMultiplier ε z

/-- The Hermitian Gram-kernel candidate suggested by the logarithmic average. -/
noncomputable def mellinQuadraticBoxGramKernel (ε : ℝ) (z w : ℂ) : ℂ :=
  z * starRingEnd ℂ w *
    mellinQuadraticBoxMultiplier ε (z + starRingEnd ℂ w)

theorem mellinQuadraticBoxMultiplier_eq_logAverage
    {ε : ℝ} (hε : 0 < ε) (z : ℂ) :
    mellinQuadraticBoxMultiplier ε z =
      ((2 * ε : ℝ)⁻¹ : ℂ) *
        (∫ t in (-ε)..ε, Complex.exp ((t : ℂ) * z)) := by
  exact centeredMellinSpectralWeight_centeredMellinBoxApprox_eq_logAverage hε z

theorem mellinQuadraticBoxGramKernel_eq_logAverage_integral
    {ε : ℝ} (hε : 0 < ε) (z w : ℂ) :
    mellinQuadraticBoxGramKernel ε z w =
      z * starRingEnd ℂ w *
        (((2 * ε : ℝ)⁻¹ : ℂ) *
          (∫ t in (-ε)..ε,
            Complex.exp ((t : ℂ) * (z + starRingEnd ℂ w)))) := by
  unfold mellinQuadraticBoxGramKernel
  rw [mellinQuadraticBoxMultiplier_eq_logAverage hε]

theorem mellinQuadraticBoxWeight_eq_quadratic_mul_multiplier
    (ε : ℝ) (z : ℂ) :
    mellinQuadraticBoxWeight ε z = z ^ 2 * mellinQuadraticBoxMultiplier ε z := by
  rfl

theorem mellinQuadraticBoxGramKernel_diagonal
    (ε : ℝ) (z : ℂ) :
    mellinQuadraticBoxGramKernel ε z z =
      (Complex.normSq z : ℂ) *
        mellinQuadraticBoxMultiplier ε (z + starRingEnd ℂ z) := by
  unfold mellinQuadraticBoxGramKernel
  rw [Complex.mul_conj]

/-- The finite-family Gram energy obtained directly from the exponential
feature map `z ↦ z * exp (t z)`. -/
noncomputable def mellinQuadraticBoxGramEnergy
    {n : ℕ} (ε : ℝ) (z : Fin n → ℂ) (c : Fin n → ℂ) : ℝ :=
  (2 * ε)⁻¹ *
    ∫ t in (-ε)..ε,
      Complex.normSq (∑ j, c j * (z j * Complex.exp ((t : ℂ) * z j)))

theorem mellinQuadraticBoxGramEnergy_nonneg
    {n : ℕ} {ε : ℝ} (hε : 0 < ε) (z : Fin n → ℂ) (c : Fin n → ℂ) :
    0 ≤ mellinQuadraticBoxGramEnergy ε z c := by
  unfold mellinQuadraticBoxGramEnergy
  have hscale : 0 ≤ (2 * ε)⁻¹ := by positivity
  have hinterval : -ε ≤ ε := by linarith
  have hmass :
      0 ≤ ∫ t in (-ε)..ε,
        Complex.normSq (∑ j, c j * (z j * Complex.exp ((t : ℂ) * z j))) := by
    apply intervalIntegral.integral_nonneg_of_ae hinterval
    exact Filter.Eventually.of_forall (fun t => Complex.normSq_nonneg _)
  exact mul_nonneg hscale hmass

end DkMath.Analysis
