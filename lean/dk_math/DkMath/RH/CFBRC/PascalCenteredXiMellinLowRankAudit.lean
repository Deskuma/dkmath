/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.PascalCenteredXiMellinFiniteJetRankAudit
import DkMath.RH.CFBRC.StandardZetaRealAxisClosure
import DkMath.RH.CFBRC.PascalCenteredXiGlobalZeroDiskBridge
import Mathlib.Tactic

/-!
# Actual-window q-zero discharge and low Mellin-jet rank

This module separates the bare Mellin null coordinate, the unconditional
actual centered-Xi zero exclusion, and the exact two- and three-orbit jet
certificates.  The conclusions concern jet coefficient vectors only; they do
not provide finite nonzero-`τ` evaluation separation or an independent
off-critical witness.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

/-! ## GWSS-001M-B0: discharge of the actual zero coordinate -/

/-- A centered Xi zero in a finite disk is nonzero.

The proof uses the unconditional nonrealness of every nontrivial zeta zero;
no RH or critical-line assumption is used. -/
theorem pascalCenteredXiZeroDiskFinset_ne_zero
    {R : ℝ} {z : ℂ}
    (hz : z ∈ pascalCenteredXiZeroDiskFinset R) :
    z ≠ 0 := by
  have hzero : z ∈ pascalCenteredXiZeros :=
    (mem_pascalCenteredXiZeroDiskFinset_iff.mp hz).2
  have hnontriv : NontrivialRiemannZetaZero (criticalLineCenter + z) :=
    (mem_pascalCenteredXiZeros_iff_nontrivial_shift z).mp hzero
  have him : (criticalLineCenter + z).im ≠ 0 :=
    nontrivialRiemannZetaZero_im_ne_zero hnontriv
  intro hz0
  apply him
  rw [hz0]
  simp [criticalLineCenter]

/-- The squared coordinate of an actual centered Xi zero is nonzero. -/
theorem pascalCenteredXiZeroDiskFinset_sq_ne_zero
    {R : ℝ} {z : ℂ}
    (hz : z ∈ pascalCenteredXiZeroDiskFinset R) :
    z ^ 2 ≠ 0 := by
  exact pow_ne_zero 2 (pascalCenteredXiZeroDiskFinset_ne_zero hz)

/-! ## GWSS-001M-B1: exact two-orbit jet certificate -/

/-- The two-orbit determinant of the quadratic and quartic jet rows factors
exactly as the expected product of the two squared coordinates and their
difference. -/
theorem twoOrbitMellinJetDeterminant_eq
    (q₁ q₂ : ℂ) :
    q₁ * (q₂ ^ 2 / 12) - q₂ * (q₁ ^ 2 / 12) =
      q₁ * q₂ * (q₂ - q₁) / 12 := by
  ring

/-- The two-orbit jet determinant is nonzero for distinct nonzero squared
coordinates. -/
theorem twoOrbitMellinJetDeterminant_ne_zero
    {q₁ q₂ : ℂ}
    (hq₁ : q₁ ≠ 0) (hq₂ : q₂ ≠ 0) (hneq : q₁ ≠ q₂) :
    q₁ * (q₂ ^ 2 / 12) - q₂ * (q₁ ^ 2 / 12) ≠ 0 := by
  rw [twoOrbitMellinJetDeterminant_eq]
  apply div_ne_zero
  · exact mul_ne_zero (mul_ne_zero hq₁ hq₂)
      (sub_ne_zero.mpr hneq.symm)
  · norm_num

/-- Actual Xi-window corollary of the two-orbit jet certificate.  The
hypothesis distinguishes squared orbits, rather than the points themselves. -/
theorem two_pascalCenteredXiZeroDiskFinset_mellinJetDeterminant_ne_zero
    {R : ℝ} {z₁ z₂ : ℂ}
    (hz₁ : z₁ ∈ pascalCenteredXiZeroDiskFinset R)
    (hz₂ : z₂ ∈ pascalCenteredXiZeroDiskFinset R)
    (hsq : z₁ ^ 2 ≠ z₂ ^ 2) :
    z₁ ^ 2 * ((z₂ ^ 2) ^ 2 / 12) -
        z₂ ^ 2 * ((z₁ ^ 2) ^ 2 / 12) ≠ 0 := by
  exact twoOrbitMellinJetDeterminant_ne_zero
    (pascalCenteredXiZeroDiskFinset_sq_ne_zero hz₁)
    (pascalCenteredXiZeroDiskFinset_sq_ne_zero hz₂) hsq

/-! ## GWSS-001M-B2: exact three-orbit jet certificate -/

/-- The direct 3-by-3 expansion of the first three even Mellin jets has the
Vandermonde factorization, with exact jet normalizations `12` and `360`.
This is deliberately a fixed low-rank identity, not a general determinant
framework. -/
theorem threeOrbitMellinJetDeterminant_eq
    (q₁ q₂ q₃ : ℂ) :
    q₁ * ((q₂ ^ 2 / 12) * (q₃ ^ 3 / 360) -
        (q₃ ^ 2 / 12) * (q₂ ^ 3 / 360)) -
      q₂ * ((q₁ ^ 2 / 12) * (q₃ ^ 3 / 360) -
        (q₃ ^ 2 / 12) * (q₁ ^ 3 / 360)) +
      q₃ * ((q₁ ^ 2 / 12) * (q₂ ^ 3 / 360) -
        (q₂ ^ 2 / 12) * (q₁ ^ 3 / 360)) =
      q₁ * q₂ * q₃ * (q₂ - q₁) * (q₃ - q₁) * (q₃ - q₂) /
        (12 * 360) := by
  ring

/-- The three-orbit jet determinant is nonzero for three distinct nonzero
squared coordinates. -/
theorem threeOrbitMellinJetDeterminant_ne_zero
    {q₁ q₂ q₃ : ℂ}
    (hq₁ : q₁ ≠ 0) (hq₂ : q₂ ≠ 0) (hq₃ : q₃ ≠ 0)
    (h₁₂ : q₁ ≠ q₂) (h₁₃ : q₁ ≠ q₃) (h₂₃ : q₂ ≠ q₃) :
    q₁ * ((q₂ ^ 2 / 12) * (q₃ ^ 3 / 360) -
        (q₃ ^ 2 / 12) * (q₂ ^ 3 / 360)) -
      q₂ * ((q₁ ^ 2 / 12) * (q₃ ^ 3 / 360) -
        (q₃ ^ 2 / 12) * (q₁ ^ 3 / 360)) +
      q₃ * ((q₁ ^ 2 / 12) * (q₂ ^ 3 / 360) -
        (q₂ ^ 2 / 12) * (q₁ ^ 3 / 360)) ≠ 0 := by
  rw [threeOrbitMellinJetDeterminant_eq]
  apply div_ne_zero
  · have hs₁₂ : q₂ - q₁ ≠ 0 := sub_ne_zero.mpr h₁₂.symm
    have hs₁₃ : q₃ - q₁ ≠ 0 := sub_ne_zero.mpr h₁₃.symm
    have hs₂₃ : q₃ - q₂ ≠ 0 := sub_ne_zero.mpr h₂₃.symm
    apply mul_ne_zero
    · apply mul_ne_zero
      · apply mul_ne_zero
        · apply mul_ne_zero
          · exact mul_ne_zero hq₁ hq₂
          · exact hq₃
        · exact hs₁₂
      · exact hs₁₃
    · exact hs₂₃
  · norm_num

/-- Actual Xi-window corollary of the three-orbit jet certificate. -/
theorem three_pascalCenteredXiZeroDiskFinset_mellinJetDeterminant_ne_zero
    {R : ℝ} {z₁ z₂ z₃ : ℂ}
    (hz₁ : z₁ ∈ pascalCenteredXiZeroDiskFinset R)
    (hz₂ : z₂ ∈ pascalCenteredXiZeroDiskFinset R)
    (hz₃ : z₃ ∈ pascalCenteredXiZeroDiskFinset R)
    (h₁₂ : z₁ ^ 2 ≠ z₂ ^ 2)
    (h₁₃ : z₁ ^ 2 ≠ z₃ ^ 2)
    (h₂₃ : z₂ ^ 2 ≠ z₃ ^ 2) :
    z₁ ^ 2 * (((z₂ ^ 2) ^ 2 / 12) * ((z₃ ^ 2) ^ 3 / 360) -
        ((z₃ ^ 2) ^ 2 / 12) * ((z₂ ^ 2) ^ 3 / 360)) -
      z₂ ^ 2 * (((z₁ ^ 2) ^ 2 / 12) * ((z₃ ^ 2) ^ 3 / 360) -
        ((z₃ ^ 2) ^ 2 / 12) * ((z₁ ^ 2) ^ 3 / 360)) +
      z₃ ^ 2 * (((z₁ ^ 2) ^ 2 / 12) * ((z₂ ^ 2) ^ 3 / 360) -
        ((z₂ ^ 2) ^ 2 / 12) * ((z₁ ^ 2) ^ 3 / 360)) ≠ 0 := by
  exact threeOrbitMellinJetDeterminant_ne_zero
    (pascalCenteredXiZeroDiskFinset_sq_ne_zero hz₁)
    (pascalCenteredXiZeroDiskFinset_sq_ne_zero hz₂)
    (pascalCenteredXiZeroDiskFinset_sq_ne_zero hz₃)
    h₁₂ h₁₃ h₂₃

end DkMath.RH.CFBRCProjection
