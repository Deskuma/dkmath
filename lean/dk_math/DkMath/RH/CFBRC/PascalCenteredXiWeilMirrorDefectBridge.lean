/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.PascalCenteredXiFixedSecondMomentDefectBridge
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.PascalCenteredXiWeilMirrorDefectBridge"

/-!
# Finite centered-Xi Weil-style mirror defect bridge

This module fixes a finite, zero-window version of the critical-mirror
quadratic structure.  The pairing here is deliberately called *Weil-style*:
it is a finite algebraic pairing on the existing Pascal zero window, not the
classical Weil criterion, a Li-coefficient identity, or a Guinand--Weil
explicit formula.

The bridge gives three exact representations of the same scalar defect on a
boundary-safe radius:

* radial diagonal mass minus the real part of the finite mirror pairing;
* the fixed centered-Xi second-moment defect;
* half of the weighted anti-mirror difference norm, equivalently twice the
  existing horizontal energy.

No Riemann hypothesis, mirror reindexing, infinite sum, admissible test
function, or defect-vanishing assertion is used here.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open scoped BigOperators

/-! ## Phase A: centered mirror algebra -/

/-
`centeredComplex_eq_sub_criticalLineCenter` and
`centeredComplex_criticalMirror_eq_neg_conj` are imported from the existing
CF2D/radial bridge.  The two lemmas below expose the exact forms needed by
the finite pairing and its anti-mirror energy.
-/

/-- The centered mirror pairing term is the negative centered square. -/
theorem centeredMirrorPairTerm_eq_neg_sq (s : ℂ) :
    centeredComplex s *
        (starRingEnd ℂ) (centeredComplex (criticalMirror s)) =
      -(centeredComplex s) ^ 2 := by
  rw [centeredComplex_criticalMirror_eq_neg_conj]
  simp
  ring

/-- The centered anti-mirror difference has twice the horizontal coordinate. -/
theorem centeredComplex_sub_criticalMirror_eq_two_horizontal (s : ℂ) :
    centeredComplex s - centeredComplex (criticalMirror s) =
      ⟨2 * (s.re - (1 : ℝ) / 2), 0⟩ := by
  apply Complex.ext
  · simp [centeredComplex, criticalMirror]
    ring
  · simp [centeredComplex, criticalMirror]

/--
Half the squared norm of the centered anti-mirror difference is the doubled
horizontal displacement.  This is a pointwise complex-algebra identity and
does not use that `s` is a zeta zero or that it lies on the critical line.
-/
theorem half_normSq_centeredComplex_sub_criticalMirror_eq (s : ℂ) :
    (1 : ℝ) / 2 *
        Complex.normSq
          (centeredComplex s - centeredComplex (criticalMirror s)) =
      2 * (s.re - (1 : ℝ) / 2) ^ 2 := by
  rw [centeredComplex_sub_criticalMirror_eq_two_horizontal]
  simp [Complex.normSq_apply]
  ring

/-! ## Phase B: finite Weil-style mirror pairing -/

/--
The finite Weil-style critical-mirror pairing on the existing zero window.

The multiplicity and the window are exactly those used by the PPW centered
second moment.  This is a finite pairing only; it is not identified here
with the classical infinite Weil quadratic form.
-/
noncomputable def pascalCriticalMirrorZeroWindowFiniteWeilMirrorPair
    (R : ℝ) : ℂ :=
  ∑ ρ ∈ pascalCriticalMirrorZeroWindowFinset R,
    (riemannZetaZeroMultiplicity ρ : ℂ) *
      centeredComplex ρ *
        (starRingEnd ℂ) (centeredComplex (criticalMirror ρ))

/-- The finite Weil-style mirror pairing is the negative centered second moment. -/
theorem pascalCriticalMirrorZeroWindowFiniteWeilMirrorPair_eq_neg_centeredSecondMoment
    (R : ℝ) :
    pascalCriticalMirrorZeroWindowFiniteWeilMirrorPair R =
      -pascalCriticalMirrorZeroWindowCenteredSecondMoment R := by
  classical
  unfold pascalCriticalMirrorZeroWindowFiniteWeilMirrorPair
  unfold pascalCriticalMirrorZeroWindowCenteredSecondMoment
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro ρ hρ
  rw [mul_assoc, centeredMirrorPairTerm_eq_neg_sq,
    centeredComplex_eq_sub_criticalLineCenter]
  ring

/-! ## Phase C: fixed centered-Xi holomorphic observable -/

/--
On a boundary-safe radius, the fixed centered-Xi holomorphic second contour
is exactly the finite Weil-style mirror pairing.  The proof only composes the
existing contour theorem with the finite pairing identity.
-/
theorem pascalCenteredXiFixedHolomorphicSecondContourFunctional_eq_finiteWeilMirrorPair
    {R : ℝ} (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    pascalCenteredXiFixedHolomorphicSecondContourFunctional R =
      pascalCriticalMirrorZeroWindowFiniteWeilMirrorPair R := by
  rw [pascalCenteredXiFixedHolomorphicSecondContourFunctional_eq hR,
    pascalCriticalMirrorZeroWindowFiniteWeilMirrorPair_eq_neg_centeredSecondMoment]

/-! ## Phase D: radial mass minus mirror pairing -/

/--
The fixed Xi defect is the radial diagonal mass minus the real part of the
finite Weil-style mirror pairing on every boundary-safe radius.
-/
theorem pascalCenteredXiFixedSecondMomentDefectFunctional_eq_radial_sub_finiteWeilMirrorPair_re
    {R : ℝ} (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    pascalCenteredXiFixedSecondMomentDefectFunctional R =
      pascalCriticalMirrorZeroWindowRadialSecondMoment R -
        (pascalCriticalMirrorZeroWindowFiniteWeilMirrorPair R).re := by
  unfold pascalCenteredXiFixedSecondMomentDefectFunctional
  rw [pascalCenteredXiFixedRadialSecondMomentFunctional_eq_windowRadial hR,
    pascalCenteredXiFixedHolomorphicSecondContourFunctional_eq_finiteWeilMirrorPair hR]

/-! ## Phase E: anti-mirror difference energy -/

/--
The finite anti-mirror difference energy.  It is a real-valued norm-square
functional on the existing finite zero window; no critical-line assumption
is built into its definition.
-/
noncomputable def pascalCriticalMirrorZeroWindowAntiMirrorEnergy
    (R : ℝ) : ℝ :=
  (1 : ℝ) / 2 *
    ∑ ρ ∈ pascalCriticalMirrorZeroWindowFinset R,
      (riemannZetaZeroMultiplicity ρ : ℝ) *
        Complex.normSq
          (centeredComplex ρ - centeredComplex (criticalMirror ρ))

/-- The anti-mirror difference energy is twice the existing horizontal energy. -/
theorem pascalCriticalMirrorZeroWindowAntiMirrorEnergy_eq_two_mul_horizontalEnergy
    (R : ℝ) :
    pascalCriticalMirrorZeroWindowAntiMirrorEnergy R =
      2 * pascalCriticalMirrorZeroWindowHorizontalEnergy R := by
  classical
  unfold pascalCriticalMirrorZeroWindowAntiMirrorEnergy
  rw [Finset.mul_sum]
  unfold pascalCriticalMirrorZeroWindowHorizontalEnergy
  conv_rhs => rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ρ hρ
  calc
    (1 : ℝ) / 2 *
          ((riemannZetaZeroMultiplicity ρ : ℝ) *
            Complex.normSq
              (centeredComplex ρ - centeredComplex (criticalMirror ρ))) =
        (riemannZetaZeroMultiplicity ρ : ℝ) *
          ((1 : ℝ) / 2 *
            Complex.normSq
              (centeredComplex ρ - centeredComplex (criticalMirror ρ))) := by
      ring
    _ = (riemannZetaZeroMultiplicity ρ : ℝ) *
          (2 * (ρ.re - (1 : ℝ) / 2) ^ 2) := by
      rw [half_normSq_centeredComplex_sub_criticalMirror_eq]
    _ = 2 * ((riemannZetaZeroMultiplicity ρ : ℝ) *
          (ρ.re - (1 : ℝ) / 2) ^ 2) := by
      ring

/--
On a boundary-safe radius, the fixed centered-Xi defect is exactly the
anti-mirror difference energy.  This is a representation identity, not a
vanishing theorem and not a proof of the Riemann hypothesis.
-/
theorem pascalCenteredXiFixedSecondMomentDefectFunctional_eq_antiMirrorEnergy
    {R : ℝ} (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    pascalCenteredXiFixedSecondMomentDefectFunctional R =
      pascalCriticalMirrorZeroWindowAntiMirrorEnergy R := by
  rw [pascalCenteredXiFixedSecondMomentDefectFunctional_eq_two_mul_horizontalEnergy hR,
    pascalCriticalMirrorZeroWindowAntiMirrorEnergy_eq_two_mul_horizontalEnergy]

end DkMath.RH.CFBRCProjection
