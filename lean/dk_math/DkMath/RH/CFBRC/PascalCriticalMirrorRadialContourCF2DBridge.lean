/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.PascalZetaWeightedSecondMomentBridge
import DkMath.CosmicFormula.Rotation.CF2D.ThreeElementBridge
import DkMath.RH.CFBRC.CriticalMirrorGeometry
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.PascalCriticalMirrorRadialContourCF2DBridge"

/-!
# Mirror-frozen radial contour charges and CF2D `q2`

The weight `pascalMirrorFrozenRadialWeight ρ` is holomorphic in its circle
variable but depends on the particular zero `ρ`.  Consequently, the finite
sum below is a sum of independent local contours, not a single fixed-weight
outer contour integral.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology

@[simp] theorem centeredComplex_eq_sub_criticalLineCenter
    (s : ℂ) : centeredComplex s = s - criticalLineCenter := by
  apply Complex.ext <;> simp [centeredComplex, criticalLineCenter]

theorem centeredComplex_criticalMirror_eq_neg_conj
    (s : ℂ) :
    centeredComplex (criticalMirror s) = -star (centeredComplex s) := by
  apply Complex.ext
  · simp [centeredComplex, criticalMirror]
    ring
  · simp [centeredComplex, criticalMirror]

theorem centeredComplex_mul_criticalMirror_eq_neg_normSq
    (s : ℂ) :
    centeredComplex s * centeredComplex (criticalMirror s) =
      -(Complex.normSq (centeredComplex s) : ℂ) := by
  apply Complex.ext <;>
    simp [centeredComplex, criticalMirror, Complex.normSq] <;>
    ring

theorem sub_center_mul_criticalMirror_sub_center_eq_neg_normSq
    (s : ℂ) :
    (s - criticalLineCenter) * (criticalMirror s - criticalLineCenter) =
      -(Complex.normSq (s - criticalLineCenter) : ℂ) := by
  rw [← centeredComplex_eq_sub_criticalLineCenter,
    ← centeredComplex_eq_sub_criticalLineCenter]
  exact centeredComplex_mul_criticalMirror_eq_neg_normSq s

noncomputable def pascalMirrorFrozenRadialWeight (ρ w : ℂ) : ℂ :=
  (w - criticalLineCenter) * (criticalMirror ρ - criticalLineCenter)

theorem differentiable_pascalMirrorFrozenRadialWeight
    (ρ : ℂ) : Differentiable ℂ (pascalMirrorFrozenRadialWeight ρ) := by
  unfold pascalMirrorFrozenRadialWeight
  fun_prop

@[simp] theorem pascalMirrorFrozenRadialWeight_self
    (ρ : ℂ) :
    pascalMirrorFrozenRadialWeight ρ ρ =
      -(Complex.normSq (ρ - criticalLineCenter) : ℂ) := by
  exact sub_center_mul_criticalMirror_sub_center_eq_neg_normSq ρ

noncomputable def pascalZetaNormalizedMirrorFrozenRadialLocalCharge
    (ρ : ℂ) : ℂ :=
  (2 * Real.pi * Complex.I)⁻¹ *
    circleIntegral
      (fun w => pascalMirrorFrozenRadialWeight ρ w * pascalZetaNegLogDeriv w)
      ρ (pascalZetaIsolatingRadius ρ)

@[simp] theorem pascalZetaNormalizedMirrorFrozenRadialLocalCharge_eq
    {ρ : ℂ} (hρ : ρ ∈ riemannZetaZeros) :
    pascalZetaNormalizedMirrorFrozenRadialLocalCharge ρ =
      (riemannZetaZeroMultiplicity ρ : ℂ) *
        (Complex.normSq (ρ - criticalLineCenter) : ℂ) := by
  rw [pascalZetaNormalizedMirrorFrozenRadialLocalCharge,
    circleIntegral_weight_mul_pascalZetaNegLogDeriv_eq hρ
      (differentiable_pascalMirrorFrozenRadialWeight ρ),
    pascalMirrorFrozenRadialWeight_self]
  have htwoPiI : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    apply mul_ne_zero
    · exact mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
    · exact Complex.I_ne_zero
  field_simp

noncomputable def pascalCriticalMirrorZeroWindowNormalizedMirrorFrozenRadialContourMass
    (R : ℝ) : ℂ :=
  ∑ ρ ∈ pascalCriticalMirrorZeroWindowFinset R,
    pascalZetaNormalizedMirrorFrozenRadialLocalCharge ρ

theorem pascalCriticalMirrorZeroWindowNormalizedMirrorFrozenRadialContourMass_eq
    (R : ℝ) :
    pascalCriticalMirrorZeroWindowNormalizedMirrorFrozenRadialContourMass R =
      (pascalCriticalMirrorZeroWindowRadialSecondMoment R : ℂ) := by
  classical
  change Finset.sum (pascalCriticalMirrorZeroWindowFinset R)
      pascalZetaNormalizedMirrorFrozenRadialLocalCharge = _
  unfold pascalCriticalMirrorZeroWindowRadialSecondMoment
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro ρ hρ
  have hρzero : ρ ∈ riemannZetaZeros :=
    nontrivialRiemannZetaZero_mem_riemannZetaZeros
      ((mem_pascalCriticalMirrorZeroWindowFinset_iff.mp hρ).2)
  simpa using pascalZetaNormalizedMirrorFrozenRadialLocalCharge_eq hρzero

noncomputable def pascalCenteredZeroCF2DState
    (s : ℂ) : DkMath.CosmicFormula.Rotation.CF2D.Vec ℝ :=
  ⟨s.re - (1 : ℝ) / 2, s.im⟩

@[simp] theorem pascalCenteredZeroCF2DState_q2_eq_normSq
    (s : ℂ) :
    DkMath.CosmicFormula.Rotation.CF2D.Vec.q2 (pascalCenteredZeroCF2DState s) =
      Complex.normSq (s - criticalLineCenter) := by
  simp [pascalCenteredZeroCF2DState,
    DkMath.CosmicFormula.Rotation.CF2D.Vec.q2, Complex.normSq, criticalLineCenter]
  ring

@[simp] theorem pascalCenteredZeroCF2DState_q2_criticalMirror
    (s : ℂ) :
    DkMath.CosmicFormula.Rotation.CF2D.Vec.q2
      (pascalCenteredZeroCF2DState (criticalMirror s)) =
      DkMath.CosmicFormula.Rotation.CF2D.Vec.q2 (pascalCenteredZeroCF2DState s) := by
  rw [pascalCenteredZeroCF2DState_q2_eq_normSq,
    pascalCenteredZeroCF2DState_q2_eq_normSq]
  rw [← centeredComplex_eq_sub_criticalLineCenter,
    ← centeredComplex_eq_sub_criticalLineCenter,
    centeredComplex_criticalMirror_eq_neg_conj]
  simp [Complex.normSq]
  ring

noncomputable def pascalCriticalMirrorZeroWindowCF2DRadialMass
    (R : ℝ) : ℝ :=
  ∑ ρ ∈ pascalCriticalMirrorZeroWindowFinset R,
    (riemannZetaZeroMultiplicity ρ : ℝ) *
      DkMath.CosmicFormula.Rotation.CF2D.Vec.q2 (pascalCenteredZeroCF2DState ρ)

@[simp] theorem pascalCriticalMirrorZeroWindowCF2DRadialMass_eq
    (R : ℝ) :
    pascalCriticalMirrorZeroWindowCF2DRadialMass R =
      pascalCriticalMirrorZeroWindowRadialSecondMoment R := by
  unfold pascalCriticalMirrorZeroWindowCF2DRadialMass
    pascalCriticalMirrorZeroWindowRadialSecondMoment
  apply Finset.sum_congr rfl
  intro ρ hρ
  rw [pascalCenteredZeroCF2DState_q2_eq_normSq]

theorem pascalNormalizedMirrorFrozenRadialContourMass_eq_CF2DRadialMass
    (R : ℝ) :
    pascalCriticalMirrorZeroWindowNormalizedMirrorFrozenRadialContourMass R =
      (pascalCriticalMirrorZeroWindowCF2DRadialMass R : ℂ) := by
  rw [pascalCriticalMirrorZeroWindowNormalizedMirrorFrozenRadialContourMass_eq,
    pascalCriticalMirrorZeroWindowCF2DRadialMass_eq]

theorem pascalSecondMomentDefect_eq_mirrorFrozenContour_sub_centeredContour_re
    (R : ℝ) :
    pascalCriticalMirrorZeroWindowSecondMomentDefect R =
      (pascalCriticalMirrorZeroWindowNormalizedMirrorFrozenRadialContourMass R).re -
        (pascalCriticalMirrorZeroWindowNormalizedCenteredSecondContourMass R).re := by
  unfold pascalCriticalMirrorZeroWindowSecondMomentDefect
  rw [pascalCriticalMirrorZeroWindowNormalizedMirrorFrozenRadialContourMass_eq]
  simp

theorem pascalMirrorFrozenContourDifference_eq_two_horizontalEnergy
    (R : ℝ) :
    (pascalCriticalMirrorZeroWindowNormalizedMirrorFrozenRadialContourMass R).re -
        (pascalCriticalMirrorZeroWindowNormalizedCenteredSecondContourMass R).re =
      2 * pascalCriticalMirrorZeroWindowHorizontalEnergy R := by
  rw [← pascalSecondMomentDefect_eq_mirrorFrozenContour_sub_centeredContour_re,
    pascalCriticalMirrorZeroWindowSecondMomentDefect_eq]

end DkMath.RH.CFBRCProjection
