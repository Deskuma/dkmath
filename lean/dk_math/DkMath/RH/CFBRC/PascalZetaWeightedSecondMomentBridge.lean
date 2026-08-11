/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.PascalZetaLocalCircleChargeBridge
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.PascalZetaWeightedSecondMomentBridge"

/-!
# Weighted local contour moments and horizontal energy

The contour sums here remain sums of independent local circles.  The final
second-moment identity is an audit identity: it does not assert that its
nonnegative horizontal-energy side vanishes.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology

noncomputable def pascalZetaWeightedLocalResidueKernel
    (h : ℂ → ℂ) (ρ w : ℂ) : ℂ :=
  h w * pascalZetaLocalResidueKernel ρ w

theorem tendsto_pascalZetaWeightedLocalResidueKernel
    {h : ℂ → ℂ} {ρ : ℂ}
    (hρzero : ρ ∈ riemannZetaZeros) (hh : ContinuousAt h ρ) :
    Tendsto (pascalZetaWeightedLocalResidueKernel h ρ) (𝓝[≠] ρ)
      (𝓝 (h ρ * (-(riemannZetaZeroMultiplicity ρ : ℂ)))) := by
  exact hh.tendsto.mono_left nhdsWithin_le_nhds |>.mul
    (tendsto_pascalZetaLocalResidueKernel hρzero)

theorem circleIntegral_weight_mul_pascalZetaNegLogDeriv_eq_of_isolatingRadius
    {h : ℂ → ℂ} {ρ : ℂ}
    (hρzero : ρ ∈ riemannZetaZeros)
    {r : ℝ} (hr : IsPascalZetaIsolatingRadius ρ r)
    (hh : Differentiable ℂ h) :
    circleIntegral (fun w => h w * pascalZetaNegLogDeriv w) ρ r =
      -(2 * Real.pi * Complex.I) *
        (riemannZetaZeroMultiplicity ρ : ℂ) * h ρ := by
  have hcont : ContinuousOn (pascalZetaWeightedLocalResidueKernel h ρ)
      (Metric.closedBall ρ r \ {ρ}) := by
    intro z hz
    exact (hh z).continuousAt.continuousWithinAt.mul
      (continuousOn_pascalZetaLocalResidueKernel_of_isolatingRadius hr z hz)
  have hdiff : ∀ z ∈ Metric.ball ρ r \ {ρ},
      DifferentiableAt ℂ (pascalZetaWeightedLocalResidueKernel h ρ) z := by
    intro z hz
    exact (hh z).mul
      (differentiableAt_pascalZetaLocalResidueKernel_of_isolatingRadius hr hz)
  have hCauchy :=
    Complex.circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable_of_tendsto
      (c := ρ) (R := r) hr.1 Set.countable_empty hcont
      (fun z hz => by simpa using hdiff z ⟨hz.1.1, hz.1.2⟩)
      (tendsto_pascalZetaWeightedLocalResidueKernel hρzero (hh ρ).continuousAt)
  calc
    circleIntegral (fun w => h w * pascalZetaNegLogDeriv w) ρ r =
        circleIntegral (fun w => (w - ρ)⁻¹ •
          pascalZetaWeightedLocalResidueKernel h ρ w) ρ r := by
      rw [circleIntegral.integral_congr hr.1.le]
      intro z hz
      have hzρ : z ≠ ρ := by
        intro h
        subst z
        have : (0 : ℝ) = r := by simpa [Metric.mem_sphere] using hz
        exact hr.1.ne' this.symm
      change h z * pascalZetaNegLogDeriv z =
        (z - ρ)⁻¹ • pascalZetaWeightedLocalResidueKernel h ρ z
      rw [pascalZetaNegLogDeriv_eq_inv_mul_localResidueKernel (ρ := ρ) hzρ]
      simp [pascalZetaWeightedLocalResidueKernel, smul_eq_mul]
      ring
    _ = (2 * Real.pi * Complex.I) •
        (h ρ * (-(riemannZetaZeroMultiplicity ρ : ℂ))) := hCauchy
    _ = -(2 * Real.pi * Complex.I) *
        (riemannZetaZeroMultiplicity ρ : ℂ) * h ρ := by
      simp [smul_eq_mul]
      ring

theorem circleIntegral_weight_mul_pascalZetaNegLogDeriv_eq
    {h : ℂ → ℂ} {ρ : ℂ} (hρzero : ρ ∈ riemannZetaZeros)
    (hh : Differentiable ℂ h) :
    circleIntegral (fun w => h w * pascalZetaNegLogDeriv w)
      ρ (pascalZetaIsolatingRadius ρ) =
      -(2 * Real.pi * Complex.I) *
        (riemannZetaZeroMultiplicity ρ : ℂ) * h ρ :=
  circleIntegral_weight_mul_pascalZetaNegLogDeriv_eq_of_isolatingRadius hρzero
    (pascalZetaIsolatingRadius_spec hρzero) hh

noncomputable def pascalCriticalMirrorZeroWindowWeightedLocalContourMass
    (h : ℂ → ℂ) (R : ℝ) : ℂ :=
  ∑ ρ ∈ pascalCriticalMirrorZeroWindowFinset R,
    circleIntegral (fun w => h w * pascalZetaNegLogDeriv w)
      ρ (pascalZetaIsolatingRadius ρ)

theorem pascalCriticalMirrorZeroWindowWeightedLocalContourMass_eq
    {h : ℂ → ℂ} (hh : Differentiable ℂ h) (R : ℝ) :
    pascalCriticalMirrorZeroWindowWeightedLocalContourMass h R =
      -(2 * Real.pi * Complex.I) *
        ∑ ρ ∈ pascalCriticalMirrorZeroWindowFinset R,
          (riemannZetaZeroMultiplicity ρ : ℂ) * h ρ := by
  classical
  change (Finset.sum (pascalCriticalMirrorZeroWindowFinset R) fun ρ =>
      circleIntegral (fun w => h w * pascalZetaNegLogDeriv w)
        ρ (pascalZetaIsolatingRadius ρ)) = _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ρ hρ
  have hρzero : ρ ∈ riemannZetaZeros :=
    nontrivialRiemannZetaZero_mem_riemannZetaZeros
      ((mem_pascalCriticalMirrorZeroWindowFinset_iff.mp hρ).2)
  simpa only [mul_assoc] using
    circleIntegral_weight_mul_pascalZetaNegLogDeriv_eq hρzero hh

theorem pascalCriticalMirrorZeroWindowNormalizedWeightedLocalContourMass_eq
    {h : ℂ → ℂ} (hh : Differentiable ℂ h) (R : ℝ) :
    (2 * Real.pi * Complex.I)⁻¹ *
      pascalCriticalMirrorZeroWindowWeightedLocalContourMass h R =
      - ∑ ρ ∈ pascalCriticalMirrorZeroWindowFinset R,
          (riemannZetaZeroMultiplicity ρ : ℂ) * h ρ := by
  rw [pascalCriticalMirrorZeroWindowWeightedLocalContourMass_eq hh]
  have htwoPiI : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    apply mul_ne_zero
    · exact mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
    · exact Complex.I_ne_zero
  field_simp

noncomputable def pascalCenteredSecondWeight (s : ℂ) : ℂ :=
  (s - criticalLineCenter) ^ 2

theorem differentiable_pascalCenteredSecondWeight :
    Differentiable ℂ pascalCenteredSecondWeight := by
  unfold pascalCenteredSecondWeight
  fun_prop

noncomputable def pascalCriticalMirrorZeroWindowCenteredSecondMoment
    (R : ℝ) : ℂ :=
  ∑ ρ ∈ pascalCriticalMirrorZeroWindowFinset R,
    (riemannZetaZeroMultiplicity ρ : ℂ) * (ρ - criticalLineCenter) ^ 2

theorem pascalCriticalMirrorZeroWindowNormalizedCenteredSecondContourMass_eq
    (R : ℝ) :
    (2 * Real.pi * Complex.I)⁻¹ *
      pascalCriticalMirrorZeroWindowWeightedLocalContourMass
        pascalCenteredSecondWeight R =
      -pascalCriticalMirrorZeroWindowCenteredSecondMoment R := by
  simpa [pascalCenteredSecondWeight, pascalCriticalMirrorZeroWindowCenteredSecondMoment] using
    pascalCriticalMirrorZeroWindowNormalizedWeightedLocalContourMass_eq
      differentiable_pascalCenteredSecondWeight R

noncomputable def pascalCriticalMirrorZeroWindowHorizontalEnergy
    (R : ℝ) : ℝ :=
  ∑ ρ ∈ pascalCriticalMirrorZeroWindowFinset R,
    (riemannZetaZeroMultiplicity ρ : ℝ) * (ρ.re - (1 : ℝ) / 2) ^ 2

noncomputable def pascalCriticalMirrorZeroWindowRadialSecondMoment
    (R : ℝ) : ℝ :=
  ∑ ρ ∈ pascalCriticalMirrorZeroWindowFinset R,
    (riemannZetaZeroMultiplicity ρ : ℝ) * Complex.normSq (ρ - criticalLineCenter)

@[simp] theorem criticalLineCenter_re :
    criticalLineCenter.re = (1 : ℝ) / 2 := by
  simp [criticalLineCenter]

@[simp] theorem criticalLineCenter_im : criticalLineCenter.im = 0 := by
  simp [criticalLineCenter]

theorem two_mul_horizontalOffsetSq_eq_normSq_add_centeredSquare_re
    (z : ℂ) :
    2 * (z.re - (1 : ℝ) / 2) ^ 2 =
      Complex.normSq (z - criticalLineCenter) + ((z - criticalLineCenter) ^ 2).re := by
  rw [Complex.normSq_apply]
  simp [criticalLineCenter, pow_two, Complex.mul_re]
  ring

theorem two_mul_pascalCriticalMirrorZeroWindowHorizontalEnergy_eq
    (R : ℝ) :
    2 * pascalCriticalMirrorZeroWindowHorizontalEnergy R =
      pascalCriticalMirrorZeroWindowRadialSecondMoment R +
        (pascalCriticalMirrorZeroWindowCenteredSecondMoment R).re := by
  classical
  unfold pascalCriticalMirrorZeroWindowHorizontalEnergy
    pascalCriticalMirrorZeroWindowRadialSecondMoment
    pascalCriticalMirrorZeroWindowCenteredSecondMoment
  rw [Finset.mul_sum, Complex.re_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ρ hρ
  have hpoint := two_mul_horizontalOffsetSq_eq_normSq_add_centeredSquare_re ρ
  calc
    2 * ((riemannZetaZeroMultiplicity ρ : ℝ) * (ρ.re - 1 / 2) ^ 2) =
        (riemannZetaZeroMultiplicity ρ : ℝ) * (2 * (ρ.re - 1 / 2) ^ 2) := by ring
    _ = (riemannZetaZeroMultiplicity ρ : ℝ) *
        (Complex.normSq (ρ - criticalLineCenter) + ((ρ - criticalLineCenter) ^ 2).re) := by
      rw [hpoint]
    _ = (riemannZetaZeroMultiplicity ρ : ℝ) * Complex.normSq (ρ - criticalLineCenter) +
        (riemannZetaZeroMultiplicity ρ : ℝ) * ((ρ - criticalLineCenter) ^ 2).re := by ring
    _ = (riemannZetaZeroMultiplicity ρ : ℝ) * Complex.normSq (ρ - criticalLineCenter) +
        (((riemannZetaZeroMultiplicity ρ : ℂ) * (ρ - criticalLineCenter) ^ 2).re) := by
      simp [Complex.mul_re]

noncomputable def pascalCriticalMirrorZeroWindowNormalizedCenteredSecondContourMass
    (R : ℝ) : ℂ :=
  (2 * Real.pi * Complex.I)⁻¹ *
    pascalCriticalMirrorZeroWindowWeightedLocalContourMass pascalCenteredSecondWeight R

theorem two_mul_horizontalEnergy_eq_radialSecondMoment_sub_contour_re
    (R : ℝ) :
    2 * pascalCriticalMirrorZeroWindowHorizontalEnergy R =
      pascalCriticalMirrorZeroWindowRadialSecondMoment R -
        (pascalCriticalMirrorZeroWindowNormalizedCenteredSecondContourMass R).re := by
  rw [two_mul_pascalCriticalMirrorZeroWindowHorizontalEnergy_eq]
  have hcontour := pascalCriticalMirrorZeroWindowNormalizedCenteredSecondContourMass_eq R
  unfold pascalCriticalMirrorZeroWindowNormalizedCenteredSecondContourMass
  rw [hcontour]
  simp

theorem pascalCriticalMirrorZeroWindowHorizontalEnergy_nonneg
    (R : ℝ) :
    0 ≤ pascalCriticalMirrorZeroWindowHorizontalEnergy R := by
  unfold pascalCriticalMirrorZeroWindowHorizontalEnergy
  exact Finset.sum_nonneg fun _ _ =>
    mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)

theorem pascalCriticalMirrorZeroWindowHorizontalEnergy_eq_zero_iff
    (R : ℝ) :
    pascalCriticalMirrorZeroWindowHorizontalEnergy R = 0 ↔
      ∀ ρ ∈ pascalCriticalMirrorZeroWindowFinset R,
        ρ.re = (1 : ℝ) / 2 := by
  unfold pascalCriticalMirrorZeroWindowHorizontalEnergy
  constructor
  · intro hzero ρ hρ
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg
      (f := fun ρ : ℂ =>
        (riemannZetaZeroMultiplicity ρ : ℝ) * (ρ.re - (1 : ℝ) / 2) ^ 2)
      (s := pascalCriticalMirrorZeroWindowFinset R)
      (fun _ _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))).mp hzero ρ hρ
    have hρzero : ρ ∈ riemannZetaZeros :=
      nontrivialRiemannZetaZero_mem_riemannZetaZeros
        ((mem_pascalCriticalMirrorZeroWindowFinset_iff.mp hρ).2)
    have hmne : (riemannZetaZeroMultiplicity ρ : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt (riemannZetaZeroMultiplicity_pos hρzero)
    have hsq : (ρ.re - (1 : ℝ) / 2) ^ 2 = 0 :=
      (mul_eq_zero.mp hterm).resolve_left hmne
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsq)
  · intro hcritical
    refine (Finset.sum_eq_zero_iff_of_nonneg
      (f := fun ρ : ℂ =>
        (riemannZetaZeroMultiplicity ρ : ℝ) * (ρ.re - (1 : ℝ) / 2) ^ 2)
      (s := pascalCriticalMirrorZeroWindowFinset R)
      (fun _ _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))).mpr ?_
    intro ρ hρ
    simp [hcritical ρ hρ]

theorem pascalCriticalMirrorZeroWindowHorizontalEnergy_pos_iff
    (R : ℝ) :
    0 < pascalCriticalMirrorZeroWindowHorizontalEnergy R ↔
      ∃ ρ ∈ pascalCriticalMirrorZeroWindowFinset R,
        ρ.re ≠ (1 : ℝ) / 2 := by
  constructor
  · intro hpos
    by_contra h
    push Not at h
    have hzero := (pascalCriticalMirrorZeroWindowHorizontalEnergy_eq_zero_iff R).mpr h
    linarith
  · rintro ⟨ρ, hρ, hre⟩
    have hne : pascalCriticalMirrorZeroWindowHorizontalEnergy R ≠ 0 := by
      intro hzero
      exact hre ((pascalCriticalMirrorZeroWindowHorizontalEnergy_eq_zero_iff R).mp hzero ρ hρ)
    exact lt_of_le_of_ne (pascalCriticalMirrorZeroWindowHorizontalEnergy_nonneg R) (Ne.symm hne)

theorem pascalHorizontalEnergy_eq_zero_iff_primeMirrorWindowEnergy_eq_zero
    {n : ℕ} (hn : 1 < n) (R : ℝ) :
    pascalCriticalMirrorZeroWindowHorizontalEnergy R = 0 ↔
      pascalCriticalMirrorZeroWindowEnergy n R = 0 := by
  rw [pascalCriticalMirrorZeroWindowHorizontalEnergy_eq_zero_iff]
  symm
  exact pascalCriticalMirrorZeroWindowEnergy_eq_zero_iff hn R

/-- The finite second-moment discrepancy.  No theorem here asserts it vanishes. -/
noncomputable def pascalCriticalMirrorZeroWindowSecondMomentDefect
    (R : ℝ) : ℝ :=
  pascalCriticalMirrorZeroWindowRadialSecondMoment R -
    (pascalCriticalMirrorZeroWindowNormalizedCenteredSecondContourMass R).re

@[simp] theorem pascalCriticalMirrorZeroWindowSecondMomentDefect_eq
    (R : ℝ) :
    pascalCriticalMirrorZeroWindowSecondMomentDefect R =
      2 * pascalCriticalMirrorZeroWindowHorizontalEnergy R := by
  unfold pascalCriticalMirrorZeroWindowSecondMomentDefect
  symm
  exact two_mul_horizontalEnergy_eq_radialSecondMoment_sub_contour_re R

theorem pascalCriticalMirrorZeroWindowSecondMomentDefect_eq_zero_iff
    {n : ℕ} (hn : 1 < n) (R : ℝ) :
    pascalCriticalMirrorZeroWindowSecondMomentDefect R = 0 ↔
      pascalCriticalMirrorZeroWindowEnergy n R = 0 := by
  rw [pascalCriticalMirrorZeroWindowSecondMomentDefect_eq]
  constructor
  · intro h
    have hhorizontal : pascalCriticalMirrorZeroWindowHorizontalEnergy R = 0 := by linarith
    exact (pascalHorizontalEnergy_eq_zero_iff_primeMirrorWindowEnergy_eq_zero hn R).mp hhorizontal
  · intro h
    have hhorizontal : pascalCriticalMirrorZeroWindowHorizontalEnergy R = 0 :=
      (pascalHorizontalEnergy_eq_zero_iff_primeMirrorWindowEnergy_eq_zero hn R).mpr h
    simp [hhorizontal]

theorem pascalCriticalMirrorZeroWindowSecondMomentDefect_pos_iff
    (R : ℝ) :
    0 < pascalCriticalMirrorZeroWindowSecondMomentDefect R ↔
      ∃ ρ ∈ pascalCriticalMirrorZeroWindowFinset R,
        ρ.re ≠ (1 : ℝ) / 2 := by
  rw [pascalCriticalMirrorZeroWindowSecondMomentDefect_eq]
  constructor
  · intro h
    exact (pascalCriticalMirrorZeroWindowHorizontalEnergy_pos_iff R).mp (by linarith)
  · intro h
    have hpos := (pascalCriticalMirrorZeroWindowHorizontalEnergy_pos_iff R).mpr h
    linarith

end DkMath.RH.CFBRCProjection
