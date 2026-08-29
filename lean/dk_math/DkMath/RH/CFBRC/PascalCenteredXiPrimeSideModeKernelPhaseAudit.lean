/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideFiniteTailProjectionAudit
import Mathlib.Tactic

/-!
# CS13: source-derived phase kernel audit

This module exposes the centered right-edge coordinate and the oscillatory
phase of one finite natural mode.  All statements remain finite and
source-derived.  In particular, no sign is inferred from `Λ n ≥ 0`, no
infinite tail is exchanged with an integral, and no RH conclusion is added.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.Analysis
open MeasureTheory
open scoped Interval Topology

/-! ## CS13-A: centered right-edge coordinate -/

/-- The centered node attached to the finite right-edge height `t`. -/
noncomputable def pascalCenteredXiPrimeSideModePhaseNode
    (W : PascalCenteredXiResidueTransportWindow) (t : ℝ) : ℂ :=
  pascalOrdinaryToCentered
    (pascalSymmetricRectangleRightEdge W.rectangle.σ t)

theorem pascalCenteredXiPrimeSideModePhaseNode_eq_affine
    (W : PascalCenteredXiResidueTransportWindow) (t : ℝ) :
    pascalCenteredXiPrimeSideModePhaseNode W t =
      ((W.rectangle.σ - (1 / 2 : ℝ) : ℝ) : ℂ) +
        (t : ℂ) * Complex.I := by
  simp [pascalCenteredXiPrimeSideModePhaseNode,
    pascalOrdinaryToCentered, pascalSymmetricRectangleRightEdge,
    criticalLineCenter]
  ring

/-! ## CS13-B: quadratic box boundary reduction -/

private theorem intervalIntegral_exp_mul_complex_eq_boundary
    {ε : ℝ} (z : ℂ) :
    (∫ t in (-ε)..ε, Complex.exp ((t : ℂ) * z)) =
      if z = 0 then (2 * ε : ℂ) else
        z⁻¹ * (Complex.exp ((ε : ℂ) * z) -
          Complex.exp ((-ε : ℂ) * z)) := by
  by_cases hz : z = 0
  · subst z
    norm_num
    ring
  · have hcont : ContinuousOn
        (fun t : ℝ => z⁻¹ * Complex.exp ((t : ℂ) * z))
        (Set.uIcc (-ε) ε) := by
      fun_prop
    have hderiv : ∀ x ∈ Set.Ioo (min (-ε) ε) (max (-ε) ε),
        HasDerivWithinAt
          (fun t : ℝ => z⁻¹ * Complex.exp ((t : ℂ) * z))
          (Complex.exp ((x : ℂ) * z)) (Set.Ioi x) x := by
      intro x hx
      have harg : HasDerivAt (fun y : ℝ => (y : ℂ) * z) z x := by
        simpa using
          (((hasDerivAt_id (x : ℂ)).mul_const z).comp_ofReal)
      have hexp : HasDerivAt
          (fun y : ℝ => Complex.exp ((y : ℂ) * z))
          (Complex.exp ((x : ℂ) * z) * z) x := by
        exact (Complex.hasDerivAt_exp ((x : ℂ) * z)).comp x harg
      have hprimitive : HasDerivWithinAt
          (fun t : ℝ => z⁻¹ * Complex.exp ((t : ℂ) * z))
          (z⁻¹ * (Complex.exp ((x : ℂ) * z) * z))
          (Set.Ioi x) x :=
        (hexp.const_mul z⁻¹).hasDerivWithinAt
      convert hprimitive using 1; field_simp [hz]
    have hint : IntervalIntegrable
        (fun t : ℝ => Complex.exp ((t : ℂ) * z))
        volume (-ε) ε := by
      have hc : Continuous (fun t : ℝ =>
          Complex.exp ((t : ℂ) * z)) := by
        fun_prop
      exact hc.intervalIntegrable (μ := volume) (-ε) ε
    have hfund := intervalIntegral.integral_eq_sub_of_hasDeriv_right
      hcont hderiv hint
    have hscale :
        (∫ t in (-ε)..ε, Complex.exp ((t : ℂ) * z)) =
          (z⁻¹ * Complex.exp ((ε : ℂ) * z)) -
            (z⁻¹ * Complex.exp ((-ε : ℂ) * z)) := by
      simpa using hfund
    rw [ite_eq_right hz, hscale]
    ring

theorem mellinQuadraticBoxWeight_eq_boundaryDifference
    {ε : ℝ} (hε : 0 < ε) (z : ℂ) :
    mellinQuadraticBoxWeight ε z =
      ((2 * ε : ℝ)⁻¹ : ℂ) * z *
        (Complex.exp ((ε : ℂ) * z) -
          Complex.exp ((-ε : ℂ) * z)) := by
  unfold mellinQuadraticBoxWeight mellinQuadraticBoxMultiplier
  rw [centeredMellinSpectralWeight_centeredMellinBoxApprox_eq_logAverage
    hε z]
  rw [intervalIntegral_exp_mul_complex_eq_boundary]
  by_cases hz : z = 0
  · subst z
    simp
  · simp only [ite_eq_right hz]
    field_simp [hz]

/-! ## CS13-C: one natural mode phase transport -/

private theorem nat_cpow_neg_eq_exp_neg_log_mul
    {n : ℕ} (hn : 0 < n) (w : ℂ) :
    ((n : ℂ) ^ (-w)) = Complex.exp (-((Real.log n : ℂ) * w)) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hn.ne')]
  rw [← Complex.natCast_log]
  ring_nf

private theorem nat_cpow_neg_add_eq_mul
    {n : ℕ} (hn : 0 < n) (u v : ℂ) :
    (n : ℂ) ^ (-(u + v)) =
      (n : ℂ) ^ (-u) * (n : ℂ) ^ (-v) := by
  rw [neg_add, Complex.cpow_add _ _ (by exact_mod_cast hn.ne')]

theorem pascalCenteredXiPrimeSideModePhaseTransport
    {ε : ℝ} (hε : 0 < ε)
    {n : ℕ} (hn : 0 < n)
    (z : ℂ) :
    mellinQuadraticBoxWeight ε z *
        ((n : ℂ) ^ (-(criticalLineCenter + z))) =
      ((n : ℂ) ^ (-(1 / 2 : ℂ))) *
        (((2 * ε : ℝ)⁻¹ : ℂ) * z) *
          (Complex.exp (((ε : ℝ) : ℂ) * z -
              (Real.log n : ℂ) * z) -
            Complex.exp (((-ε : ℝ) : ℂ) * z -
              (Real.log n : ℂ) * z)) := by
  rw [mellinQuadraticBoxWeight_eq_boundaryDifference hε]
  have hsplit := nat_cpow_neg_add_eq_mul hn
    (1 / 2 : ℂ) z
  rw [show criticalLineCenter = (1 / 2 : ℂ) by rfl,
    hsplit]
  rw [nat_cpow_neg_eq_exp_neg_log_mul hn]
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hn.ne')]
  rw [← Complex.natCast_log]
  have hplus : Complex.exp (((ε : ℝ) : ℂ) * z -
      (Real.log n : ℂ) * z) =
      Complex.exp (((ε : ℝ) : ℂ) * z) *
        Complex.exp (-((Real.log n : ℂ) * z)) := by
    rw [Complex.exp_sub]
    simp only [div_eq_mul_inv]
    rw [← Complex.exp_neg]
  have hminus : Complex.exp (((-ε : ℝ) : ℂ) * z -
      (Real.log n : ℂ) * z) =
      Complex.exp (-((ε : ℝ) : ℂ) * z) *
        Complex.exp (-((Real.log n : ℂ) * z)) := by
    have heps : ((-ε : ℝ) : ℂ) = -((ε : ℝ) : ℂ) := by
      norm_num
    rw [heps]
    rw [Complex.exp_sub]
    simp only [div_eq_mul_inv]
    rw [← Complex.exp_neg]
  rw [hplus, hminus]
  norm_num [Complex.ofReal_neg]
  ring

/-! ## CS13-D/E: boundary phase kernel surface -/

/-- The boundary-form integrand for one positive natural mode.  It is the
source-derived phase surface before taking the real part and integrating. -/
noncomputable def pascalCenteredXiPrimeSideFiniteModeBoundaryPhaseIntegrand
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (n : ℕ) (t : ℝ) : ℝ :=
  (((2 * ε : ℝ)⁻¹ : ℂ) *
      pascalCenteredXiPrimeSideModePhaseNode W t *
      (Complex.exp ((ε : ℂ) * pascalCenteredXiPrimeSideModePhaseNode W t) -
        Complex.exp ((-ε : ℂ) * pascalCenteredXiPrimeSideModePhaseNode W t)) *
      ((n : ℂ) ^
        (-(pascalSymmetricRectangleRightEdge W.rectangle.σ t)))).re

/-- Safe finite half-window integral of the boundary-form phase integrand. -/
noncomputable def pascalCenteredXiPrimeSideFiniteModeBoundaryPhaseKernel
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (n : ℕ) : ℝ :=
  ∫ t in (0 : ℝ)..W.rectangle.T,
    pascalCenteredXiPrimeSideFiniteModeBoundaryPhaseIntegrand ε W n t

theorem pascalCenteredXiPrimeSideFiniteModeKernel_eq_boundaryPhaseKernel
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) {n : ℕ} (hn : 0 < n) :
    pascalCenteredXiPrimeSideFiniteModeKernel ε W n =
      pascalCenteredXiPrimeSideFiniteModeBoundaryPhaseKernel ε W n := by
  unfold pascalCenteredXiPrimeSideFiniteModeKernel
    pascalCenteredXiPrimeSideFiniteModeBoundaryPhaseKernel
  apply intervalIntegral.integral_congr_ae
  filter_upwards [] with t ht
  simp only [pascalCenteredXiPrimeSideFiniteModeIntegrand,
    ite_eq_right (ne_of_gt hn),
    pascalCenteredXiPrimeSideFiniteModeBoundaryPhaseIntegrand]
  unfold pascalCenteredXiPrimeSideModePhaseNode
  have hweight : ∀ z : ℂ,
      pascalCenteredXiMellinSecondDifferenceWeight ε 0 z =
        mellinQuadraticBoxWeight ε z := by
    intro z
    rw [pascalCenteredXiMellinSecondDifferenceWeight_tau_zero_eq_quadraticWeight
      hε]
    rfl
  rw [hweight]
  rw [mellinQuadraticBoxWeight_eq_boundaryDifference hε]

/-! ## CS13-D/E: real phase and safe half-window primitive -/

theorem real_part_affine_exp_phase
    (a r t : ℝ) :
    Complex.re (((a : ℂ) + (t : ℂ) * Complex.I) *
        Complex.exp ((r : ℂ) * ((a : ℂ) + (t : ℂ) * Complex.I))) =
      Real.exp (a * r) * (a * Real.cos (r * t) -
        t * Real.sin (r * t)) := by
  simp [Complex.mul_re, Complex.exp_re, Complex.exp_im]
  ring_nf

/-- Safe, integral-definition-first phase primitive. -/
noncomputable def pascalCenteredXiPrimeSidePhasePrimitive
    (a r T : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..T,
    Real.exp (a * r) * (a * Real.cos (r * t) -
      t * Real.sin (r * t))

theorem pascalCenteredXiPrimeSidePhasePrimitive_zero_frequency
    (a T : ℝ) :
    pascalCenteredXiPrimeSidePhasePrimitive a 0 T = a * T := by
  unfold pascalCenteredXiPrimeSidePhasePrimitive
  simp
  ring

/-! ## CS13-F: the explicit phase remains signed -/

/- The nonzero-frequency closed form is intentionally a named frontier.  The
integral-definition-first kernel above is already exact and finite; this
marker prevents a later phase calculation from being mistaken for a sign
provider. -/
inductive PascalCenteredXiPrimeSideModePhaseClosedFormGap : Prop
  | nonzeroFrequencyClosedFormPending

end DkMath.RH.CFBRCProjection
