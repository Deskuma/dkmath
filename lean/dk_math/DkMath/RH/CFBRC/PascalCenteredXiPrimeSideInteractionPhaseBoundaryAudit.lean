/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideCommonCarrierInteractionCancellationAudit
import Mathlib.Tactic

/-!
# CS26: interaction phase / boundary closed-form audit

This module closes the finite oscillatory primitive used by the CS25
interaction term.  The resulting formulas are finite identities only: they
do not provide a sign for the interaction, a tail exchange, or an RH
conclusion.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.Analysis
open DkMath.NumberTheory
open DkMath.NumberTheory.PrimitiveSet
open Filter
open MeasureTheory
open scoped Interval Topology

/-! ## CS26-A: the finite phase primitive -/

private theorem cs26PhaseCandidate_continuousOn
    (a r : ℝ) :
    ContinuousOn
      (fun t : ℝ => Real.exp (a * r) *
        (t * Real.cos (r * t) / r +
          (a * r - 1) * Real.sin (r * t) / r ^ 2))
      (Set.uIcc (0 : ℝ) 0) := by
  fun_prop

private theorem cs26PhaseCandidate_hasDerivAt
    {a r x : ℝ} (hr : r ≠ 0) :
    HasDerivAt
      (fun t : ℝ => Real.exp (a * r) *
        (t * Real.cos (r * t) / r +
          (a * r - 1) * Real.sin (r * t) / r ^ 2))
      (Real.exp (a * r) *
        (a * Real.cos (r * x) - x * Real.sin (r * x))) x := by
  have hrt : HasDerivAt (fun t : ℝ => r * t) r x := by
    simpa [mul_comm] using (hasDerivAt_id x).const_mul r
  have hcos : HasDerivAt (fun t : ℝ => Real.cos (r * t))
      (-r * Real.sin (r * x)) x := by
    simpa [Function.comp_def, mul_comm] using
      (Real.hasDerivAt_cos (r * x)).comp x hrt
  have hsin : HasDerivAt (fun t : ℝ => Real.sin (r * t))
      (r * Real.cos (r * x)) x := by
    simpa [Function.comp_def, mul_comm] using
      (Real.hasDerivAt_sin (r * x)).comp x hrt
  have htc : HasDerivAt (fun t : ℝ => t * Real.cos (r * t))
      (Real.cos (r * x) - x * r * Real.sin (r * x)) x := by
    convert! (hasDerivAt_id' x).mul hcos using 1 <;> simp [Pi.mul_apply,
      id_eq, mul_comm, mul_left_comm, mul_assoc] <;> ring
  have hfirst : HasDerivAt (fun t : ℝ => t * Real.cos (r * t) / r)
      ((Real.cos (r * x) - x * r * Real.sin (r * x)) / r) x := by
    simpa using htc.div_const r
  have hsecond : HasDerivAt
      (fun t : ℝ => (a * r - 1) * Real.sin (r * t) / r ^ 2)
      ((a * r - 1) * (r * Real.cos (r * x)) / r ^ 2) x := by
    simpa [mul_assoc] using (hsin.const_mul (a * r - 1)).div_const (r ^ 2)
  have hsum := hfirst.add hsecond
  have hresult := hsum.const_mul (Real.exp (a * r))
  have hresult' : HasDerivAt
      (fun t : ℝ => Real.exp (a * r) *
        (t * Real.cos (r * t) / r +
          (a * r - 1) * Real.sin (r * t) / r ^ 2))
      (Real.exp (a * r) *
        ((Real.cos (r * x) - x * r * Real.sin (r * x)) / r +
          (a * r - 1) * (r * Real.cos (r * x)) / r ^ 2)) x := by
    simpa [Pi.add_apply, smul_eq_mul] using hresult
  have hder :
      Real.exp (a * r) *
          ((Real.cos (r * x) - x * r * Real.sin (r * x)) / r +
            (a * r - 1) * (r * Real.cos (r * x)) / r ^ 2) =
        Real.exp (a * r) *
          (a * Real.cos (r * x) - x * Real.sin (r * x)) := by
    congr 1
    field_simp [hr]
    ring
  rw [hder] at hresult'
  exact hresult'

theorem pascalCenteredXiPrimeSidePhasePrimitive_nonzero_frequency
    {a r T : ℝ} (hr : r ≠ 0) :
    pascalCenteredXiPrimeSidePhasePrimitive a r T =
      Real.exp (a * r) *
        (T * Real.cos (r * T) / r +
          (a * r - 1) * Real.sin (r * T) / r ^ 2) := by
  unfold pascalCenteredXiPrimeSidePhasePrimitive
  have hcont : ContinuousOn
      (fun t : ℝ => Real.exp (a * r) *
        (t * Real.cos (r * t) / r +
          (a * r - 1) * Real.sin (r * t) / r ^ 2))
      (Set.uIcc (0 : ℝ) T) := by
    fun_prop
  have hderiv : ∀ x ∈ Set.Ioo (min (0 : ℝ) T) (max (0 : ℝ) T),
      HasDerivWithinAt
        (fun t : ℝ => Real.exp (a * r) *
          (t * Real.cos (r * t) / r +
            (a * r - 1) * Real.sin (r * t) / r ^ 2))
        (Real.exp (a * r) *
          (a * Real.cos (r * x) - x * Real.sin (r * x)))
        (Set.Ioi x) x := by
    intro x hx
    exact (cs26PhaseCandidate_hasDerivAt hr).hasDerivWithinAt
  have hint : IntervalIntegrable
      (fun t : ℝ => Real.exp (a * r) *
        (a * Real.cos (r * t) - t * Real.sin (r * t)))
      volume 0 T := by
    have hc : Continuous (fun t : ℝ => Real.exp (a * r) *
        (a * Real.cos (r * t) - t * Real.sin (r * t))) := by
      fun_prop
    exact hc.intervalIntegrable (μ := volume) 0 T
  have hfund := intervalIntegral.integral_eq_sub_of_hasDeriv_right
    hcont hderiv hint
  simpa using hfund

noncomputable def pascalCenteredXiPrimeSidePhasePrimitiveClosedForm
    (a r T : ℝ) : ℝ :=
  if r = 0 then a * T else
    Real.exp (a * r) *
      (T * Real.cos (r * T) / r +
        (a * r - 1) * Real.sin (r * T) / r ^ 2)

theorem pascalCenteredXiPrimeSidePhasePrimitive_eq_closedForm
    (a r T : ℝ) :
    pascalCenteredXiPrimeSidePhasePrimitive a r T =
      pascalCenteredXiPrimeSidePhasePrimitiveClosedForm a r T := by
  by_cases hr : r = 0
  · simp [pascalCenteredXiPrimeSidePhasePrimitiveClosedForm, hr,
      pascalCenteredXiPrimeSidePhasePrimitive_zero_frequency]
  · simp [pascalCenteredXiPrimeSidePhasePrimitiveClosedForm, hr,
      pascalCenteredXiPrimeSidePhasePrimitive_nonzero_frequency hr]

/-! ## CS26 bonus: two boundary values that require no sign input -/

theorem pascalCenteredXiPrimeSidePhasePrimitive_zero_height
    (a r : ℝ) :
    pascalCenteredXiPrimeSidePhasePrimitive a r 0 = 0 := by
  unfold pascalCenteredXiPrimeSidePhasePrimitive
  simp

theorem pascalCenteredXiPrimeSidePhasePrimitive_zero_epsilon_difference
    (a r : ℝ) :
    pascalCenteredXiPrimeSidePhasePrimitive a r 0 -
        pascalCenteredXiPrimeSidePhasePrimitive a r 0 = 0 := by
  ring

/-! ## CS26-C: source cutoff and the safe frequency regime -/

theorem pascalCenteredXiPrimeSide_vonMangoldt_zero :
    (ArithmeticFunction.vonMangoldt 0 : ℝ) = 0 := by
  simp

theorem pascalCenteredXiPrimeSide_vonMangoldt_one :
    (ArithmeticFunction.vonMangoldt 1 : ℝ) = 0 := by
  simp

private theorem cs26_nat_cpow_neg_half
    {n : ℕ} (hn : 0 < n) :
    (n : ℂ) ^ (-(1 / 2 : ℂ)) =
      ((Real.exp (-(1 / 2 : ℝ) * Real.log (n : ℝ))) : ℂ) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hn.ne')]
  rw [← Complex.natCast_log]
  norm_num [Complex.ofReal_exp]
  congr 1
  ring

noncomputable def pascalCenteredXiPrimeSidePhaseFrequencyPlus
    (ε : ℝ) (n : ℕ) : ℝ :=
  ε - Real.log n

noncomputable def pascalCenteredXiPrimeSidePhaseFrequencyMinus
    (ε : ℝ) (n : ℕ) : ℝ :=
  -ε - Real.log n

noncomputable def pascalCenteredXiPrimeSidePhaseCarrier
    (ε : ℝ) (n : ℕ) : ℝ :=
  (2 * ε)⁻¹ * Real.exp (-(1 / 2 : ℝ) * Real.log n)

noncomputable def pascalCenteredXiPrimeSidePhaseIntegrand
    (a r t : ℝ) : ℝ :=
  Real.exp (a * r) * (a * Real.cos (r * t) - t * Real.sin (r * t))

private theorem cs26_boundary_integrand_eq_phase_difference
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) {n : ℕ} (hn : 0 < n)
    (t : ℝ) :
    pascalCenteredXiPrimeSideFiniteModeBoundaryPhaseIntegrand ε W n t =
      pascalCenteredXiPrimeSidePhaseCarrier ε n *
        (pascalCenteredXiPrimeSidePhaseIntegrand
            (W.rectangle.σ - (1 / 2 : ℝ))
            (pascalCenteredXiPrimeSidePhaseFrequencyPlus ε n) t -
          pascalCenteredXiPrimeSidePhaseIntegrand
            (W.rectangle.σ - (1 / 2 : ℝ))
            (pascalCenteredXiPrimeSidePhaseFrequencyMinus ε n) t) := by
  let z := pascalCenteredXiPrimeSideModePhaseNode W t
  have hnode : criticalLineCenter + z =
      pascalSymmetricRectangleRightEdge W.rectangle.σ t := by
    simp [z, pascalCenteredXiPrimeSideModePhaseNode,
      pascalOrdinaryToCentered]
  have htransport := pascalCenteredXiPrimeSideModePhaseTransport
    hε hn z
  have hboundary :
      (((2 * ε : ℝ)⁻¹ : ℂ) * z *
        (Complex.exp ((ε : ℂ) * z) -
          Complex.exp ((-ε : ℂ) * z)) *
        ((n : ℂ) ^
          (-(pascalSymmetricRectangleRightEdge W.rectangle.σ t)))) =
        ((n : ℂ) ^ (-(1 / 2 : ℂ))) *
          (((2 * ε : ℝ)⁻¹ : ℂ) * z) *
            (Complex.exp (((ε : ℝ) : ℂ) * z -
                (Real.log n : ℂ) * z) -
              Complex.exp (((-ε : ℝ) : ℂ) * z -
                (Real.log n : ℂ) * z)) := by
    calc
      (((2 * ε : ℝ)⁻¹ : ℂ) * z *
          (Complex.exp ((ε : ℂ) * z) -
            Complex.exp ((-ε : ℂ) * z)) *
          ((n : ℂ) ^
            (-(pascalSymmetricRectangleRightEdge W.rectangle.σ t)))) =
          mellinQuadraticBoxWeight ε z *
            ((n : ℂ) ^ (-(criticalLineCenter + z))) := by
              rw [mellinQuadraticBoxWeight_eq_boundaryDifference hε]
              rw [hnode]
      _ = _ := htransport
  unfold pascalCenteredXiPrimeSideFiniteModeBoundaryPhaseIntegrand
  rw [hboundary]
  rw [cs26_nat_cpow_neg_half hn]
  dsimp [z]
  rw [pascalCenteredXiPrimeSideModePhaseNode_eq_affine]
  simp only [pascalCenteredXiPrimeSidePhaseCarrier,
    pascalCenteredXiPrimeSidePhaseIntegrand,
    pascalCenteredXiPrimeSidePhaseFrequencyPlus,
    pascalCenteredXiPrimeSidePhaseFrequencyMinus]
  have hplus :
      (((ε : ℝ) : ℂ) *
          (((W.rectangle.σ - (1 / 2 : ℝ) : ℝ) : ℂ) +
            (t : ℂ) * Complex.I) -
        (Real.log n : ℂ) *
          (((W.rectangle.σ - (1 / 2 : ℝ) : ℝ) : ℂ) +
            (t : ℂ) * Complex.I)) =
        (((ε - Real.log n : ℝ) : ℂ) *
          (((W.rectangle.σ - (1 / 2 : ℝ) : ℝ) : ℂ) +
            (t : ℂ) * Complex.I)) := by
    norm_num
    ring
  have hminus :
      (((-ε : ℝ) : ℂ) *
          (((W.rectangle.σ - (1 / 2 : ℝ) : ℝ) : ℂ) +
            (t : ℂ) * Complex.I) -
        (Real.log n : ℂ) *
          (((W.rectangle.σ - (1 / 2 : ℝ) : ℝ) : ℂ) +
            (t : ℂ) * Complex.I)) =
        (((-ε - Real.log n : ℝ) : ℂ) *
          (((W.rectangle.σ - (1 / 2 : ℝ) : ℝ) : ℂ) +
            (t : ℂ) * Complex.I)) := by
    norm_num
    ring
  rw [hplus, hminus]
  let a : ℝ := W.rectangle.σ - (1 / 2 : ℝ)
  have hphase (r : ℝ) :
      Complex.re (((Real.exp (-(1 / 2 : ℝ) * Real.log n) : ℂ) *
          ((2 * ε : ℝ)⁻¹ : ℂ)) *
        (((a : ℂ) + (t : ℂ) * Complex.I) *
          Complex.exp ((r : ℂ) * ((a : ℂ) + (t : ℂ) * Complex.I)))) =
          pascalCenteredXiPrimeSidePhaseCarrier ε n *
          pascalCenteredXiPrimeSidePhaseIntegrand a r t := by
    have him :
        (((a : ℂ) + (t : ℂ) * Complex.I) *
          Complex.exp ((r : ℂ) * ((a : ℂ) + (t : ℂ) * Complex.I))).im =
          Real.exp (a * r) *
            (a * Real.sin (r * t) + t * Real.cos (r * t)) := by
      simp [Complex.mul_im, Complex.exp_re, Complex.exp_im]
      ring
    rw [Complex.mul_re]
    rw [real_part_affine_exp_phase]
    rw [him]
    have hscalar :
        ((Real.exp (-(1 / 2 : ℝ) * Real.log n) : ℂ) *
            ((2 * ε : ℝ)⁻¹ : ℂ)).re =
          Real.exp (-(1 / 2 : ℝ) * Real.log n) * (2 * ε)⁻¹ := by
      have h2ε : (2 * ε : ℝ) ≠ 0 := by nlinarith
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, sub_zero, zero_mul, add_zero]
      simp [h2ε]
    have hscalar_im :
        ((Real.exp (-(1 / 2 : ℝ) * Real.log n) : ℂ) *
            ((2 * ε : ℝ)⁻¹ : ℂ)).im = 0 := by
      have h2ε : (2 * ε : ℝ) ≠ 0 := by nlinarith
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, sub_zero, zero_mul, add_zero]
      simp [h2ε]
    rw [hscalar, hscalar_im]
    simp only [pascalCenteredXiPrimeSidePhaseCarrier,
      pascalCenteredXiPrimeSidePhaseIntegrand]
    ring
  have hsplit :
      Complex.re (((Real.exp (-(1 / 2 : ℝ) * Real.log n) : ℂ) *
          ((2 * ε : ℝ)⁻¹ : ℂ)) *
        (((a : ℂ) + (t : ℂ) * Complex.I) *
          (Complex.exp ((pascalCenteredXiPrimeSidePhaseFrequencyPlus ε n : ℂ) *
              ((a : ℂ) + (t : ℂ) * Complex.I)) -
            Complex.exp ((pascalCenteredXiPrimeSidePhaseFrequencyMinus ε n : ℂ) *
              ((a : ℂ) + (t : ℂ) * Complex.I))))) =
      Complex.re (((Real.exp (-(1 / 2 : ℝ) * Real.log n) : ℂ) *
          ((2 * ε : ℝ)⁻¹ : ℂ)) *
        (((a : ℂ) + (t : ℂ) * Complex.I) *
          Complex.exp ((pascalCenteredXiPrimeSidePhaseFrequencyPlus ε n : ℂ) *
            ((a : ℂ) + (t : ℂ) * Complex.I)))) -
      Complex.re (((Real.exp (-(1 / 2 : ℝ) * Real.log n) : ℂ) *
          ((2 * ε : ℝ)⁻¹ : ℂ)) *
        (((a : ℂ) + (t : ℂ) * Complex.I) *
          Complex.exp ((pascalCenteredXiPrimeSidePhaseFrequencyMinus ε n : ℂ) *
            ((a : ℂ) + (t : ℂ) * Complex.I)))) := by
    congr 1 <;>
      simp [pascalCenteredXiPrimeSidePhaseFrequencyPlus,
        pascalCenteredXiPrimeSidePhaseFrequencyMinus] <;> ring
  have hassoc :
      Complex.re (((Real.exp (-(1 / 2 : ℝ) * Real.log n) : ℂ) *
          (((2 * ε : ℝ)⁻¹ : ℂ) *
            (((W.rectangle.σ - (1 / 2 : ℝ) : ℝ) : ℂ) +
              (t : ℂ) * Complex.I))) *
        (Complex.exp (((ε - Real.log n : ℝ) : ℂ) *
            (((W.rectangle.σ - (1 / 2 : ℝ) : ℝ) : ℂ) +
              (t : ℂ) * Complex.I)) -
          Complex.exp (((-ε - Real.log n : ℝ) : ℂ) *
            (((W.rectangle.σ - (1 / 2 : ℝ) : ℝ) : ℂ) +
              (t : ℂ) * Complex.I)))) =
      Complex.re (((Real.exp (-(1 / 2 : ℝ) * Real.log n) : ℂ) *
          ((2 * ε : ℝ)⁻¹ : ℂ)) *
        ((((W.rectangle.σ - (1 / 2 : ℝ) : ℝ) : ℂ) +
            (t : ℂ) * Complex.I) *
          (Complex.exp (((ε - Real.log n : ℝ) : ℂ) *
              (((W.rectangle.σ - (1 / 2 : ℝ) : ℝ) : ℂ) +
                (t : ℂ) * Complex.I)) -
            Complex.exp (((-ε - Real.log n : ℝ) : ℂ) *
              (((W.rectangle.σ - (1 / 2 : ℝ) : ℝ) : ℂ) +
                (t : ℂ) * Complex.I))))) := by
    congr 1 <;> ring
  have hsplit' :
      Complex.re (((Real.exp (-(1 / 2 : ℝ) * Real.log n) : ℂ) *
          ((2 * ε : ℝ)⁻¹ : ℂ)) *
        (((a : ℂ) + (t : ℂ) * Complex.I) *
          (Complex.exp (((ε - Real.log n : ℝ) : ℂ) *
              ((a : ℂ) + (t : ℂ) * Complex.I)) -
            Complex.exp (((-ε - Real.log n : ℝ) : ℂ) *
              ((a : ℂ) + (t : ℂ) * Complex.I))))) =
      Complex.re (((Real.exp (-(1 / 2 : ℝ) * Real.log n) : ℂ) *
          ((2 * ε : ℝ)⁻¹ : ℂ)) *
        (((a : ℂ) + (t : ℂ) * Complex.I) *
          Complex.exp (((ε - Real.log n : ℝ) : ℂ) *
            ((a : ℂ) + (t : ℂ) * Complex.I)))) -
      Complex.re (((Real.exp (-(1 / 2 : ℝ) * Real.log n) : ℂ) *
          ((2 * ε : ℝ)⁻¹ : ℂ)) *
        (((a : ℂ) + (t : ℂ) * Complex.I) *
          Complex.exp (((-ε - Real.log n : ℝ) : ℂ) *
            ((a : ℂ) + (t : ℂ) * Complex.I)))) := by
    congr 1 <;> ring
  rw [hassoc, hsplit', hphase, hphase]
  simp only [pascalCenteredXiPrimeSidePhaseCarrier,
    pascalCenteredXiPrimeSidePhaseIntegrand]
  dsimp [a]
  ring

theorem pascalCenteredXiPrimeSideFiniteModeKernel_eq_phasePrimitive_difference
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) {n : ℕ} (hn : 0 < n) :
    pascalCenteredXiPrimeSideFiniteModeKernel ε W n =
      pascalCenteredXiPrimeSidePhaseCarrier ε n *
        (pascalCenteredXiPrimeSidePhasePrimitive
            (W.rectangle.σ - (1 / 2 : ℝ))
            (pascalCenteredXiPrimeSidePhaseFrequencyPlus ε n)
            W.rectangle.T -
          pascalCenteredXiPrimeSidePhasePrimitive
            (W.rectangle.σ - (1 / 2 : ℝ))
            (pascalCenteredXiPrimeSidePhaseFrequencyMinus ε n)
            W.rectangle.T) := by
  have hplus : IntervalIntegrable
      (pascalCenteredXiPrimeSidePhaseIntegrand
        (W.rectangle.σ - (1 / 2 : ℝ))
        (pascalCenteredXiPrimeSidePhaseFrequencyPlus ε n))
      volume 0 W.rectangle.T := by
    have hc : Continuous
        (pascalCenteredXiPrimeSidePhaseIntegrand
          (W.rectangle.σ - (1 / 2 : ℝ))
          (pascalCenteredXiPrimeSidePhaseFrequencyPlus ε n)) := by
      unfold pascalCenteredXiPrimeSidePhaseIntegrand
      fun_prop
    exact hc.intervalIntegrable (μ := volume) 0 W.rectangle.T
  have hminus : IntervalIntegrable
      (pascalCenteredXiPrimeSidePhaseIntegrand
        (W.rectangle.σ - (1 / 2 : ℝ))
        (pascalCenteredXiPrimeSidePhaseFrequencyMinus ε n))
      volume 0 W.rectangle.T := by
    have hc : Continuous
        (pascalCenteredXiPrimeSidePhaseIntegrand
          (W.rectangle.σ - (1 / 2 : ℝ))
          (pascalCenteredXiPrimeSidePhaseFrequencyMinus ε n)) := by
      unfold pascalCenteredXiPrimeSidePhaseIntegrand
      fun_prop
    exact hc.intervalIntegrable (μ := volume) 0 W.rectangle.T
  rw [pascalCenteredXiPrimeSideFiniteModeKernel_eq_boundaryPhaseKernel hε W hn]
  unfold pascalCenteredXiPrimeSideFiniteModeBoundaryPhaseKernel
    pascalCenteredXiPrimeSidePhasePrimitive
  have hplusRaw : IntervalIntegrable
      (fun t : ℝ => Real.exp ((W.rectangle.σ - (1 / 2 : ℝ)) *
          pascalCenteredXiPrimeSidePhaseFrequencyPlus ε n) *
        ((W.rectangle.σ - (1 / 2 : ℝ)) *
            Real.cos (pascalCenteredXiPrimeSidePhaseFrequencyPlus ε n * t) -
          t * Real.sin (pascalCenteredXiPrimeSidePhaseFrequencyPlus ε n * t)))
      volume 0 W.rectangle.T := by
    have hc : Continuous (fun t : ℝ =>
        Real.exp ((W.rectangle.σ - (1 / 2 : ℝ)) *
            pascalCenteredXiPrimeSidePhaseFrequencyPlus ε n) *
          ((W.rectangle.σ - (1 / 2 : ℝ)) *
              Real.cos (pascalCenteredXiPrimeSidePhaseFrequencyPlus ε n * t) -
            t * Real.sin (pascalCenteredXiPrimeSidePhaseFrequencyPlus ε n * t))) := by
      fun_prop
    exact hc.intervalIntegrable (μ := volume) 0 W.rectangle.T
  have hminusRaw : IntervalIntegrable
      (fun t : ℝ => Real.exp ((W.rectangle.σ - (1 / 2 : ℝ)) *
          pascalCenteredXiPrimeSidePhaseFrequencyMinus ε n) *
        ((W.rectangle.σ - (1 / 2 : ℝ)) *
            Real.cos (pascalCenteredXiPrimeSidePhaseFrequencyMinus ε n * t) -
          t * Real.sin (pascalCenteredXiPrimeSidePhaseFrequencyMinus ε n * t)))
      volume 0 W.rectangle.T := by
    have hc : Continuous (fun t : ℝ =>
        Real.exp ((W.rectangle.σ - (1 / 2 : ℝ)) *
            pascalCenteredXiPrimeSidePhaseFrequencyMinus ε n) *
          ((W.rectangle.σ - (1 / 2 : ℝ)) *
              Real.cos (pascalCenteredXiPrimeSidePhaseFrequencyMinus ε n * t) -
            t * Real.sin (pascalCenteredXiPrimeSidePhaseFrequencyMinus ε n * t))) := by
      fun_prop
    exact hc.intervalIntegrable (μ := volume) 0 W.rectangle.T
  rw [← intervalIntegral.integral_sub hplusRaw hminusRaw]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [] with t ht
  exact cs26_boundary_integrand_eq_phase_difference hε W hn t

theorem pascalCenteredXiPrimeSideFiniteModeKernel_eq_closedPhaseBoundary_difference
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) {n : ℕ} (hn : 0 < n) :
    pascalCenteredXiPrimeSideFiniteModeKernel ε W n =
      pascalCenteredXiPrimeSidePhaseCarrier ε n *
        (pascalCenteredXiPrimeSidePhasePrimitiveClosedForm
            (W.rectangle.σ - (1 / 2 : ℝ))
            (pascalCenteredXiPrimeSidePhaseFrequencyPlus ε n)
            W.rectangle.T -
          pascalCenteredXiPrimeSidePhasePrimitiveClosedForm
            (W.rectangle.σ - (1 / 2 : ℝ))
            (pascalCenteredXiPrimeSidePhaseFrequencyMinus ε n)
            W.rectangle.T) := by
  rw [pascalCenteredXiPrimeSideFiniteModeKernel_eq_phasePrimitive_difference hε W hn,
    pascalCenteredXiPrimeSidePhasePrimitive_eq_closedForm,
    pascalCenteredXiPrimeSidePhasePrimitive_eq_closedForm]

noncomputable def pascalCenteredXiPrimeSideFiniteClosedPhaseModeTerm
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (n : ℕ) : ℝ :=
  if n = 0 then 0 else
    pascalCenteredXiPrimeSidePhaseCarrier ε n *
      (pascalCenteredXiPrimeSidePhasePrimitiveClosedForm
          (W.rectangle.σ - (1 / 2 : ℝ))
          (pascalCenteredXiPrimeSidePhaseFrequencyPlus ε n)
          W.rectangle.T -
        pascalCenteredXiPrimeSidePhasePrimitiveClosedForm
          (W.rectangle.σ - (1 / 2 : ℝ))
          (pascalCenteredXiPrimeSidePhaseFrequencyMinus ε n)
          W.rectangle.T)

theorem pascalCenteredXiPrimeSideFiniteClosedPhaseModeTerm_eq_kernel
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) {n : ℕ} (hn : 0 < n) :
    pascalCenteredXiPrimeSideFiniteClosedPhaseModeTerm ε W n =
      pascalCenteredXiPrimeSideFiniteModeKernel ε W n := by
  rw [pascalCenteredXiPrimeSideFiniteClosedPhaseModeTerm, if_neg hn.ne']
  exact (pascalCenteredXiPrimeSideFiniteModeKernel_eq_closedPhaseBoundary_difference
    hε W hn).symm

theorem pascalCenteredXiPrimeSideAggregateInteraction_eq_closedPhaseLedger
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W X =
      2 * (∑ n ∈ Finset.range (X + 1),
        (ArithmeticFunction.vonMangoldt n : ℝ) *
          pascalCenteredXiPrimeSideFiniteClosedPhaseModeTerm ε W n) := by
  classical
  rw [pascalCenteredXiPrimeSideAggregateRayInteractionEnergy_eq_two_modeSum hε W X]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hn0 : n = 0
  · simp [hn0, pascalCenteredXiPrimeSide_vonMangoldt_zero]
  · rw [pascalCenteredXiPrimeSideFiniteClosedPhaseModeTerm_eq_kernel hε W
      (Nat.pos_of_ne_zero hn0)]

/-! The last horizontal/top-boundary comparison remains a separate audit
frontier.  Naming it here prevents the exact finite ledger from being read as
a matching or sign provider. -/

inductive PascalCenteredXiPrimeSideInteractionPhaseTopBoundaryMatchGap : Prop
  | topHorizontalCorrectionMatchingPending

theorem pascalCenteredXiPrimeSide_phase_frequencies_nonzero
    {ε : ℝ} {n : ℕ} (hε : 0 < ε)
    (hεn : ε < Real.log n) (hn : 0 < n) :
    ε - Real.log n ≠ 0 ∧ -ε - Real.log n ≠ 0 := by
  constructor <;> nlinarith [hεn]

theorem pascalCenteredXiPrimeSide_phase_frequencies_safe_cutoff
    {ε : ℝ} {n : ℕ} (hε : 0 < ε)
    (hε2 : ε < Real.log 2) (hn : 2 ≤ n) :
    ε < Real.log n ∧
      pascalCenteredXiPrimeSidePhaseFrequencyPlus ε n ≠ 0 ∧
      pascalCenteredXiPrimeSidePhaseFrequencyMinus ε n ≠ 0 := by
  have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le (by norm_num) hnreal
  have hlog : Real.log 2 ≤ Real.log n := by
    exact Real.strictMonoOn_log.monotoneOn (by norm_num) hnpos hnreal
  have hεn : ε < Real.log n := lt_of_lt_of_le hε2 hlog
  refine ⟨hεn, ?_⟩
  simpa [pascalCenteredXiPrimeSidePhaseFrequencyPlus,
    pascalCenteredXiPrimeSidePhaseFrequencyMinus] using
    pascalCenteredXiPrimeSide_phase_frequencies_nonzero hε hεn (by omega : 0 < n)

end DkMath.RH.CFBRCProjection
