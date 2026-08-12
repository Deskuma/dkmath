/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.PascalCenteredXiExplicitFormulaFunctionalEquationReflection
import DkMath.Analysis.MellinMultiplicativeApproxIdentity
import Mathlib.Tactic

/-!
# Finite-window horizontal pairing and Mellin decay audit

This module closes the finite-height horizontal geometry left open by
XDP-010.  For an even centered weight, the bottom horizontal contribution
equals the top contribution, so the four-edge fixed-Xi rectangle is exactly
the sum of twice the right-edge decomposed observable and twice one finite
horizontal contribution.

The Mellin box weight is audited separately.  Its centered spectral weight and
its centered second-difference weight are proved even.  A possible
imaginary-height decay is represented by a provider contract only: decay of
the weight alone is not decay of the Xi-weighted integrand, and no `T → ∞`
transport is taken under a fixed same-zero-set window.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open MeasureTheory
open Set
open DkMath.Analysis
open scoped Interval Topology

/-! ## Gates A-C: horizontal reflection and pairing -/

/-- The bottom horizontal fixed-Xi integrand, parameterized in ordinary
coordinates but evaluated after the canonical ordinary-to-centered
translation. -/
def pascalCenteredXiBottomHorizontalIntegrand
    (h : ℂ → ℂ) (T u : ℝ) : ℂ :=
  pascalCenteredXiWeightedNegLogDeriv h
    (pascalOrdinaryToCentered (pascalSymmetricRectangleBottomEdge u T))

/-- The top horizontal fixed-Xi integrand. -/
def pascalCenteredXiTopHorizontalIntegrand
    (h : ℂ → ℂ) (T u : ℝ) : ℂ :=
  pascalCenteredXiWeightedNegLogDeriv h
    (pascalOrdinaryToCentered (pascalSymmetricRectangleTopEdge u T))

/-- Reflection of the horizontal integrands, before interval orientation is
reversed. -/
theorem pascalCenteredXiBottomHorizontalIntegrand_reflected
    {h : ℂ → ℂ} (hh : PascalCenteredEvenWeight h)
    (T u : ℝ) :
    pascalCenteredXiBottomHorizontalIntegrand h T (1 - u) =
      -pascalCenteredXiTopHorizontalIntegrand h T u := by
  unfold pascalCenteredXiBottomHorizontalIntegrand
    pascalCenteredXiTopHorizontalIntegrand
  rw [pascalOrdinaryToCentered_bottomEdge_reflected_eq_neg_topEdge]
  rw [pascalCenteredXiWeightedNegLogDeriv_neg hh]

/-- The bottom horizontal contribution equals the top contribution.  The
pointwise minus sign from fixed-Xi oddness is cancelled by the reversed
interval orientation. -/
theorem pascalCenteredXiBottomHorizontalContribution_eq_top
    {h : ℂ → ℂ} (hh : PascalCenteredEvenWeight h)
    (W : PascalCenteredXiContourTransportWindow) :
    pascalCenteredXiBottomHorizontalContribution h W =
      pascalCenteredXiTopHorizontalContribution h W := by
  unfold pascalCenteredXiBottomHorizontalContribution
    pascalCenteredXiTopHorizontalContribution
  have hbottom :
      (fun u : ℝ => pascalCenteredXiBottomHorizontalIntegrand
        h W.rectangle.T u) =
      (fun u : ℝ => pascalCenteredXiWeightedNegLogDeriv h
        (pascalOrdinaryToCentered
          (pascalSymmetricRectangleBottomEdge u W.rectangle.T))) := by
    rfl
  let f : ℝ → ℂ := fun u =>
    pascalCenteredXiBottomHorizontalIntegrand h W.rectangle.T u
  let g : ℝ → ℂ := fun u =>
    pascalCenteredXiTopHorizontalIntegrand h W.rectangle.T u
  have hcomp :
      (∫ u in W.rectangle.σ..1 - W.rectangle.σ, f (1 - u)) =
        ∫ u in W.rectangle.σ..1 - W.rectangle.σ, f u := by
    simpa only [sub_sub_cancel] using
      (intervalIntegral.integral_comp_sub_left
        (f := f) (a := W.rectangle.σ) (b := 1 - W.rectangle.σ) (d := 1))
  have hreflect :
      (∫ u in W.rectangle.σ..1 - W.rectangle.σ, f (1 - u)) =
        -∫ u in W.rectangle.σ..1 - W.rectangle.σ, g u := by
    calc
      (∫ u in W.rectangle.σ..1 - W.rectangle.σ, f (1 - u)) =
          ∫ u in W.rectangle.σ..1 - W.rectangle.σ, -g u := by
        apply intervalIntegral.integral_congr
        intro u hu
        exact pascalCenteredXiBottomHorizontalIntegrand_reflected hh
          W.rectangle.T u
      _ = -∫ u in W.rectangle.σ..1 - W.rectangle.σ, g u := by
        rw [intervalIntegral.integral_neg]
  rw [← hbottom]
  change (∫ u in (1 - W.rectangle.σ)..W.rectangle.σ, f u) = _
  calc
    (∫ u in (1 - W.rectangle.σ)..W.rectangle.σ, f u) =
        -∫ u in W.rectangle.σ..1 - W.rectangle.σ, f u :=
      by rw [intervalIntegral.integral_symm]
    _ = -∫ u in W.rectangle.σ..1 - W.rectangle.σ, f (1 - u) := by
      rw [hcomp]
    _ = ∫ u in W.rectangle.σ..1 - W.rectangle.σ, g u := by
      rw [hreflect]
      simp

/-- The horizontal pair is twice the top contribution. -/
theorem pascalCenteredXiHorizontalPair_eq_two_top
    {h : ℂ → ℂ} (hh : PascalCenteredEvenWeight h)
    (W : PascalCenteredXiContourTransportWindow) :
    pascalCenteredXiTopHorizontalContribution h W +
        pascalCenteredXiBottomHorizontalContribution h W =
      2 * pascalCenteredXiTopHorizontalContribution h W := by
  rw [pascalCenteredXiBottomHorizontalContribution_eq_top hh W]
  ring

/-! ## Gate D: full finite rectangle reduction -/

/-- The canonical centered fixed-Xi rectangle contribution. -/
def pascalCenteredXiRectangleContribution
    (h : ℂ → ℂ) (W : PascalCenteredXiContourTransportWindow) : ℂ :=
  pascalExplicitFormulaCenteredRectangleContribution
    (pascalCenteredXiWeightedNegLogDeriv h) W

/-- The four-edge fixed-Xi rectangle reduces at finite height to twice the
right-edge decomposed observable plus twice the named top horizontal term. -/
theorem pascalCenteredXiRectangleContribution_eq_two_right_decomposed_add_two_top
    {h : ℂ → ℂ} (hh : PascalCenteredEvenWeight h)
    (W : PascalCenteredXiContourTransportWindow) :
    pascalCenteredXiRectangleContribution h W =
      2 * (∫ t in (-W.rectangle.T)..W.rectangle.T,
        (h (pascalOrdinaryToCentered
            (pascalSymmetricRectangleRightEdge W.rectangle.σ t)) *
          pascalXiDecomposedNegLogDeriv
            (pascalSymmetricRectangleRightEdge W.rectangle.σ t)) *
          Complex.I) +
        2 * pascalCenteredXiTopHorizontalContribution h W := by
  unfold pascalCenteredXiRectangleContribution
    pascalExplicitFormulaCenteredRectangleContribution
    pascalExplicitFormulaOrdinaryRectangleContribution
    pascalSymmetricRectangleBoundaryIntegral
  change
    pascalCenteredXiRightVerticalContribution h W +
        pascalCenteredXiTopHorizontalContribution h W +
        pascalCenteredXiLeftVerticalContribution h W +
        pascalCenteredXiBottomHorizontalContribution h W = _
  calc
    pascalCenteredXiRightVerticalContribution h W +
        pascalCenteredXiTopHorizontalContribution h W +
        pascalCenteredXiLeftVerticalContribution h W +
        pascalCenteredXiBottomHorizontalContribution h W =
      (pascalCenteredXiLeftVerticalContribution h W +
          pascalCenteredXiRightVerticalContribution h W) +
        (pascalCenteredXiTopHorizontalContribution h W +
          pascalCenteredXiBottomHorizontalContribution h W) := by ring
    _ = 2 * (∫ t in (-W.rectangle.T)..W.rectangle.T,
        (h (pascalOrdinaryToCentered
            (pascalSymmetricRectangleRightEdge W.rectangle.σ t)) *
          pascalXiDecomposedNegLogDeriv
            (pascalSymmetricRectangleRightEdge W.rectangle.σ t)) *
          Complex.I) +
        2 * pascalCenteredXiTopHorizontalContribution h W := by
      rw [pascalCenteredXiVerticalPair_eq_two_right_decomposed hh W,
        pascalCenteredXiHorizontalPair_eq_two_top hh W]

/-! ## Gate E: Mellin evenness -/

/-- The logarithmic box Mellin spectral weight is even in the centered
complex coordinate. -/
theorem centeredMellinSpectralWeight_centeredMellinBoxApprox_even
    {ε : ℝ} (hε : 0 < ε) (z : ℂ) :
    centeredMellinSpectralWeight (centeredMellinBoxApprox ε) (-z) =
      centeredMellinSpectralWeight (centeredMellinBoxApprox ε) z := by
  rw [centeredMellinSpectralWeight_centeredMellinBoxApprox_eq_logAverage hε,
    centeredMellinSpectralWeight_centeredMellinBoxApprox_eq_logAverage hε]
  have hneg :
      (∫ t in (-ε)..ε, Complex.exp ((t : ℂ) * (-z))) =
        ∫ t in (-ε)..ε, Complex.exp ((t : ℂ) * z) := by
    have hcomp :
        (∫ t in (-ε)..ε,
          (fun t : ℝ => Complex.exp ((t : ℂ) * z)) (-t)) =
          ∫ t in (-ε)..ε, Complex.exp ((t : ℂ) * z) := by
      simpa only [neg_neg] using
        (intervalIntegral.integral_comp_neg
          (f := fun t : ℝ => Complex.exp ((t : ℂ) * z))
          (a := -ε) (b := ε))
    simpa [mul_neg, neg_mul] using hcomp
  rw [hneg]

/-- The principal Mellin second-difference box weight is an even centered
weight, including the patched `τ = 0` branch. -/
theorem centeredMellinSecondDifferenceWeight_centeredMellinBoxApprox_even
    {ε τ : ℝ} (hε : 0 < ε) :
    PascalCenteredEvenWeight
      (centeredMellinSecondDifferenceWeight
        (centeredMellinBoxApprox ε) τ) := by
  intro z
  by_cases hτ : τ = 0
  · simp [centeredMellinSecondDifferenceWeight, hτ,
      centeredMellinSpectralWeight_centeredMellinBoxApprox_even hε]
  · rw [centeredMellinSecondDifferenceWeight_eq_kernel_mul hτ,
      centeredMellinSecondDifferenceWeight_eq_kernel_mul hτ]
    have hkernel :
        (Complex.exp ((τ : ℂ) * (-z)) - 2 +
            Complex.exp (-(τ : ℂ) * (-z))) / (τ : ℂ) ^ 2 =
          (Complex.exp ((τ : ℂ) * z) - 2 +
            Complex.exp (-(τ : ℂ) * z)) / (τ : ℂ) ^ 2 := by
      congr 1
      simp only [mul_neg, neg_mul]
      ring_nf
    rw [hkernel,
      centeredMellinSpectralWeight_centeredMellinBoxApprox_even hε]

/-! ## Gate F/G: weight-only decay is a separate provider -/

/-- A provider for weight-only decay on the finite top edge.

This structure intentionally does not include the Xi logarithmic derivative.
Its existence would not by itself imply decay of the full horizontal
integrand; a uniform Xi growth bound and suitable zero-avoidance heights are
separate obligations. -/
structure PascalCenteredXiMellinWeightVerticalDecayProvider
    (ε τ σ : ℝ) where
  hε : 0 < ε
  hσ : 1 < σ
  weight_tendsto_zero : ∀ u ∈ Set.Icc (1 - σ) σ,
    Tendsto
      (fun T : ℝ => centeredMellinSecondDifferenceWeight
        (centeredMellinBoxApprox ε) τ
        (pascalOrdinaryToCentered
          (pascalSymmetricRectangleTopEdge u T)))
      atTop (𝓝 0)

/-! ## Gate H: fixed-window localization obstruction -/

/-- A zero outside the centered circle but inside the rectangle contradicts
the same-zero-set field of a transport window.  This formalizes why a fixed
`R` window cannot automatically be extended to arbitrary heights. -/
theorem not_same_zero_set_window_of_zero_outside_ball_inside_rectangle
    (W : PascalCenteredXiContourTransportWindow)
    {z : ℂ} (hz : z ∈ pascalCenteredXiZeros)
    (hzball : z ∉ Metric.ball (0 : ℂ) W.R)
    (hzrect : pascalCenteredToOrdinary z ∈
      pascalSymmetricRectangleInterior W.rectangle.σ W.rectangle.T) :
    False := by
  exact hzball ((W.zero_mem_iff z hz).mpr hzrect)

/-! ## Gate I: explicit finite-limit ledger -/

/-- The finite-window phase exposes no limit permutation.  This proposition is
only a marker for documentation and has no analytic content beyond truth. -/
def pascalCenteredXiXDP011FiniteWindowAudit : Prop := True

end DkMath.RH.CFBRCProjection
