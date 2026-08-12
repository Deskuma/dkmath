/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.PascalCenteredXiExplicitFormulaContourTransport
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Tactic

/-!
# Coordinate-safe functional-equation edge reflection

This module implements the pointwise and finite-rectangle consequences of the
fixed centered Xi functional equation.  The left edge remains a fixed-Xi
observable; only the right edge is decomposed into ordinary zeta, Gammaℝ, and
elementary terms, where `Re(s) > 1` supplies the required hypotheses.

The horizontal edges remain named contributions.  No horizontal decay,
`T → ∞` limit, rectangle deformation, residue formula, cutoff/integral
exchange, defect statement, or RH conclusion is asserted here.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open MeasureTheory
open scoped Interval Topology

/-! ## Gate A: fixed-Xi oddness -/

/-- The derivative of an even differentiable function is odd. -/
private theorem deriv_eq_neg_deriv_neg_of_even
    {f : ℂ → ℂ} (hf : ∀ z, f (-z) = f z) (z : ℂ) :
    deriv f (-z) = -deriv f z := by
  have hcomp : deriv (fun w : ℂ => f (-w)) z = -deriv f (-z) := by
    simpa using (deriv_comp_neg (f := f) z)
  have heq : (fun w : ℂ => f (-w)) = f := by
    funext w
    exact hf w
  rw [heq] at hcomp
  linear_combination hcomp

/-- The fixed centered Xi negative logarithmic derivative is odd.

The proof uses the evenness theorem for the fixed kernel and derivative
transport under negation.  It does not introduce a nonvanishing assumption,
because `logDeriv` is the totalized Mathlib operation. -/
theorem pascalCenteredXiNegLogDeriv_neg (z : ℂ) :
    pascalCenteredXiNegLogDeriv (-z) =
      -pascalCenteredXiNegLogDeriv z := by
  unfold pascalCenteredXiNegLogDeriv
  rw [logDeriv_apply, logDeriv_apply]
  rw [pascalCenteredRiemannXiKernel_neg,
    deriv_eq_neg_deriv_neg_of_even
      (fun w => pascalCenteredRiemannXiKernel_neg w) z]
  ring

/-! ## Gate C and D: centered weights and weighted oddness -/

/-- A centered weight invariant under the centered reflection. -/
def PascalCenteredEvenWeight (h : ℂ → ℂ) : Prop :=
  ∀ z, h (-z) = h z

/-- The quadratic centered weight is even. -/
theorem pascalCenteredEvenWeight_quadratic :
    PascalCenteredEvenWeight (fun z : ℂ => z ^ 2) := by
  intro z
  ring

/-- The fixed-Xi weighted logarithmic-derivative integrand. -/
def pascalCenteredXiWeightedNegLogDeriv
    (h : ℂ → ℂ) (z : ℂ) : ℂ :=
  h z * pascalCenteredXiNegLogDeriv z

/-- An even centered weight makes the fixed-Xi weighted integrand odd. -/
theorem pascalCenteredXiWeightedNegLogDeriv_neg
    {h : ℂ → ℂ} (hh : PascalCenteredEvenWeight h) (z : ℂ) :
    pascalCenteredXiWeightedNegLogDeriv h (-z) =
      -pascalCenteredXiWeightedNegLogDeriv h z := by
  simp only [pascalCenteredXiWeightedNegLogDeriv]
  rw [hh, pascalCenteredXiNegLogDeriv_neg]
  ring

/-! ## Gate B: combined decomposed observable -/

/-- The ordinary-coordinate sum supplied by the XDP-008 decomposition.

Only this combined observable is assigned to the completed functional
equation.  No individual reflection law for its three summands is asserted.
-/
def pascalXiDecomposedNegLogDeriv (s : ℂ) : ℂ :=
  pascalXiOrdinaryZetaNegLogDeriv s +
    pascalXiArchimedeanLogDeriv s +
    pascalXiElementaryLogDerivCorrection s

/-- At points where the XDP-008 factor hypotheses hold, the centered fixed-Xi
observable is the combined decomposed ordinary-coordinate observable. -/
theorem pascalCenteredXiNegLogDeriv_sub_center_eq_decomposed
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hzeta : riemannZeta s ≠ 0)
    (hGamma : Complex.Gammaℝ s ≠ 0) :
    pascalCenteredXiNegLogDeriv (pascalOrdinaryToCentered s) =
      pascalXiDecomposedNegLogDeriv s := by
  have harg : criticalLineCenter + pascalOrdinaryToCentered s = s :=
    pascalCenteredToOrdinary_pascalOrdinaryToCentered s
  have h := pascalCenteredXiNegLogDeriv_eq_zeta_add_archimedean_add_elementary
    (z := pascalOrdinaryToCentered s) (by rw [harg]; exact hs0)
    (by rw [harg]; exact hs1)
    (by rw [harg]; exact hzeta)
    (by rw [harg]; exact hGamma)
  rw [harg] at h
  exact h

/-- Wherever the XDP-008 decomposition is available at both reflected
ordinary-coordinate points, the combined decomposition inherits the fixed-Xi
functional equation.  The theorem intentionally does not split this law into
three individual termwise reflection statements. -/
theorem pascalXiDecomposedNegLogDeriv_one_sub_eq_neg
    {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hzeta : riemannZeta s ≠ 0)
    (hGamma : Complex.Gammaℝ s ≠ 0)
    (h1s0 : 1 - s ≠ 0) (h1s1 : 1 - s ≠ 1)
    (h1szeta : riemannZeta (1 - s) ≠ 0)
    (h1sGamma : Complex.Gammaℝ (1 - s) ≠ 0) :
    pascalXiDecomposedNegLogDeriv (1 - s) =
      -pascalXiDecomposedNegLogDeriv s := by
  have hleft := pascalCenteredXiNegLogDeriv_sub_center_eq_decomposed
    (s := 1 - s) h1s0 h1s1 h1szeta h1sGamma
  have hright := pascalCenteredXiNegLogDeriv_sub_center_eq_decomposed
    (s := s) hs0 hs1 hzeta hGamma
  have hcenter : pascalOrdinaryToCentered (1 - s) =
      -pascalOrdinaryToCentered s := by
    simp [pascalOrdinaryToCentered, criticalLineCenter]
    ring
  rw [← hleft, ← hright, hcenter, pascalCenteredXiNegLogDeriv_neg]

/-! ## Gate E: automatic right-edge safety -/

/-- The right edge automatically avoids the ordinary factor exceptional
locations when `1 < σ`. -/
theorem rightEdge_factor_nonzero_of_one_lt
    {σ t : ℝ} (hσ : 1 < σ) :
    let s := pascalSymmetricRectangleRightEdge σ t
    s ≠ 0 ∧ s ≠ 1 ∧ riemannZeta s ≠ 0 ∧ Complex.Gammaℝ s ≠ 0 := by
  let s := pascalSymmetricRectangleRightEdge σ t
  have hsre : 1 < s.re := one_lt_re_pascalSymmetricRectangleRightEdge hσ
  have hs0 : s ≠ 0 := by
    intro hs
    have hre := congrArg Complex.re hs
    simp at hre
    linarith
  have hs1 : s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  have hzeta : riemannZeta s ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re hsre.le
  have hGamma : Complex.Gammaℝ s ≠ 0 :=
    gammaR_ne_zero_of_pos_re (lt_trans zero_lt_one hsre)
  exact ⟨hs0, hs1, hzeta, hGamma⟩

/-- The fixed-Xi value at a right-edge point has the XDP-008 decomposition
without additional zeta/Gamma hypotheses from the caller. -/
theorem pascalCenteredXiNegLogDeriv_rightEdge_eq_decomposed
    {σ t : ℝ} (hσ : 1 < σ) :
    pascalCenteredXiNegLogDeriv
        (pascalOrdinaryToCentered
          (pascalSymmetricRectangleRightEdge σ t)) =
      pascalXiDecomposedNegLogDeriv
        (pascalSymmetricRectangleRightEdge σ t) := by
  rcases rightEdge_factor_nonzero_of_one_lt hσ with
    ⟨hs0, hs1, hzeta, hGamma⟩
  exact pascalCenteredXiNegLogDeriv_sub_center_eq_decomposed
    hs0 hs1 hzeta hGamma

/-! ## Gate F: oriented vertical edges -/

/-- The centered fixed-Xi integrand pulled back to the ordinary right edge.
-/
def pascalCenteredXiRightEdgeIntegrand
    (h : ℂ → ℂ) (σ t : ℝ) : ℂ :=
  pascalCenteredXiWeightedNegLogDeriv h
    (pascalOrdinaryToCentered (pascalSymmetricRectangleRightEdge σ t)) *
      Complex.I

/-- The centered fixed-Xi integrand pulled back to the ordinary left edge. -/
def pascalCenteredXiLeftEdgeIntegrand
    (h : ℂ → ℂ) (σ t : ℝ) : ℂ :=
  pascalCenteredXiWeightedNegLogDeriv h
    (pascalOrdinaryToCentered (pascalSymmetricRectangleLeftEdge σ t)) *
      Complex.I

/-- Reflection of the left edge, including the vertical differential factor.
-/
theorem pascalCenteredXiLeftEdgeIntegrand_eq_neg_right_comp_neg
    {h : ℂ → ℂ} (hh : PascalCenteredEvenWeight h)
    (σ t : ℝ) :
    pascalCenteredXiLeftEdgeIntegrand h σ t =
      -pascalCenteredXiRightEdgeIntegrand h σ (-t) := by
  unfold pascalCenteredXiLeftEdgeIntegrand pascalCenteredXiRightEdgeIntegrand
  have hedge := pascalOrdinaryToCentered_leftEdge_neg_eq_neg_rightEdge σ (-t)
  simp only [neg_neg] at hedge
  rw [hedge]
  rw [pascalCenteredXiWeightedNegLogDeriv_neg hh]
  ring

/-- The right vertical contribution with the XDP-009 bottom-to-top
orientation. -/
def pascalCenteredXiRightVerticalContribution
    (h : ℂ → ℂ) (W : PascalCenteredXiContourTransportWindow) : ℂ :=
  ∫ t in (-W.rectangle.T)..W.rectangle.T,
    pascalCenteredXiRightEdgeIntegrand h W.rectangle.σ t

/-- The left vertical contribution with the XDP-009 top-to-bottom
orientation. -/
def pascalCenteredXiLeftVerticalContribution
    (h : ℂ → ℂ) (W : PascalCenteredXiContourTransportWindow) : ℂ :=
  ∫ t in W.rectangle.T..(-W.rectangle.T),
    pascalCenteredXiLeftEdgeIntegrand h W.rectangle.σ t

/-! ## Gate I: horizontal terms stay explicit -/

/-- The top horizontal contribution of the centered fixed-Xi integrand. -/
def pascalCenteredXiTopHorizontalContribution
    (h : ℂ → ℂ) (W : PascalCenteredXiContourTransportWindow) : ℂ :=
  ∫ u in W.rectangle.σ..(1 - W.rectangle.σ),
    pascalCenteredXiWeightedNegLogDeriv h
      (pascalOrdinaryToCentered
        (pascalSymmetricRectangleTopEdge u W.rectangle.T))

/-- The bottom horizontal contribution of the centered fixed-Xi integrand. -/
def pascalCenteredXiBottomHorizontalContribution
    (h : ℂ → ℂ) (W : PascalCenteredXiContourTransportWindow) : ℂ :=
  ∫ u in (1 - W.rectangle.σ)..W.rectangle.σ,
    pascalCenteredXiWeightedNegLogDeriv h
      (pascalOrdinaryToCentered
        (pascalSymmetricRectangleBottomEdge u W.rectangle.T))

/-! ## Gate G: vertical pair -/

/-- The left vertical fixed-Xi contribution equals the right contribution
after affine negation and interval orientation reversal. -/
theorem pascalCenteredXiLeftVerticalContribution_eq_right
    {h : ℂ → ℂ} (hh : PascalCenteredEvenWeight h)
    (W : PascalCenteredXiContourTransportWindow) :
    pascalCenteredXiLeftVerticalContribution h W =
      pascalCenteredXiRightVerticalContribution h W := by
  unfold pascalCenteredXiLeftVerticalContribution
    pascalCenteredXiRightVerticalContribution
  rw [show (fun t => pascalCenteredXiLeftEdgeIntegrand h W.rectangle.σ t) =
      (fun t => -pascalCenteredXiRightEdgeIntegrand h W.rectangle.σ (-t)) by
        funext t
        exact pascalCenteredXiLeftEdgeIntegrand_eq_neg_right_comp_neg hh
          W.rectangle.σ t]
  rw [intervalIntegral.integral_neg]
  rw [intervalIntegral.integral_comp_neg]
  rw [intervalIntegral.integral_symm]
  simp only [neg_neg]

/-- The oriented fixed-Xi vertical pair is twice the right-edge fixed-Xi
contribution. -/
theorem pascalCenteredXiVerticalPair_eq_two_right
    {h : ℂ → ℂ} (hh : PascalCenteredEvenWeight h)
    (W : PascalCenteredXiContourTransportWindow) :
    pascalCenteredXiLeftVerticalContribution h W +
        pascalCenteredXiRightVerticalContribution h W =
      2 * pascalCenteredXiRightVerticalContribution h W := by
  rw [pascalCenteredXiLeftVerticalContribution_eq_right hh W]
  ring

/-- The right-edge fixed-Xi vertical contribution is the right-edge
decomposed observable, with no decomposition imposed on the left edge. -/
theorem pascalCenteredXiRightVerticalContribution_eq_decomposed
    (h : ℂ → ℂ) (W : PascalCenteredXiContourTransportWindow) :
    pascalCenteredXiRightVerticalContribution h W =
      ∫ t in (-W.rectangle.T)..W.rectangle.T,
        (h (pascalOrdinaryToCentered
            (pascalSymmetricRectangleRightEdge W.rectangle.σ t)) *
          pascalXiDecomposedNegLogDeriv
            (pascalSymmetricRectangleRightEdge W.rectangle.σ t)) *
          Complex.I := by
  unfold pascalCenteredXiRightVerticalContribution
  apply intervalIntegral.integral_congr
  intro t ht
  change (h (pascalOrdinaryToCentered
      (pascalSymmetricRectangleRightEdge W.rectangle.σ t)) *
      pascalCenteredXiNegLogDeriv
        (pascalOrdinaryToCentered
          (pascalSymmetricRectangleRightEdge W.rectangle.σ t))) * Complex.I = _
  rw [pascalCenteredXiNegLogDeriv_rightEdge_eq_decomposed W.rectangle.hσ]

/-- Principal XDP-010 endpoint: for an even centered weight, the oriented
fixed-Xi vertical pair is twice the right-edge decomposed observable. -/
theorem pascalCenteredXiVerticalPair_eq_two_right_decomposed
    {h : ℂ → ℂ} (hh : PascalCenteredEvenWeight h)
    (W : PascalCenteredXiContourTransportWindow) :
    pascalCenteredXiLeftVerticalContribution h W +
        pascalCenteredXiRightVerticalContribution h W =
      2 * (∫ t in (-W.rectangle.T)..W.rectangle.T,
        (h (pascalOrdinaryToCentered
            (pascalSymmetricRectangleRightEdge W.rectangle.σ t)) *
          pascalXiDecomposedNegLogDeriv
            (pascalSymmetricRectangleRightEdge W.rectangle.σ t)) *
          Complex.I) := by
  rw [pascalCenteredXiVerticalPair_eq_two_right hh W,
    pascalCenteredXiRightVerticalContribution_eq_decomposed]

end DkMath.RH.CFBRCProjection
