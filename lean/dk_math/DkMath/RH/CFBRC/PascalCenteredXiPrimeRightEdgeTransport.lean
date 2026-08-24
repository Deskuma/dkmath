/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.PascalCenteredXiFiniteRectangleResidueAssembly
import DkMath.RH.CFBRC.PascalVonMangoldtLSeriesBridge
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Tactic

/-!
# Finite prime-cutoff transport on the right edge

This module closes XDP-017.  It names the weighted finite Pascal/von Mangoldt
right-edge integrands and proves their convergence on every finite vertical
interval in the half-plane `1 < σ`.  The proof uses the absolute von Mangoldt
L-series at the real point `σ` as a majorant; Mathlib's term norm comparison
then makes that majorant independent of the height `t`.

All coordinates are explicit: `h` is evaluated at the centered point
`pascalOrdinaryToCentered s`, while the arithmetic and ordinary-zeta terms are
evaluated at the ordinary point `s`.  No `T → ∞` limit, horizontal decay,
prime-side infinite integral, residue deformation, defect statement, or RH
conclusion is asserted here.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open MeasureTheory
open scoped Interval Topology

/-! ## Gate A: named right-edge observables -/

/-- The weighted finite Pascal prime-power observable on the ordinary right edge.

The final factor `Complex.I` is the right-edge differential `ds = i dt` and
is kept inside the observable so that the resulting interval integral has the
same shape as the contour skeleton.
-/
def pascalPrimePowerRightEdgeCutoffIntegrand
    (h : ℂ → ℂ) (σ : ℝ) (X : ℕ) (t : ℝ) : ℂ :=
  (h (pascalOrdinaryToCentered
      (pascalSymmetricRectangleRightEdge σ t)) *
    pascalPrimePowerPHZFiniteUpTo X
      (pascalSymmetricRectangleRightEdge σ t)) * Complex.I

/-- The finite-interval integral of the weighted Pascal prime-power cutoff. -/
def pascalPrimePowerRightEdgeCutoffIntegral
    (h : ℂ → ℂ) (σ T : ℝ) (X : ℕ) : ℂ :=
  ∫ t in (-T)..T, pascalPrimePowerRightEdgeCutoffIntegrand h σ X t

/-- The weighted ordinary-zeta limit observable on the same right edge. -/
def pascalXiOrdinaryZetaRightEdgeIntegrand
    (h : ℂ → ℂ) (σ : ℝ) (t : ℝ) : ℂ :=
  (h (pascalOrdinaryToCentered
      (pascalSymmetricRectangleRightEdge σ t)) *
    pascalXiOrdinaryZetaNegLogDeriv
      (pascalSymmetricRectangleRightEdge σ t)) * Complex.I

/-- The finite-interval integral of the weighted ordinary-zeta right edge. -/
def pascalXiOrdinaryZetaRightEdgeIntegral
    (h : ℂ → ℂ) (σ T : ℝ) : ℂ :=
  ∫ t in (-T)..T, pascalXiOrdinaryZetaRightEdgeIntegrand h σ t

/-! ## Gate B: pointwise weighted convergence -/

/-- The weighted finite right-edge integrand converges pointwise to the
ordinary-zeta integrand.  Differentiability of the weight is not needed for
this pointwise statement.
-/
theorem tendsto_pascalPrimePowerRightEdgeCutoffIntegrand
    {h : ℂ → ℂ} {σ t : ℝ} (hσ : 1 < σ) :
    Tendsto (fun X => pascalPrimePowerRightEdgeCutoffIntegrand h σ X t) atTop
      (nhds (pascalXiOrdinaryZetaRightEdgeIntegrand h σ t)) := by
  have hpoint :=
    tendsto_pascalPrimePowerPHZFiniteUpTo_pascalXiOrdinaryZetaNegLogDeriv_rightEdge
      (σ := σ) (t := t) hσ
  change Tendsto
    (fun X =>
      (h (pascalOrdinaryToCentered
        (pascalSymmetricRectangleRightEdge σ t)) *
        pascalPrimePowerPHZFiniteUpTo X
          (pascalSymmetricRectangleRightEdge σ t)) * Complex.I) atTop
    (nhds ((h (pascalOrdinaryToCentered
      (pascalSymmetricRectangleRightEdge σ t)) *
      pascalXiOrdinaryZetaNegLogDeriv
        (pascalSymmetricRectangleRightEdge σ t)) * Complex.I))
  exact ((tendsto_const_nhds.mul hpoint).mul_const _)

/-! ## Gate C: the vertical absolute majorant -/

private abbrev pascalVonMangoldtCoeff : ℕ → ℂ :=
  fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)

/-- The real-axis absolute von Mangoldt L-series, used as a vertical-line
majorant for every finite cutoff.
-/
def pascalVonMangoldtVerticalMajorant (σ : ℝ) : ℝ :=
  ∑' n : ℕ, ‖LSeries.term pascalVonMangoldtCoeff (σ : ℂ) n‖

/-- Every von Mangoldt L-series term has the same norm at a vertical point and
at the real point with the same real part.  The `n = 0` case is handled by the
totalized L-series term and does not inspect a zero base of `Complex.cpow`.
-/
theorem norm_pascalVonMangoldt_LSeries_term_rightEdge_eq
    (σ t : ℝ) (n : ℕ) :
    ‖LSeries.term pascalVonMangoldtCoeff
        (pascalSymmetricRectangleRightEdge σ t) n‖ =
      ‖LSeries.term pascalVonMangoldtCoeff (σ : ℂ) n‖ := by
  apply le_antisymm
  · apply LSeries.norm_term_le_of_re_le_re pascalVonMangoldtCoeff
    simp [pascalSymmetricRectangleRightEdge]
  · apply LSeries.norm_term_le_of_re_le_re pascalVonMangoldtCoeff
    simp [pascalSymmetricRectangleRightEdge]

/-- The majorant series is summable in the safe half-plane. -/
theorem summable_pascalVonMangoldtVerticalMajorant
    {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ =>
      ‖LSeries.term pascalVonMangoldtCoeff (σ : ℂ) n‖) := by
  exact (ArithmeticFunction.LSeriesSummable_vonMangoldt
    (s := (σ : ℂ)) (by simpa using hσ)).norm

/-- The finite Pascal cutoff is uniformly bounded in both its cutoff and its
vertical height by the real-axis absolute von Mangoldt series.

This is the load-bearing finite majorant for the interval dominated-convergence
argument below.  It is an `X,t`-independent bound, not an assertion about an
infinite prime-side integral.
-/
theorem norm_pascalPrimePowerPHZFiniteUpTo_rightEdge_le_verticalMajorant
    {σ : ℝ} (hσ : 1 < σ) (X : ℕ) (t : ℝ) :
    ‖pascalPrimePowerPHZFiniteUpTo X
        (pascalSymmetricRectangleRightEdge σ t)‖ ≤
      pascalVonMangoldtVerticalMajorant σ := by
  have hsum := summable_pascalVonMangoldtVerticalMajorant hσ
  calc
    ‖pascalPrimePowerPHZFiniteUpTo X
        (pascalSymmetricRectangleRightEdge σ t)‖ =
        ‖∑ n ∈ Finset.range (X + 1),
          LSeries.term pascalVonMangoldtCoeff
            (pascalSymmetricRectangleRightEdge σ t) n‖ := by
      rw [pascalPrimePowerPHZFiniteUpTo_eq_LSeries_partialSum]
    _ ≤ ∑ n ∈ Finset.range (X + 1),
        ‖LSeries.term pascalVonMangoldtCoeff
          (pascalSymmetricRectangleRightEdge σ t) n‖ := by
      exact norm_sum_le _ _
    _ = ∑ n ∈ Finset.range (X + 1),
        ‖LSeries.term pascalVonMangoldtCoeff (σ : ℂ) n‖ := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [norm_pascalVonMangoldt_LSeries_term_rightEdge_eq]
    _ ≤ ∑' n : ℕ, ‖LSeries.term pascalVonMangoldtCoeff (σ : ℂ) n‖ := by
      exact hsum.sum_le_tsum _ (fun n hn => norm_nonneg _)

/-! ## Gate D: continuity and finite-interval domination -/

private theorem continuous_pascalOrdinaryRightEdge (σ : ℝ) :
    Continuous (fun t : ℝ =>
      pascalSymmetricRectangleRightEdge σ t) := by
  change Continuous (fun t : ℝ => (σ : ℂ) + (t : ℂ) * Complex.I)
  fun_prop

private theorem continuous_pascalCenteredRightEdgeWeight
    {h : ℂ → ℂ} (hh : Differentiable ℂ h) (σ : ℝ) :
    Continuous (fun t : ℝ =>
      h (pascalOrdinaryToCentered
        (pascalSymmetricRectangleRightEdge σ t))) := by
  apply hh.continuous.comp
  change Continuous (fun t : ℝ =>
    pascalSymmetricRectangleRightEdge σ t - criticalLineCenter)
  convert (continuous_pascalOrdinaryRightEdge σ).sub continuous_const using 1
  all_goals (ext t; rfl)

private theorem continuous_pascalPrimePowerRightEdgeCutoffIntegrand
    {h : ℂ → ℂ} (hh : Differentiable ℂ h) (σ : ℝ) (X : ℕ) :
    Continuous (fun t : ℝ =>
      pascalPrimePowerRightEdgeCutoffIntegrand h σ X t) := by
  have hpath := continuous_pascalOrdinaryRightEdge σ
  have hweight := continuous_pascalCenteredRightEdgeWeight hh σ
  have hterm : ∀ n : ℕ, Continuous (fun t : ℝ =>
      LSeries.term pascalVonMangoldtCoeff
        (pascalSymmetricRectangleRightEdge σ t) n) := by
    intro n
    by_cases hn : n = 0
    · subst n
      have hz : (fun t : ℝ =>
          LSeries.term pascalVonMangoldtCoeff
            (pascalSymmetricRectangleRightEdge σ t) 0) =
        (fun _ : ℝ => 0) := by
          funext t
          rw [vonMangoldt_LSeries_term_eq]
          simp
      rw [hz]
      exact continuous_const
    · let : NeZero (n : ℂ) := ⟨by
        exact_mod_cast hn⟩
      have hnterm : (fun t : ℝ =>
          LSeries.term pascalVonMangoldtCoeff
            (pascalSymmetricRectangleRightEdge σ t) n) =
        (fun t : ℝ =>
          pascalVonMangoldtCoeff n *
            ((n : ℂ) ^
              (-(pascalSymmetricRectangleRightEdge σ t)))) := by
        funext t
        rw [vonMangoldt_LSeries_term_eq]
      rw [hnterm]
      convert continuous_const.mul
          ((continuous_const_cpow (n : ℂ)).comp
            (continuous_neg.comp hpath)) using 1
      all_goals (ext t; rfl)
  have hsum : Continuous (fun t : ℝ =>
      ∑ n ∈ Finset.range (X + 1),
        LSeries.term pascalVonMangoldtCoeff
          (pascalSymmetricRectangleRightEdge σ t) n) := by
    apply continuous_finsetSum
    intro n hn
    exact hterm n
  change Continuous (fun t : ℝ =>
    (h (pascalOrdinaryToCentered
      (pascalSymmetricRectangleRightEdge σ t)) *
      pascalPrimePowerPHZFiniteUpTo X
        (pascalSymmetricRectangleRightEdge σ t)) * Complex.I)
  have hphz : Continuous (fun t : ℝ =>
      pascalPrimePowerPHZFiniteUpTo X
        (pascalSymmetricRectangleRightEdge σ t)) := by
    have heq : (fun t : ℝ => pascalPrimePowerPHZFiniteUpTo X
        (pascalSymmetricRectangleRightEdge σ t)) =
        (fun t : ℝ => ∑ n ∈ Finset.range (X + 1),
          LSeries.term pascalVonMangoldtCoeff
            (pascalSymmetricRectangleRightEdge σ t) n) := by
      funext t
      exact pascalPrimePowerPHZFiniteUpTo_eq_LSeries_partialSum X _
    rw [heq]
    exact hsum
  exact (hweight.mul hphz).mul continuous_const

private theorem pascalRightEdgeCutoff_norm_le_majorant
    {h : ℂ → ℂ} {σ : ℝ} (hσ : 1 < σ) (X : ℕ) (t : ℝ) :
    ‖pascalPrimePowerRightEdgeCutoffIntegrand h σ X t‖ ≤
      ‖h (pascalOrdinaryToCentered
        (pascalSymmetricRectangleRightEdge σ t))‖ *
        pascalVonMangoldtVerticalMajorant σ := by
  calc
    ‖pascalPrimePowerRightEdgeCutoffIntegrand h σ X t‖ =
        ‖h (pascalOrdinaryToCentered
          (pascalSymmetricRectangleRightEdge σ t))‖ *
          ‖pascalPrimePowerPHZFiniteUpTo X
            (pascalSymmetricRectangleRightEdge σ t)‖ * ‖Complex.I‖ := by
      rw [pascalPrimePowerRightEdgeCutoffIntegrand, norm_mul, norm_mul]
    _ = ‖h (pascalOrdinaryToCentered
          (pascalSymmetricRectangleRightEdge σ t))‖ *
          ‖pascalPrimePowerPHZFiniteUpTo X
            (pascalSymmetricRectangleRightEdge σ t)‖ := by
      norm_num
    _ ≤ ‖h (pascalOrdinaryToCentered
          (pascalSymmetricRectangleRightEdge σ t))‖ *
          pascalVonMangoldtVerticalMajorant σ := by
      exact mul_le_mul_of_nonneg_left
        (norm_pascalPrimePowerPHZFiniteUpTo_rightEdge_le_verticalMajorant hσ X t)
        (norm_nonneg _)

/-- The ordinary-zeta right-edge limit integrand is interval-integrable.

This companion to the cutoff convergence theorem records the limit-side
integrability supplied by the same finite-interval dominated-convergence data.
It is proved by taking the almost-everywhere measurable pointwise limit and
using the majorant with `IntervalIntegrable.mono_fun'`; interval integrals are
therefore never treated as integrable merely because they are totalized.
-/
theorem intervalIntegrable_pascalXiOrdinaryZetaRightEdgeIntegrand
    {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    {σ T : ℝ} (hσ : 1 < σ) :
    IntervalIntegrable
      (pascalXiOrdinaryZetaRightEdgeIntegrand h σ)
      volume (-T) T := by
  let bound : ℝ → ℝ := fun t =>
    ‖h (pascalOrdinaryToCentered
      (pascalSymmetricRectangleRightEdge σ t))‖ *
      pascalVonMangoldtVerticalMajorant σ
  have hbound : IntervalIntegrable bound volume (-T) T := by
    apply (continuous_pascalCenteredRightEdgeWeight hh σ).norm.mul
      continuous_const |>.intervalIntegrable
  let μ : Measure ℝ := volume.restrict (Ι (-T) T)
  have hmeas : ∀ X : ℕ,
      AEStronglyMeasurable
        (fun t : ℝ => pascalPrimePowerRightEdgeCutoffIntegrand h σ X t) μ := by
    intro X
    exact (continuous_pascalPrimePowerRightEdgeCutoffIntegrand hh σ X).aestronglyMeasurable
  have hlim : ∀ᵐ t : ℝ ∂μ,
      Tendsto (fun X => pascalPrimePowerRightEdgeCutoffIntegrand h σ X t) atTop
        (nhds (pascalXiOrdinaryZetaRightEdgeIntegrand h σ t)) := by
    filter_upwards [] with t
    exact tendsto_pascalPrimePowerRightEdgeCutoffIntegrand hσ
  have htarget : AEStronglyMeasurable
      (pascalXiOrdinaryZetaRightEdgeIntegrand h σ) μ := by
    exact aestronglyMeasurable_of_tendsto_ae atTop hmeas hlim
  have hnorm : ∀ᵐ t : ℝ ∂μ,
      ‖pascalXiOrdinaryZetaRightEdgeIntegrand h σ t‖ ≤ bound t := by
    filter_upwards [] with t
    apply le_of_tendsto
      (tendsto_norm.comp (tendsto_pascalPrimePowerRightEdgeCutoffIntegrand hσ))
    exact Eventually.of_forall fun X =>
      pascalRightEdgeCutoff_norm_le_majorant hσ X t
  exact hbound.mono_fun' htarget hnorm

/-! ## Gate E: finite interval dominated convergence -/

/-- Finite right-edge cutoff integrals converge to the ordinary-zeta right-edge
integral.  The proof explicitly invokes the pinned interval-integral dominated
convergence theorem; pointwise convergence is not used as an integral rewrite.
-/
theorem tendsto_pascalPrimePowerRightEdgeCutoffIntegral
    {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    {σ T : ℝ} (hσ : 1 < σ) :
    Tendsto
      (fun X => pascalPrimePowerRightEdgeCutoffIntegral h σ T X)
      atTop
      (nhds (pascalXiOrdinaryZetaRightEdgeIntegral h σ T)) := by
  let bound : ℝ → ℝ := fun t =>
    ‖h (pascalOrdinaryToCentered
      (pascalSymmetricRectangleRightEdge σ t))‖ *
      pascalVonMangoldtVerticalMajorant σ
  have hbound : IntervalIntegrable bound volume (-T) T := by
    apply (continuous_pascalCenteredRightEdgeWeight hh σ).norm.mul
      continuous_const |>.intervalIntegrable
  have hmeas : ∀ᶠ X : ℕ in atTop,
      AEStronglyMeasurable
        (fun t : ℝ => pascalPrimePowerRightEdgeCutoffIntegrand h σ X t)
        (volume.restrict (Ι (-T) T)) := by
    filter_upwards [] with X
    exact (continuous_pascalPrimePowerRightEdgeCutoffIntegrand hh σ X).aestronglyMeasurable
  have hdom : ∀ᶠ X : ℕ in atTop, ∀ᵐ t : ℝ ∂volume,
      t ∈ Ι (-T) T →
        ‖pascalPrimePowerRightEdgeCutoffIntegrand h σ X t‖ ≤ bound t := by
    filter_upwards [] with X
    filter_upwards [] with t
    intro ht
    exact pascalRightEdgeCutoff_norm_le_majorant hσ X t
  have hlim : ∀ᵐ t : ℝ ∂volume, t ∈ Ι (-T) T →
      Tendsto (fun X => pascalPrimePowerRightEdgeCutoffIntegrand h σ X t) atTop
        (nhds (pascalXiOrdinaryZetaRightEdgeIntegrand h σ t)) := by
    filter_upwards [] with t
    intro ht
    exact tendsto_pascalPrimePowerRightEdgeCutoffIntegrand hσ
  exact intervalIntegral.tendsto_integral_filter_of_dominated_convergence bound
    hmeas hdom hbound hlim

/-! ## Gate F: finite arithmetic expansion -/

/-- The finite right-edge integral is a finite von Mangoldt sum of weighted
oscillatory kernels.  The complex `cpow` form is retained, so no branch or
trigonometric expansion is hidden in this transport theorem.
-/
theorem pascalPrimePowerRightEdgeCutoffIntegral_eq_vonMangoldt_sum
    {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    (σ T : ℝ) (X : ℕ) :
    pascalPrimePowerRightEdgeCutoffIntegral h σ T X =
      ∑ n ∈ Finset.range (X + 1),
        ∫ t in (-T)..T,
          (h (pascalOrdinaryToCentered
            (pascalSymmetricRectangleRightEdge σ t)) *
            ((ArithmeticFunction.vonMangoldt n : ℂ) *
              ((n : ℂ) ^
                (-(pascalSymmetricRectangleRightEdge σ t)))) * Complex.I) := by
  let F : ℕ → ℝ → ℂ := fun n t =>
    (h (pascalOrdinaryToCentered
      (pascalSymmetricRectangleRightEdge σ t)) *
      ((ArithmeticFunction.vonMangoldt n : ℂ) *
        ((n : ℂ) ^
          (-(pascalSymmetricRectangleRightEdge σ t)))) * Complex.I)
  have hF : ∀ n ∈ Finset.range (X + 1),
      IntervalIntegrable (F n) volume (-T) T := by
    intro n hn
    by_cases hn0 : n = 0
    · subst n
      have hz : F 0 = fun _ : ℝ => 0 := by
        funext t
        simp [F]
      rw [hz]
      exact intervalIntegrable_const (μ := volume) (a := -T) (b := T)
    · let : NeZero (n : ℂ) := ⟨by exact_mod_cast hn0⟩
      have hpath := continuous_pascalOrdinaryRightEdge σ
      have hweight := continuous_pascalCenteredRightEdgeWeight hh σ
      have hpow := (continuous_const_cpow (n : ℂ)).comp
        (continuous_neg.comp hpath)
      have hc : Continuous (F n) := by
        dsimp [F]
        exact ((hweight.mul (continuous_const.mul hpow)).mul continuous_const)
      exact hc.intervalIntegrable _ _
  have hpoint : (fun t : ℝ =>
      pascalPrimePowerRightEdgeCutoffIntegrand h σ X t) =
      (fun t : ℝ => ∑ n ∈ Finset.range (X + 1), F n t) := by
    funext t
    dsimp [pascalPrimePowerRightEdgeCutoffIntegrand, F]
    rw [pascalPrimePowerPHZFiniteUpTo_eq_vonMangoldt_sum]
    simp_rw [Finset.mul_sum, Finset.sum_mul]
  unfold pascalPrimePowerRightEdgeCutoffIntegral
  rw [hpoint, intervalIntegral.integral_finsetSum hF]

/-! ## Gate G: residue-window adapter -/

/-- The principal finite-cutoff integral transport specialized to an XDP-016
residue window.  Its target is syntactically the ordinary-zeta component of
the finite explicit-formula right edge.
-/
theorem tendsto_pascalPrimePowerRightEdgeCutoffIntegral_of_residueTransportWindow
    {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    (W : PascalCenteredXiResidueTransportWindow) :
    Tendsto
      (fun X => pascalPrimePowerRightEdgeCutoffIntegral h
        W.rectangle.σ W.rectangle.T X)
      atTop
      (nhds (pascalXiOrdinaryZetaRightEdgeIntegral h
        W.rectangle.σ W.rectangle.T)) := by
  exact tendsto_pascalPrimePowerRightEdgeCutoffIntegral hh W.rectangle.hσ

/-! ## Gate H boundary -/

/-
Mathematical boundary recorded for XDP-017: splitting the complete decomposed
right-edge integral into ordinary-zeta, archimedean, and elementary integrals
requires separate finite-interval integrability contracts for the latter two
terms.  That is the explicitly optional XDP-018 follow-up; this module only
transports the ordinary-zeta component and does not claim the split.
-/

end DkMath.RH.CFBRCProjection
