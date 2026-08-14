/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideFiniteSourceCancellationAudit
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Tactic

/-!
# CS11: finite signed prime-tail pairing audit

This module makes the remaining finite prime-side residual explicit as a
signed vertical pairing.  Every identity here is on a finite cutoff and a
finite symmetric interval.  In particular, this module does not exchange an
infinite prime tail with an integral and does not provide a fixed-ε sign
theorem or an RH consequence.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.Analysis
open Filter
open MeasureTheory
open scoped Interval Topology

/-! ## CS11-A: raw finite residual -/

/-- The un-oriented finite prime-minus-zeta amplitude on the right edge. -/
noncomputable def pascalCenteredXiPrimeSideFiniteCutoffRawDifference
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (X : ℕ) (t : ℝ) : ℂ :=
  pascalCenteredXiMellinSecondDifferenceWeight ε 0
      (pascalOrdinaryToCentered
        (pascalSymmetricRectangleRightEdge W.rectangle.σ t)) *
    (pascalPrimePowerPHZFiniteUpTo X
        (pascalSymmetricRectangleRightEdge W.rectangle.σ t) -
      pascalXiOrdinaryZetaNegLogDeriv
        (pascalSymmetricRectangleRightEdge W.rectangle.σ t))

private theorem intervalIntegrable_pascalPrimePowerRightEdgeCutoffIntegrand
    {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    {σ T : ℝ} (X : ℕ) :
    IntervalIntegrable
      (pascalPrimePowerRightEdgeCutoffIntegrand h σ X)
      volume (-T) T := by
  have hpath : Continuous (fun t : ℝ =>
      pascalSymmetricRectangleRightEdge σ t) := by
    change Continuous (fun t : ℝ => (σ : ℂ) + (t : ℂ) * Complex.I)
    fun_prop
  have hweight : Continuous (fun t : ℝ =>
      h (pascalOrdinaryToCentered
        (pascalSymmetricRectangleRightEdge σ t))) := by
    apply hh.continuous.comp
    change Continuous (fun t : ℝ =>
      pascalSymmetricRectangleRightEdge σ t - criticalLineCenter)
    convert hpath.sub continuous_const using 1
    all_goals ext t; rfl
  have hterm : ∀ n : ℕ, Continuous (fun t : ℝ =>
      LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ))
        (pascalSymmetricRectangleRightEdge σ t) n) := by
    intro n
    by_cases hn : n = 0
    · subst n
      have hz : (fun t : ℝ =>
          LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ))
            (pascalSymmetricRectangleRightEdge σ t) 0) =
        (fun _ : ℝ => 0) := by
        funext t
        rw [vonMangoldt_LSeries_term_eq]
        simp
      rw [hz]
      exact continuous_const
    · letI : NeZero (n : ℂ) := ⟨by exact_mod_cast hn⟩
      have hnterm : (fun t : ℝ =>
          LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ))
            (pascalSymmetricRectangleRightEdge σ t) n) =
        (fun t : ℝ =>
          (ArithmeticFunction.vonMangoldt n : ℂ) *
            ((n : ℂ) ^ (-(pascalSymmetricRectangleRightEdge σ t)))) := by
        funext t
        rw [vonMangoldt_LSeries_term_eq]
      rw [hnterm]
      convert continuous_const.mul
          ((continuous_const_cpow (n : ℂ)).comp
            (continuous_neg.comp hpath)) using 1
      all_goals ext t; rfl
  have hsum : Continuous (fun t : ℝ =>
      ∑ n ∈ Finset.range (X + 1),
        LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ))
          (pascalSymmetricRectangleRightEdge σ t) n) := by
    apply continuous_finsetSum
    intro n hn
    exact hterm n
  have hphz : Continuous (fun t : ℝ =>
      pascalPrimePowerPHZFiniteUpTo X
        (pascalSymmetricRectangleRightEdge σ t)) := by
    have heq : (fun t : ℝ => pascalPrimePowerPHZFiniteUpTo X
        (pascalSymmetricRectangleRightEdge σ t)) =
        (fun t : ℝ => ∑ n ∈ Finset.range (X + 1),
          LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ))
            (pascalSymmetricRectangleRightEdge σ t) n) := by
      funext t
      exact pascalPrimePowerPHZFiniteUpTo_eq_LSeries_partialSum X _
    rw [heq]
    exact hsum
  have hcont : Continuous (fun t : ℝ =>
    (h (pascalOrdinaryToCentered
      (pascalSymmetricRectangleRightEdge σ t)) *
      pascalPrimePowerPHZFiniteUpTo X
        (pascalSymmetricRectangleRightEdge σ t)) * Complex.I) :=
    (hweight.mul hphz).mul continuous_const
  change IntervalIntegrable (fun t : ℝ =>
    (h (pascalOrdinaryToCentered
      (pascalSymmetricRectangleRightEdge σ t)) *
      pascalPrimePowerPHZFiniteUpTo X
        (pascalSymmetricRectangleRightEdge σ t)) * Complex.I) volume (-T) T
  exact hcont.intervalIntegrable (μ := (volume : Measure ℝ)) (-T) T

theorem pascalCenteredXiPrimeSideFiniteCutoffResidual_eq_integral_rawDifference
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiPrimeSideFiniteCutoffResidual ε W X =
      ∫ t in (-W.rectangle.T)..W.rectangle.T,
        pascalCenteredXiPrimeSideFiniteCutoffRawDifference ε W X t * Complex.I := by
  rw [pascalCenteredXiPrimeSideFiniteCutoffResidual,
    pascalCenteredXiPrimeSideQuadraticizationPrimeModeSum_eq_cutoffIntegral hε]
  have hcut := intervalIntegrable_pascalPrimePowerRightEdgeCutoffIntegrand
    (h := pascalCenteredXiMellinSecondDifferenceWeight ε 0)
    (pascalCenteredXiMellinSecondDifferenceWeight_differentiable
      (ε := ε) (τ := 0) hε)
    (σ := W.rectangle.σ) (T := W.rectangle.T) X
  have hzeta := intervalIntegrable_pascalXiOrdinaryZetaRightEdgeIntegrand_of_residueWindow
    (h := pascalCenteredXiMellinSecondDifferenceWeight ε 0)
    (pascalCenteredXiMellinSecondDifferenceWeight_differentiable
      (ε := ε) (τ := 0) hε) W
  calc
    pascalPrimePowerRightEdgeCutoffIntegral
          (pascalCenteredXiMellinSecondDifferenceWeight ε 0)
          W.rectangle.σ W.rectangle.T X -
        pascalXiOrdinaryZetaRightEdgeIntegral
          (pascalCenteredXiMellinSecondDifferenceWeight ε 0)
          W.rectangle.σ W.rectangle.T =
      ∫ t in (-W.rectangle.T)..W.rectangle.T,
        (pascalPrimePowerRightEdgeCutoffIntegrand
          (pascalCenteredXiMellinSecondDifferenceWeight ε 0)
          W.rectangle.σ X t -
          pascalXiOrdinaryZetaRightEdgeIntegrand
            (pascalCenteredXiMellinSecondDifferenceWeight ε 0)
            W.rectangle.σ t) := by
          unfold pascalPrimePowerRightEdgeCutoffIntegral
            pascalXiOrdinaryZetaRightEdgeIntegral
          rw [intervalIntegral.integral_sub hcut hzeta]
    _ = ∫ t in (-W.rectangle.T)..W.rectangle.T,
        pascalCenteredXiPrimeSideFiniteCutoffRawDifference ε W X t * Complex.I := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [] with t ht
          simp only [pascalPrimePowerRightEdgeCutoffIntegrand,
            pascalXiOrdinaryZetaRightEdgeIntegrand,
            pascalCenteredXiPrimeSideFiniteCutoffRawDifference]
          ring

/-! ## CS11-B/C: conjugation contracts -/

private theorem pascalCenteredXiMellinQuadraticMultiplier_conj
    {ε : ℝ} (hε : 0 < ε) (z : ℂ) :
    mellinQuadraticBoxMultiplier ε (starRingEnd ℂ z) =
      starRingEnd ℂ (mellinQuadraticBoxMultiplier ε z) := by
  rw [mellinQuadraticBoxMultiplier_eq_logAverage hε,
    mellinQuadraticBoxMultiplier_eq_logAverage hε]
  have hscale : starRingEnd ℂ ((2 * ε : ℝ)⁻¹ : ℂ) =
      ((2 * ε : ℝ)⁻¹ : ℂ) := by
    have htwo : starRingEnd ℂ (2 : ℂ) = 2 := by
      simp only [map_ofNat]
    simp [map_inv₀, htwo, Complex.ofReal_mul]
  calc
    ((2 * ε : ℝ)⁻¹ : ℂ) *
        (∫ t in (-ε)..ε, Complex.exp ((t : ℂ) * starRingEnd ℂ z)) =
      ((2 * ε : ℝ)⁻¹ : ℂ) *
        (∫ t in (-ε)..ε,
          starRingEnd ℂ (Complex.exp ((t : ℂ) * z))) := by
            congr 1
            apply intervalIntegral.integral_congr_ae
            filter_upwards [] with t ht
            rw [← Complex.exp_conj]
            congr 1
            simp
    _ = ((2 * ε : ℝ)⁻¹ : ℂ) *
        starRingEnd ℂ (∫ t in (-ε)..ε, Complex.exp ((t : ℂ) * z)) := by
          rw [intervalIntegral.intervalIntegral_conj]
    _ = starRingEnd ℂ
        (((2 * ε : ℝ)⁻¹ : ℂ) *
          (∫ t in (-ε)..ε, Complex.exp ((t : ℂ) * z))) := by
          rw [map_mul, hscale]

private theorem pascalCenteredXiMellinSecondDifferenceWeight_conj
    {ε : ℝ} (hε : 0 < ε) (z : ℂ) :
    pascalCenteredXiMellinSecondDifferenceWeight ε 0 (starRingEnd ℂ z) =
      starRingEnd ℂ
        (pascalCenteredXiMellinSecondDifferenceWeight ε 0 z) := by
  rw [pascalCenteredXiMellinQuadraticWeight_eq_generic hε,
    pascalCenteredXiMellinQuadraticWeight_eq_generic hε]
  unfold mellinQuadraticBoxWeight
  rw [map_mul, map_pow, pascalCenteredXiMellinQuadraticMultiplier_conj hε]

private theorem pascalXiOrdinaryZetaNegLogDeriv_conj (s : ℂ) :
    pascalXiOrdinaryZetaNegLogDeriv (starRingEnd ℂ s) =
      starRingEnd ℂ (pascalXiOrdinaryZetaNegLogDeriv s) := by
  have hfun : (starRingEnd ℂ) ∘ riemannZeta ∘ (starRingEnd ℂ) =
      riemannZeta := by
    funext z
    simp [Function.comp_def, riemannZeta_conj]
  have hderiv := congrFun (deriv_conj_conj (f := riemannZeta))
    (starRingEnd ℂ s)
  have hderiv' : deriv riemannZeta (starRingEnd ℂ s) =
      starRingEnd ℂ (deriv riemannZeta s) := by
    rw [← hfun] at hderiv
    simpa [Function.comp_def] using hderiv
  unfold pascalXiOrdinaryZetaNegLogDeriv
  rw [hderiv', riemannZeta_conj]
  simp

theorem pascalCenteredXiPrimeSideFiniteCutoffRawDifference_neg_eq_conj
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) (t : ℝ) :
    pascalCenteredXiPrimeSideFiniteCutoffRawDifference ε W X (-t) =
      starRingEnd ℂ
        (pascalCenteredXiPrimeSideFiniteCutoffRawDifference ε W X t) := by
  unfold pascalCenteredXiPrimeSideFiniteCutoffRawDifference
  have hs : pascalSymmetricRectangleRightEdge W.rectangle.σ (-t) =
      starRingEnd ℂ (pascalSymmetricRectangleRightEdge W.rectangle.σ t) := by
    apply Complex.ext <;>
      simp [pascalSymmetricRectangleRightEdge]
  have hz : pascalOrdinaryToCentered
      (pascalSymmetricRectangleRightEdge W.rectangle.σ (-t)) =
      starRingEnd ℂ (pascalOrdinaryToCentered
        (pascalSymmetricRectangleRightEdge W.rectangle.σ t)) := by
    rw [hs]
    have htwo : starRingEnd ℂ (2 : ℂ) = 2 := by
      simp only [map_ofNat]
    simp [pascalOrdinaryToCentered, criticalLineCenter, htwo]
  rw [hz, hs, pascalCenteredXiMellinSecondDifferenceWeight_conj hε,
    pascalPrimePowerPHZFiniteUpTo_conj,
    pascalXiOrdinaryZetaNegLogDeriv_conj]
  simp only [map_sub, map_mul]

/-! ## CS11-D: anti-conjugate oriented integrand -/

theorem pascalCenteredXiPrimeSideFiniteCutoffOrientedIntegrand_neg_eq_neg_conj
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) (t : ℝ) :
    pascalCenteredXiPrimeSideFiniteCutoffRawDifference ε W X (-t) * Complex.I =
      -starRingEnd ℂ
        (pascalCenteredXiPrimeSideFiniteCutoffRawDifference ε W X t * Complex.I) := by
  rw [pascalCenteredXiPrimeSideFiniteCutoffRawDifference_neg_eq_conj hε W X t]
  simp [map_mul]

/-! ## CS11-E: signed half-interval projection -/

theorem pascalCenteredXiPrimeSideFiniteCutoffResidual_re_eq_zero
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    (pascalCenteredXiPrimeSideFiniteCutoffResidual ε W X).re = 0 := by
  rw [pascalCenteredXiPrimeSideFiniteCutoffResidual_eq_integral_rawDifference hε W X]
  have hanti : ∀ t : ℝ,
      pascalCenteredXiPrimeSideFiniteCutoffRawDifference ε W X (-t) * Complex.I =
        -starRingEnd ℂ
          (pascalCenteredXiPrimeSideFiniteCutoffRawDifference ε W X t * Complex.I) :=
    fun t => pascalCenteredXiPrimeSideFiniteCutoffOrientedIntegrand_neg_eq_neg_conj
      hε W X t
  have hsym :
      (∫ t in (-W.rectangle.T)..W.rectangle.T,
        pascalCenteredXiPrimeSideFiniteCutoffRawDifference ε W X t * Complex.I) =
        -starRingEnd ℂ
          (∫ t in (-W.rectangle.T)..W.rectangle.T,
            pascalCenteredXiPrimeSideFiniteCutoffRawDifference ε W X t * Complex.I) := by
    let f : ℝ → ℂ := fun t =>
      pascalCenteredXiPrimeSideFiniteCutoffRawDifference ε W X t * Complex.I
    change (∫ t in (-W.rectangle.T)..W.rectangle.T, f t) =
      -starRingEnd ℂ (∫ t in (-W.rectangle.T)..W.rectangle.T, f t)
    calc
      (∫ t in (-W.rectangle.T)..W.rectangle.T, f t) =
          ∫ t in (-W.rectangle.T)..W.rectangle.T, f (-t) := by
            symm
            simpa only [neg_neg] using
              (intervalIntegral.integral_comp_neg (f := f)
                (a := -W.rectangle.T) (b := W.rectangle.T))
      _ = ∫ t in (-W.rectangle.T)..W.rectangle.T,
          -starRingEnd ℂ (f t) := by
            apply intervalIntegral.integral_congr_ae
            filter_upwards [] with t ht
            exact hanti t
      _ = -starRingEnd ℂ
          (∫ t in (-W.rectangle.T)..W.rectangle.T, f t) := by
            rw [intervalIntegral.integral_neg,
              intervalIntegral.intervalIntegral_conj]
  have hre := congrArg Complex.re hsym
  change (∫ t in (-W.rectangle.T)..W.rectangle.T,
      pascalCenteredXiPrimeSideFiniteCutoffRawDifference ε W X t * Complex.I).re = 0
  change (∫ t in (-W.rectangle.T)..W.rectangle.T,
      pascalCenteredXiPrimeSideFiniteCutoffRawDifference ε W X t * Complex.I).re =
    -(∫ t in (-W.rectangle.T)..W.rectangle.T,
      pascalCenteredXiPrimeSideFiniteCutoffRawDifference ε W X t * Complex.I).re at hre
  linarith

theorem pascalCenteredXiPrimeSideFiniteCutoffResidual_im_eq_two_mul_half_re
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    (pascalCenteredXiPrimeSideFiniteCutoffResidual ε W X).im =
      2 * ∫ t in (0 : ℝ)..W.rectangle.T,
        (pascalCenteredXiPrimeSideFiniteCutoffRawDifference ε W X t).re := by
  let g : ℝ → ℂ := fun t =>
    pascalCenteredXiPrimeSideFiniteCutoffRawDifference ε W X t * Complex.I
  have hcut := intervalIntegrable_pascalPrimePowerRightEdgeCutoffIntegrand
    (h := pascalCenteredXiMellinSecondDifferenceWeight ε 0)
    (pascalCenteredXiMellinSecondDifferenceWeight_differentiable
      (ε := ε) (τ := 0) hε)
    (σ := W.rectangle.σ) (T := W.rectangle.T) X
  have hzeta := intervalIntegrable_pascalXiOrdinaryZetaRightEdgeIntegrand_of_residueWindow
    (h := pascalCenteredXiMellinSecondDifferenceWeight ε 0)
    (pascalCenteredXiMellinSecondDifferenceWeight_differentiable
      (ε := ε) (τ := 0) hε) W
  have hgi : IntervalIntegrable g volume (-W.rectangle.T) W.rectangle.T := by
    apply (hcut.sub hzeta).congr
    intro t ht
    simp only [g, pascalPrimePowerRightEdgeCutoffIntegrand,
      pascalXiOrdinaryZetaRightEdgeIntegrand,
      pascalCenteredXiPrimeSideFiniteCutoffRawDifference]
    ring
  have hgi₀T : IntervalIntegrable g volume 0 W.rectangle.T := by
    apply hgi.mono_set
    intro t ht
    simp only [Set.mem_uIcc] at ht ⊢
    rcases ht with ht | ht
    · exact Or.inl ⟨by linarith [W.rectangle.hT, ht.1], ht.2⟩
    · exfalso
      linarith [W.rectangle.hT]
  have hgi_left : IntervalIntegrable g volume (-W.rectangle.T) 0 := by
    apply hgi.mono_set
    rw [Set.uIcc_of_le (by linarith [W.rectangle.hT]),
      Set.uIcc_of_le (by linarith [W.rectangle.hT])]
    intro t ht
    exact ⟨ht.1, by linarith [ht.2, W.rectangle.hT]⟩
  have hsplit :
      (∫ t in (-W.rectangle.T)..W.rectangle.T, g t) =
        (∫ t in (-W.rectangle.T)..0, g t) +
          ∫ t in 0..W.rectangle.T, g t := by
    symm
    exact intervalIntegral.integral_add_adjacent_intervals hgi_left hgi₀T
  have hpair :
      (∫ t in (-W.rectangle.T)..0, g t) =
        -starRingEnd ℂ (∫ t in 0..W.rectangle.T, g t) := by
    calc
      (∫ t in (-W.rectangle.T)..0, g t) =
          ∫ t in 0..W.rectangle.T, g (-t) := by
            symm
            simpa only [neg_zero, neg_neg] using
              (intervalIntegral.integral_comp_neg (f := g)
                (a := 0) (b := W.rectangle.T))
      _ = ∫ t in 0..W.rectangle.T, -starRingEnd ℂ (g t) := by
            apply intervalIntegral.integral_congr_ae
            filter_upwards [] with t ht
            exact pascalCenteredXiPrimeSideFiniteCutoffOrientedIntegrand_neg_eq_neg_conj
              hε W X t
      _ = -starRingEnd ℂ (∫ t in 0..W.rectangle.T, g t) := by
            rw [intervalIntegral.integral_neg,
              intervalIntegral.intervalIntegral_conj]
  have htotal :
      (pascalCenteredXiPrimeSideFiniteCutoffResidual ε W X) =
        -starRingEnd ℂ (∫ t in 0..W.rectangle.T, g t) +
          ∫ t in 0..W.rectangle.T, g t := by
    rw [pascalCenteredXiPrimeSideFiniteCutoffResidual_eq_integral_rawDifference
      hε W X]
    change (∫ t in (-W.rectangle.T)..W.rectangle.T, g t) = _
    rw [hsplit, hpair]
  have him := congrArg Complex.im htotal
  have him' :
      (pascalCenteredXiPrimeSideFiniteCutoffResidual ε W X).im =
        2 * (∫ t in 0..W.rectangle.T, g t).im := by
    calc
      (pascalCenteredXiPrimeSideFiniteCutoffResidual ε W X).im =
          (∫ t in 0..W.rectangle.T, g t).im +
            (∫ t in 0..W.rectangle.T, g t).im := by simpa using him
      _ = 2 * (∫ t in 0..W.rectangle.T, g t).im := by ring
  rw [him']
  calc
    2 * (∫ t in 0..W.rectangle.T, g t).im =
        2 * ∫ t in 0..W.rectangle.T, (g t).im := by
          exact congrArg (fun x : ℝ => 2 * x)
            (intervalIntegral.intervalIntegral_im hgi₀T).symm
    _ = 2 * ∫ t in 0..W.rectangle.T,
        (pascalCenteredXiPrimeSideFiniteCutoffRawDifference ε W X t).re := by
          congr 1
          apply intervalIntegral.integral_congr_ae
          filter_upwards [] with t ht
          simp [g, Complex.mul_im]

/-! ## CS11-F/G: signed tail convention and frontier -/

/-- The positive-convention finite prime tail is ordinary zeta minus PHZ. -/
noncomputable def pascalCenteredXiPrimeSideFinitePrimeTail
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) (t : ℝ) : ℂ :=
  pascalXiOrdinaryZetaNegLogDeriv
      (pascalSymmetricRectangleRightEdge W.rectangle.σ t) -
    pascalPrimePowerPHZFiniteUpTo X
      (pascalSymmetricRectangleRightEdge W.rectangle.σ t)

theorem pascalCenteredXiPrimeSideFiniteCutoffRawDifference_eq_neg_weight_mul_primeTail
    {ε : ℝ} (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) (t : ℝ) :
    pascalCenteredXiPrimeSideFiniteCutoffRawDifference ε W X t =
      -(pascalCenteredXiMellinSecondDifferenceWeight ε 0
        (pascalOrdinaryToCentered
          (pascalSymmetricRectangleRightEdge W.rectangle.σ t)) *
        pascalCenteredXiPrimeSideFinitePrimeTail W X t) := by
  unfold pascalCenteredXiPrimeSideFiniteCutoffRawDifference
    pascalCenteredXiPrimeSideFinitePrimeTail
  ring

/-- The raw finite residual amplitude is interval-integrable on the complete
finite residue window.  This adapter is exported for the finite block layer;
it does not assert integrability of an infinite tail. -/
theorem intervalIntegrable_pascalCenteredXiPrimeSideFiniteCutoffRawDifference
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    IntervalIntegrable
      (pascalCenteredXiPrimeSideFiniteCutoffRawDifference ε W X)
      volume (-W.rectangle.T) W.rectangle.T := by
  have hcut := intervalIntegrable_pascalPrimePowerRightEdgeCutoffIntegrand
    (h := pascalCenteredXiMellinSecondDifferenceWeight ε 0)
    (pascalCenteredXiMellinSecondDifferenceWeight_differentiable
      (ε := ε) (τ := 0) hε)
    (σ := W.rectangle.σ) (T := W.rectangle.T) X
  have hzeta := intervalIntegrable_pascalXiOrdinaryZetaRightEdgeIntegrand_of_residueWindow
    (h := pascalCenteredXiMellinSecondDifferenceWeight ε 0)
    (pascalCenteredXiMellinSecondDifferenceWeight_differentiable
      (ε := ε) (τ := 0) hε) W
  have hcut' := hcut.mul_const (-Complex.I)
  have hzeta' := hzeta.mul_const (-Complex.I)
  apply (hcut'.sub hzeta').congr
  intro t ht
  simp only [pascalPrimePowerRightEdgeCutoffIntegrand,
    pascalXiOrdinaryZetaRightEdgeIntegrand,
    pascalCenteredXiPrimeSideFiniteCutoffRawDifference]
  ring_nf
  simp [Complex.I_sq]
  ring

/-! ## CS11 closeout: the exact signed tail formula -/

/-- The finite defect error is exactly the positive-convention signed tail
projection.  This is a finite source identity: it uses neither an infinite
tail representation nor a sum/integral exchange. -/
theorem pascalCenteredXiMellinQuadraticArithmeticDefectApproximant_sub_endpoint_eq_two_over_pi_integral_primeTail
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiMellinQuadraticArithmeticDefectApproximant ε W X -
        pascalCenteredXiMellinQuadraticArithmeticDefectEndpoint ε W =
      (2 / Real.pi) *
        ∫ t in (0 : ℝ)..W.rectangle.T,
          (pascalCenteredXiMellinSecondDifferenceWeight ε 0
              (pascalOrdinaryToCentered
                (pascalSymmetricRectangleRightEdge W.rectangle.σ t)) *
            pascalCenteredXiPrimeSideFinitePrimeTail W X t).re := by
  rw [pascalCenteredXiMellinQuadraticArithmeticDefectApproximant_sub_endpoint_eq_neg_primeResidual_im_div_pi
    hε W X,
    pascalCenteredXiPrimeSideFiniteCutoffResidual_im_eq_two_mul_half_re hε W X]
  have hpoint : ∀ t : ℝ,
      pascalCenteredXiPrimeSideFiniteCutoffRawDifference ε W X t =
        -(pascalCenteredXiMellinSecondDifferenceWeight ε 0
          (pascalOrdinaryToCentered
            (pascalSymmetricRectangleRightEdge W.rectangle.σ t)) *
          pascalCenteredXiPrimeSideFinitePrimeTail W X t) :=
    fun t => pascalCenteredXiPrimeSideFiniteCutoffRawDifference_eq_neg_weight_mul_primeTail
      W X t
  have hInt :
      ∫ t in (0 : ℝ)..W.rectangle.T,
          (pascalCenteredXiPrimeSideFiniteCutoffRawDifference ε W X t).re =
        ∫ t in (0 : ℝ)..W.rectangle.T,
          (-(pascalCenteredXiMellinSecondDifferenceWeight ε 0
            (pascalOrdinaryToCentered
              (pascalSymmetricRectangleRightEdge W.rectangle.σ t)) *
            pascalCenteredXiPrimeSideFinitePrimeTail W X t)).re := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [] with t ht
    rw [hpoint]
  rw [hInt]
  have hneg :
      ∫ t in (0 : ℝ)..W.rectangle.T,
          (-(pascalCenteredXiMellinSecondDifferenceWeight ε 0
            (pascalOrdinaryToCentered
              (pascalSymmetricRectangleRightEdge W.rectangle.σ t)) *
            pascalCenteredXiPrimeSideFinitePrimeTail W X t)).re =
        -(∫ t in (0 : ℝ)..W.rectangle.T,
          (pascalCenteredXiMellinSecondDifferenceWeight ε 0
            (pascalOrdinaryToCentered
              (pascalSymmetricRectangleRightEdge W.rectangle.σ t)) *
            pascalCenteredXiPrimeSideFinitePrimeTail W X t).re) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [] with t ht
    simp only [Complex.neg_re]
  rw [hneg]
  ring

inductive PascalCenteredXiPrimeSideSignedTailPairingGap : Prop
  | noIndependentSignedTailProjectionProvider :
      PascalCenteredXiPrimeSideSignedTailPairingGap

end DkMath.RH.CFBRCProjection
