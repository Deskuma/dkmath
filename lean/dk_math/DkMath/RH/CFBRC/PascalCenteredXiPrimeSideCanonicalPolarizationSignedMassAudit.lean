/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideIndependentRadialContactProviderAudit
import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideNormalizedRayPolarizationOrderingAudit
import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideQuadraticizationAudit
import Mathlib.Tactic

/-!
# CS24: canonical polarization signed-mass audit

This module instantiates the CS23 signed mass with the finite aggregate plus
polarization energy.  It proves the exact finite source normalization and the
resulting canonical decomposition.  The canonical remainder is intentionally
left as a named source frontier; no cofinal smallness or sign provider is
claimed.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.Analysis
open DkMath.NumberTheory
open DkMath.NumberTheory.PrimitiveSet
open Filter
open MeasureTheory
open scoped Interval Topology

local notation "GεX" => pascalCenteredXiPrimeSideFiniteRadialContactDeficit
local notation "E+εX" => pascalCenteredXiPrimeSideAggregateRayPlusEnergy
local notation "E-εX" => pascalCenteredXiPrimeSideAggregateRayMinusEnergy

/-! The following local source helpers repeat the finite CS11 conjugation
pattern for the prime source itself.  They are finite identities only. -/

private noncomputable def cs24PrimeSource
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) (t : ℝ) : ℂ :=
  pascalCenteredXiMellinSecondDifferenceWeight ε 0
      (pascalOrdinaryToCentered
        (pascalSymmetricRectangleRightEdge W.rectangle.σ t)) *
    pascalPrimePowerPHZFiniteUpTo X
      (pascalSymmetricRectangleRightEdge W.rectangle.σ t)

private theorem cs24Multiplier_conj
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

private theorem cs24Weight_conj
    {ε : ℝ} (hε : 0 < ε) (z : ℂ) :
    pascalCenteredXiMellinSecondDifferenceWeight ε 0 (starRingEnd ℂ z) =
      starRingEnd ℂ (pascalCenteredXiMellinSecondDifferenceWeight ε 0 z) := by
  rw [pascalCenteredXiMellinQuadraticWeight_eq_generic hε,
    pascalCenteredXiMellinQuadraticWeight_eq_generic hε]
  unfold mellinQuadraticBoxWeight
  rw [map_mul, map_pow, cs24Multiplier_conj hε]

private theorem cs24PrimeSource_neg_eq_conj
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) (t : ℝ) :
    cs24PrimeSource ε W X (-t) =
      starRingEnd ℂ (cs24PrimeSource ε W X t) := by
  unfold cs24PrimeSource
  have hs : pascalSymmetricRectangleRightEdge W.rectangle.σ (-t) =
      starRingEnd ℂ (pascalSymmetricRectangleRightEdge W.rectangle.σ t) := by
    exact pascalSymmetricRectangleRightEdge_neg_eq_conj W.rectangle.σ t
  have hz : pascalOrdinaryToCentered
      (pascalSymmetricRectangleRightEdge W.rectangle.σ (-t)) =
      starRingEnd ℂ (pascalOrdinaryToCentered
        (pascalSymmetricRectangleRightEdge W.rectangle.σ t)) := by
    rw [hs]
    have htwo : starRingEnd ℂ (2 : ℂ) = 2 := by
      simp only [map_ofNat]
    simp [pascalOrdinaryToCentered, criticalLineCenter, htwo]
  rw [hz, hs, cs24Weight_conj hε,
    pascalPrimePowerPHZFiniteUpTo_conj]
  simp only [map_mul]

private theorem cs24ContinuousPHZ
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    Continuous (fun t : ℝ => pascalPrimePowerPHZFiniteUpTo X
      (pascalSymmetricRectangleRightEdge W.rectangle.σ t)) := by
  have hpath : Continuous (fun t : ℝ =>
      pascalSymmetricRectangleRightEdge W.rectangle.σ t) := by
    change Continuous (fun t : ℝ => (W.rectangle.σ : ℂ) + (t : ℂ) * Complex.I)
    fun_prop
  have hterm : ∀ n : ℕ, Continuous (fun t : ℝ =>
      LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ))
        (pascalSymmetricRectangleRightEdge W.rectangle.σ t) n) := by
    intro n
    by_cases hn : n = 0
    · subst n
      have hz : (fun t : ℝ =>
          LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ))
            (pascalSymmetricRectangleRightEdge W.rectangle.σ t) 0) =
        (fun _ : ℝ => 0) := by
        funext t
        rw [vonMangoldt_LSeries_term_eq]
        simp
      rw [hz]
      exact continuous_const
    · let : NeZero (n : ℂ) := ⟨by exact_mod_cast hn⟩
      have hnterm : (fun t : ℝ =>
          LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ))
            (pascalSymmetricRectangleRightEdge W.rectangle.σ t) n) =
        (fun t : ℝ => (ArithmeticFunction.vonMangoldt n : ℂ) *
          ((n : ℂ) ^ (-(pascalSymmetricRectangleRightEdge W.rectangle.σ t)))) := by
        funext t
        rw [vonMangoldt_LSeries_term_eq]
      rw [hnterm]
      convert continuous_const.mul
          ((continuous_const_cpow (n : ℂ)).comp
            (continuous_neg.comp hpath)) using 1
      all_goals (ext t; rfl)
  rw [show (fun t : ℝ => pascalPrimePowerPHZFiniteUpTo X
      (pascalSymmetricRectangleRightEdge W.rectangle.σ t)) =
      (fun t : ℝ => ∑ n ∈ Finset.range (X + 1),
        LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ))
          (pascalSymmetricRectangleRightEdge W.rectangle.σ t) n) by
        funext t; exact pascalPrimePowerPHZFiniteUpTo_eq_LSeries_partialSum X _]
  apply continuous_finsetSum
  intro n hn
  exact hterm n

private theorem cs24ContinuousPrimeSource
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    Continuous (cs24PrimeSource ε W X) := by
  have hnode : Continuous (fun t : ℝ =>
      pascalOrdinaryToCentered
        (pascalSymmetricRectangleRightEdge W.rectangle.σ t)) := by
    have hpath : Continuous (fun t : ℝ =>
        pascalSymmetricRectangleRightEdge W.rectangle.σ t) := by
      change Continuous (fun t : ℝ =>
        (W.rectangle.σ : ℂ) + (t : ℂ) * Complex.I)
      fun_prop
    change Continuous (fun t : ℝ =>
      pascalSymmetricRectangleRightEdge W.rectangle.σ t - criticalLineCenter)
    exact hpath.sub continuous_const
  have hw := (pascalCenteredXiMellinSecondDifferenceWeight_differentiable
    (ε := ε) (τ := 0) hε).continuous
  exact (hw.comp hnode).mul (cs24ContinuousPHZ W X)

private theorem cs24PrimeSource_full_re_eq_two_half_re
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    (∫ t in (-W.rectangle.T)..W.rectangle.T, cs24PrimeSource ε W X t).re =
      2 * ∫ t in (0 : ℝ)..W.rectangle.T,
        (cs24PrimeSource ε W X t).re := by
  have hfull := (cs24ContinuousPrimeSource hε W X).intervalIntegrable
    (μ := volume) (-W.rectangle.T) W.rectangle.T
  have hright : IntervalIntegrable (cs24PrimeSource ε W X)
      volume 0 W.rectangle.T := by
    apply hfull.mono_set
    intro t ht
    simp only [Set.mem_uIcc] at ht ⊢
    rcases ht with ht | ht
    · exact Or.inl ⟨by linarith [W.rectangle.hT, ht.1], ht.2⟩
    · exfalso
      linarith [W.rectangle.hT]
  have hleft : IntervalIntegrable (cs24PrimeSource ε W X)
      volume (-W.rectangle.T) 0 := by
    apply hfull.mono_set
    rw [Set.uIcc_of_le (by linarith [W.rectangle.hT]),
      Set.uIcc_of_le (by linarith [W.rectangle.hT])]
    intro t ht
    exact ⟨ht.1, by linarith [ht.2, W.rectangle.hT]⟩
  have hsplit :
      (∫ t in (-W.rectangle.T)..W.rectangle.T, cs24PrimeSource ε W X t) =
        (∫ t in (-W.rectangle.T)..0, cs24PrimeSource ε W X t) +
          ∫ t in 0..W.rectangle.T, cs24PrimeSource ε W X t := by
    symm
    exact intervalIntegral.integral_add_adjacent_intervals hleft hright
  have hpair :
      (∫ t in (-W.rectangle.T)..0, cs24PrimeSource ε W X t) =
        starRingEnd ℂ (∫ t in 0..W.rectangle.T, cs24PrimeSource ε W X t) := by
    calc
      (∫ t in (-W.rectangle.T)..0, cs24PrimeSource ε W X t) =
          ∫ t in 0..W.rectangle.T, cs24PrimeSource ε W X (-t) := by
            symm
            simpa only [neg_zero, neg_neg] using
              (intervalIntegral.integral_comp_neg
                (f := cs24PrimeSource ε W X) (a := 0)
                (b := W.rectangle.T))
      _ = ∫ t in 0..W.rectangle.T,
          starRingEnd ℂ (cs24PrimeSource ε W X t) := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [] with t ht
          exact cs24PrimeSource_neg_eq_conj hε W X t
      _ = starRingEnd ℂ (∫ t in 0..W.rectangle.T,
          cs24PrimeSource ε W X t) := by
          rw [intervalIntegral.intervalIntegral_conj]
  rw [hsplit, hpair]
  rw [Complex.add_re, Complex.conj_re]
  symm
  have hre :
      (∫ t in (0 : ℝ)..W.rectangle.T, (cs24PrimeSource ε W X t).re) =
        (∫ t in (0 : ℝ)..W.rectangle.T, cs24PrimeSource ε W X t).re := by
    rw [intervalIntegral.integral_of_le (by linarith [W.rectangle.hT]),
      intervalIntegral.integral_of_le (by linarith [W.rectangle.hT])]
    exact integral_re hright.1
  rw [hre]
  ring

private theorem cs24NormalizedVertical_re
    (z : ℂ) :
    ((2 * Real.pi * Complex.I)⁻¹ * (2 * (z * Complex.I))).re =
      z.re / Real.pi := by
  simp only [Complex.mul_re, Complex.mul_im, Complex.inv_re, Complex.inv_im,
    Complex.normSq, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im]
  norm_num
  field_simp [Real.pi_ne_zero]

private theorem cs24ContinuousModeIntegrand
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (n : ℕ) :
    Continuous (pascalCenteredXiPrimeSideFiniteModeIntegrand ε W n) := by
  have hpath : Continuous (fun t : ℝ =>
      pascalSymmetricRectangleRightEdge W.rectangle.σ t) := by
    change Continuous (fun t : ℝ =>
      (W.rectangle.σ : ℂ) + (t : ℂ) * Complex.I)
    fun_prop
  have hnode : Continuous (fun t : ℝ =>
      pascalOrdinaryToCentered
        (pascalSymmetricRectangleRightEdge W.rectangle.σ t)) := by
    change Continuous (fun t : ℝ =>
      pascalSymmetricRectangleRightEdge W.rectangle.σ t - criticalLineCenter)
    exact hpath.sub continuous_const
  have hweight : Continuous (fun t : ℝ =>
      pascalCenteredXiMellinSecondDifferenceWeight ε 0
        (pascalOrdinaryToCentered
          (pascalSymmetricRectangleRightEdge W.rectangle.σ t))) :=
    (pascalCenteredXiMellinSecondDifferenceWeight_differentiable
      (ε := ε) (τ := 0) hε).continuous.comp hnode
  by_cases hn : n = 0
  · subst n
    have hz : pascalCenteredXiPrimeSideFiniteModeIntegrand ε W 0 =
        fun _ : ℝ => 0 := by
      funext t
      simp [pascalCenteredXiPrimeSideFiniteModeIntegrand]
    rw [hz]
    exact continuous_const
  · let : NeZero (n : ℂ) := ⟨by exact_mod_cast hn⟩
    have hpow : Continuous (fun t : ℝ =>
        ((n : ℂ) ^
          (-(pascalSymmetricRectangleRightEdge W.rectangle.σ t)))) := by
      exact (continuous_const_cpow (n : ℂ)).comp
        (continuous_neg.comp hpath)
    have hcomplex : Continuous (fun t : ℝ =>
        pascalCenteredXiMellinSecondDifferenceWeight ε 0
          (pascalOrdinaryToCentered
            (pascalSymmetricRectangleRightEdge W.rectangle.σ t)) *
        ((n : ℂ) ^
          (-(pascalSymmetricRectangleRightEdge W.rectangle.σ t)))) :=
      hweight.mul hpow
    have hraw : Continuous (fun t : ℝ =>
      Complex.re
        ((pascalCenteredXiMellinSecondDifferenceWeight ε 0
            (pascalOrdinaryToCentered
              (pascalSymmetricRectangleRightEdge W.rectangle.σ t))) *
          ((n : ℂ) ^
            (-(pascalSymmetricRectangleRightEdge W.rectangle.σ t))))) :=
      Complex.continuous_re.comp hcomplex
    have hdef : pascalCenteredXiPrimeSideFiniteModeIntegrand ε W n =
        (fun t : ℝ => Complex.re
          ((pascalCenteredXiMellinSecondDifferenceWeight ε 0
              (pascalOrdinaryToCentered
                (pascalSymmetricRectangleRightEdge W.rectangle.σ t))) *
            ((n : ℂ) ^
              (-(pascalSymmetricRectangleRightEdge W.rectangle.σ t))))) := by
      funext t
      simp [pascalCenteredXiPrimeSideFiniteModeIntegrand, hn]
    rw [hdef]
    exact hraw

private theorem cs24ModeSum_eq_half_source_re
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    (∑ n ∈ Finset.range (X + 1),
      (ArithmeticFunction.vonMangoldt n : ℝ) *
        pascalCenteredXiPrimeSideFiniteModeKernel ε W n) =
      ∫ t in (0 : ℝ)..W.rectangle.T,
        (cs24PrimeSource ε W X t).re := by
  have hsum : ∀ n ∈ Finset.range (X + 1),
      IntervalIntegrable
        (fun t => (ArithmeticFunction.vonMangoldt n : ℝ) *
          pascalCenteredXiPrimeSideFiniteModeIntegrand ε W n t)
        volume 0 W.rectangle.T := by
    intro n hn
    exact (cs24ContinuousModeIntegrand hε W n).intervalIntegrable
      (μ := volume) 0 W.rectangle.T |>.const_mul _
  calc
    (∑ n ∈ Finset.range (X + 1),
        (ArithmeticFunction.vonMangoldt n : ℝ) *
          pascalCenteredXiPrimeSideFiniteModeKernel ε W n) =
        ∑ n ∈ Finset.range (X + 1),
          ∫ t in (0 : ℝ)..W.rectangle.T,
            (ArithmeticFunction.vonMangoldt n : ℝ) *
              pascalCenteredXiPrimeSideFiniteModeIntegrand ε W n t := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [pascalCenteredXiPrimeSideFiniteModeKernel]
      rw [← intervalIntegral.integral_const_mul]
    _ = ∫ t in (0 : ℝ)..W.rectangle.T,
          ∑ n ∈ Finset.range (X + 1),
            (ArithmeticFunction.vonMangoldt n : ℝ) *
              pascalCenteredXiPrimeSideFiniteModeIntegrand ε W n t := by
      symm
      exact intervalIntegral.integral_finsetSum hsum
    _ = ∫ t in (0 : ℝ)..W.rectangle.T,
          (cs24PrimeSource ε W X t).re := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [] with t ht
      simp only [cs24PrimeSource,
        pascalPrimePowerPHZFiniteUpTo_eq_vonMangoldt_sum,
        Finset.mul_sum, Complex.re_sum]
      apply Finset.sum_congr rfl
      intro n hn
      by_cases h0 : n = 0
      · subst n
        simp [pascalCenteredXiPrimeSideFiniteModeIntegrand]
      · simp [pascalCenteredXiPrimeSideFiniteModeIntegrand, h0,
          Complex.mul_re]
        ring

private theorem cs24NormalizedPrime_eq_source_integral
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiMellinQuadraticNormalizedPrimeContribution ε W X =
      ((2 * Real.pi * Complex.I)⁻¹ *
        (2 * ∫ t in (-W.rectangle.T)..W.rectangle.T,
          cs24PrimeSource ε W X t * Complex.I)).re := by
  unfold pascalCenteredXiMellinQuadraticNormalizedPrimeContribution
  have hsum := pascalCenteredXiPrimeSideQuadraticizationPrimeModeSum_eq_cutoffIntegral
    hε W X
  have hsum' :
      (∑ n ∈ Finset.range (X + 1),
        ∫ t in (-W.rectangle.T)..W.rectangle.T,
          (pascalCenteredXiMellinSecondDifferenceWeight ε 0
            (pascalOrdinaryToCentered
              (pascalSymmetricRectangleRightEdge W.rectangle.σ t)) *
            ((ArithmeticFunction.vonMangoldt n : ℂ) *
              ((n : ℂ) ^
                (-(pascalSymmetricRectangleRightEdge W.rectangle.σ t)))) *
            Complex.I)) =
        ∫ t in (-W.rectangle.T)..W.rectangle.T,
          cs24PrimeSource ε W X t * Complex.I := by
    simpa only [pascalCenteredXiPrimeSideQuadraticizationPrimeModeSum,
    pascalCenteredXiPrimeSideQuadraticizationPrimeMode,
    pascalPrimePowerRightEdgeCutoffIntegral,
    pascalPrimePowerRightEdgeCutoffIntegrand, cs24PrimeSource] using hsum
  change ((2 * Real.pi * Complex.I)⁻¹ *
      (2 * (∑ n ∈ Finset.range (X + 1),
        ∫ t in (-W.rectangle.T)..W.rectangle.T,
          (pascalCenteredXiMellinSecondDifferenceWeight ε 0
            (pascalOrdinaryToCentered
              (pascalSymmetricRectangleRightEdge W.rectangle.σ t)) *
            ((ArithmeticFunction.vonMangoldt n : ℂ) *
              ((n : ℂ) ^
                (-(pascalSymmetricRectangleRightEdge W.rectangle.σ t)))) *
            Complex.I)))).re = _
  rw [hsum']

/-! ## CS24-A: finite prime normalization -/

theorem pascalCenteredXiMellinQuadraticNormalizedPrimeContribution_eq_two_div_pi_modeSum
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiMellinQuadraticNormalizedPrimeContribution ε W X =
      (2 / Real.pi) *
    (∑ n ∈ Finset.range (X + 1),
          (ArithmeticFunction.vonMangoldt n : ℝ) *
            pascalCenteredXiPrimeSideFiniteModeKernel ε W n) := by
  rw [cs24NormalizedPrime_eq_source_integral hε W X]
  have hmul :
      (∫ t in (-W.rectangle.T)..W.rectangle.T,
          cs24PrimeSource ε W X t * Complex.I) =
        (∫ t in (-W.rectangle.T)..W.rectangle.T,
          cs24PrimeSource ε W X t) * Complex.I := by
    rw [intervalIntegral.integral_mul_const]
  rw [hmul, cs24NormalizedVertical_re,
    cs24PrimeSource_full_re_eq_two_half_re hε W X,
    cs24ModeSum_eq_half_source_re hε W X]
  field_simp [Real.pi_ne_zero]

theorem pascalCenteredXiMellinQuadraticNormalizedPrimeContribution_eq_aggregateEnergyDifference_div_two_pi
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiMellinQuadraticNormalizedPrimeContribution ε W X =
      (E+εX ε W X - E-εX ε W X) / (2 * Real.pi) := by
  rw [pascalCenteredXiMellinQuadraticNormalizedPrimeContribution_eq_two_div_pi_modeSum
    hε W X,
    ← pascalCenteredXiPrimeSideFiniteModeSum_eq_aggregateRayEnergy_difference hε W X]
  ring

/-! ## CS24-B/C: correction split and canonical signed mass -/

noncomputable def pascalCenteredXiPrimeSideIndependentCorrectionSourceReal
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) : ℝ :=
  pascalCenteredXiMellinQuadraticNormalizedArchimedeanContribution ε W +
  pascalCenteredXiMellinQuadraticNormalizedElementaryContribution ε W +
  pascalCenteredXiMellinQuadraticNormalizedTopContribution ε W

theorem pascalCenteredXiPrimeSideIndependentCompleteSourceReal_eq_prime_add_correction
    {ε : ℝ} (_hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiPrimeSideIndependentCompleteSourceReal ε W X =
      pascalCenteredXiMellinQuadraticNormalizedPrimeContribution ε W X +
      pascalCenteredXiPrimeSideIndependentCorrectionSourceReal ε W := by
  simp [pascalCenteredXiPrimeSideIndependentCompleteSourceReal,
    pascalCenteredXiPrimeSideIndependentCorrectionSourceReal]
  ring

noncomputable def pascalCenteredXiPrimeSideCanonicalPolarizationMass
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) : ℝ :=
  E+εX ε W X / 2

noncomputable def pascalCenteredXiPrimeSideCanonicalPolarizationRemainder
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) : ℝ :=
  Real.pi *
      (pascalCenteredXiFixedRadialSecondMomentFunctional W.R -
        pascalCenteredXiPrimeSideIndependentCorrectionSourceReal ε W) +
    E-εX ε W X / 2

theorem pascalCenteredXiPrimeSideCanonicalPolarizationMass_nonneg
    {ε : ℝ} (hε : 0 < ε)
  (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    0 ≤ pascalCenteredXiPrimeSideCanonicalPolarizationMass ε W X := by
  unfold pascalCenteredXiPrimeSideCanonicalPolarizationMass
  exact div_nonneg (pascalCenteredXiPrimeSideAggregateRayPlusEnergy_nonneg hε W X)
    (by norm_num)

theorem pascalCenteredXiPrimeSideFiniteRadialContactDeficit_eq_canonicalRemainder_sub_mass
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    GεX ε W X =
      pascalCenteredXiPrimeSideCanonicalPolarizationRemainder ε W X -
        pascalCenteredXiPrimeSideCanonicalPolarizationMass ε W X := by
  have hsource := pascalCenteredXiPrimeSideIndependentCompleteSource_radialDeficit_eq
    hε W X
  have hsplit := pascalCenteredXiPrimeSideIndependentCompleteSourceReal_eq_prime_add_correction
    hε W X
  have hprime :=
    pascalCenteredXiMellinQuadraticNormalizedPrimeContribution_eq_aggregateEnergyDifference_div_two_pi
      hε W X
  rw [hsource, hsplit, hprime]
  unfold pascalCenteredXiPrimeSideCanonicalPolarizationRemainder
    pascalCenteredXiPrimeSideCanonicalPolarizationMass
  field_simp [Real.pi_ne_zero]
  ring

/-! ## CS24-D/E: cutoff-zero baseline and strength audit -/

theorem pascalCenteredXiPrimeSideAggregateRayPlusEnergy_zero
    {ε : ℝ} (_hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) :
    E+εX ε W 0 = 0 := by
  unfold pascalCenteredXiPrimeSideAggregateRayPlusEnergy
  have hs : pascalPrimeCoordinateSupportUpTo 0 = ∅ := by
    ext p
    rw [mem_pascalPrimeCoordinateSupportUpTo_iff]
    constructor
    · rintro ⟨hp, hp0⟩
      exact (hp.ne_zero (Nat.eq_zero_of_le_zero hp0)).elim
    · intro hp
      simp at hp
  rw [hs]
  simp

theorem pascalCenteredXiPrimeSideAggregateRayMinusEnergy_zero
    {ε : ℝ} (_hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) :
    E-εX ε W 0 = 0 := by
  unfold pascalCenteredXiPrimeSideAggregateRayMinusEnergy
  have hs : pascalPrimeCoordinateSupportUpTo 0 = ∅ := by
    ext p
    rw [mem_pascalPrimeCoordinateSupportUpTo_iff]
    constructor
    · rintro ⟨hp, hp0⟩
      exact (hp.ne_zero (Nat.eq_zero_of_le_zero hp0)).elim
    · intro hp
      simp at hp
  rw [hs]
  simp

theorem pascalCenteredXiPrimeSideCanonicalPolarizationMass_zero
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) :
    pascalCenteredXiPrimeSideCanonicalPolarizationMass ε W 0 = 0 := by
  unfold pascalCenteredXiPrimeSideCanonicalPolarizationMass
  rw [pascalCenteredXiPrimeSideAggregateRayPlusEnergy_zero hε W]
  ring

theorem pascalCenteredXiPrimeSideCanonicalPolarizationRemainder_eq_zeroCutoff_deficit_add_minusMass
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiPrimeSideCanonicalPolarizationRemainder ε W X =
      GεX ε W 0 + E-εX ε W X / 2 := by
  have hdecomp0 :=
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit_eq_canonicalRemainder_sub_mass
      hε W 0
  have hmass0 := pascalCenteredXiPrimeSideCanonicalPolarizationMass_zero hε W
  have hminus0 := pascalCenteredXiPrimeSideAggregateRayMinusEnergy_zero hε W
  have hbase :
      GεX ε W 0 =
        Real.pi *
            (pascalCenteredXiFixedRadialSecondMomentFunctional W.R -
              pascalCenteredXiPrimeSideIndependentCorrectionSourceReal ε W) := by
    rw [hdecomp0, hmass0]
    unfold pascalCenteredXiPrimeSideCanonicalPolarizationRemainder
    rw [hminus0]
    ring
  unfold pascalCenteredXiPrimeSideCanonicalPolarizationRemainder
  rw [← hbase]

theorem pascalCenteredXiPrimeSideCanonicalPolarizationRemainder_ge_zeroCutoff_deficit
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    GεX ε W 0 ≤
      pascalCenteredXiPrimeSideCanonicalPolarizationRemainder ε W X := by
  rw [pascalCenteredXiPrimeSideCanonicalPolarizationRemainder_eq_zeroCutoff_deficit_add_minusMass
    hε W X]
  have hminus := pascalCenteredXiPrimeSideAggregateRayMinusEnergy_nonneg hε W X
  linarith

/-! A useful necessary-condition bonus: a small canonical remainder must also
control the nonnegative minus-energy that was moved into the remainder.  This
is still finite and algebraic; it is not a provider for the required estimate. -/

theorem pascalCenteredXiPrimeSideCanonicalRemainder_le_implies_minusEnergy_le
    {ε η : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ)
    (hR : pascalCenteredXiPrimeSideCanonicalPolarizationRemainder ε W X ≤ η) :
    E-εX ε W X ≤ 2 * (η - GεX ε W 0) := by
  have hbase :=
    pascalCenteredXiPrimeSideCanonicalPolarizationRemainder_eq_zeroCutoff_deficit_add_minusMass
      hε W X
  linarith

/-! ## CS24-F: conditional cofinal adapter -/

def PascalCenteredXiPrimeSideCanonicalPolarizationRemainderCofinalSmallAt
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) : Prop :=
  ∀ η : ℝ, 0 < η → ∀ N : ℕ, ∃ X : ℕ, N ≤ X ∧
    pascalCenteredXiPrimeSideCanonicalPolarizationRemainder ε W X ≤ η

theorem pascalCenteredXiPrimeSideCanonicalRemainder_cofinalSmall_implies_zeroCutoff_nonpos
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow)
    (hsmall : PascalCenteredXiPrimeSideCanonicalPolarizationRemainderCofinalSmallAt ε W) :
    GεX ε W 0 ≤ 0 := by
  by_contra hnot
  have hpositive : 0 < GεX ε W 0 := lt_of_not_ge hnot
  let η : ℝ := GεX ε W 0 / 2
  have hη : 0 < η := by
    dsimp [η]
    linarith
  rcases hsmall η hη 0 with ⟨X, _, hR⟩
  have hle := pascalCenteredXiPrimeSideCanonicalPolarizationRemainder_ge_zeroCutoff_deficit
    hε W X
  dsimp [η] at hR
  linarith

theorem pascalCenteredXiPrimeSideCanonicalRemainder_cofinalSmall_implies_cofinalRadialContactZero
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow)
    (hsmall : PascalCenteredXiPrimeSideCanonicalPolarizationRemainderCofinalSmallAt ε W) :
    PascalCenteredXiPrimeSideCofinalRadialContactZeroAt ε W := by
  intro η hη N
  rcases hsmall η hη N with ⟨X, hNX, hR⟩
  refine ⟨X, hNX, ?_⟩
  have hmass := pascalCenteredXiPrimeSideCanonicalPolarizationMass_nonneg hε W X
  have hdecomp := pascalCenteredXiPrimeSideFiniteRadialContactDeficit_eq_canonicalRemainder_sub_mass
    hε W X
  rw [hdecomp]
  linarith

inductive PascalCenteredXiPrimeSideCanonicalPolarizationRemainderGap : Prop
  | noIndependentCofinalCanonicalRemainderProvider

end DkMath.RH.CFBRCProjection
