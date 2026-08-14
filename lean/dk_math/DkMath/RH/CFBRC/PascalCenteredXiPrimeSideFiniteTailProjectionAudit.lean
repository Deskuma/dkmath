/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideSignedTailPairingAudit
import Mathlib.Tactic

/-!
# CS12: finite signed-tail projection and block-kernel audit

This module keeps the signed tail at finite cutoff and finite vertical window.
It records cutoff/endpoint order adapters and finite PHZ blocks.  It does not
exchange an infinite tail with an integral, prove a fixed-ε sign theorem, or
derive RH.  In particular, the coefficient `Λ(n) ≥ 0` is not treated as a
sign certificate for the oscillatory mode kernel.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open MeasureTheory
open scoped Interval Topology

/-! ## CS12-A: finite signed tail projection -/

/-- The finite signed projection of the positive-convention prime tail. -/
noncomputable def pascalCenteredXiPrimeSideFiniteTailProjection
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) : ℝ :=
  ∫ t in (0 : ℝ)..W.rectangle.T,
    (pascalCenteredXiMellinSecondDifferenceWeight ε 0
      (pascalOrdinaryToCentered
        (pascalSymmetricRectangleRightEdge W.rectangle.σ t)) *
      pascalCenteredXiPrimeSideFinitePrimeTail W X t).re

theorem pascalCenteredXiMellinQuadraticArithmeticDefectApproximant_sub_endpoint_eq_tailProjection
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiMellinQuadraticArithmeticDefectApproximant ε W X -
        pascalCenteredXiMellinQuadraticArithmeticDefectEndpoint ε W =
      (2 / Real.pi) *
        pascalCenteredXiPrimeSideFiniteTailProjection ε W X := by
  simpa [pascalCenteredXiPrimeSideFiniteTailProjection] using
    (pascalCenteredXiMellinQuadraticArithmeticDefectApproximant_sub_endpoint_eq_two_over_pi_integral_primeTail
      hε W X)

/-! ## CS12-B: direction-only order adapters -/

theorem pascalCenteredXiPrimeSideFiniteTailProjection_nonneg_iff_endpoint_le_approximant
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    0 ≤ pascalCenteredXiPrimeSideFiniteTailProjection ε W X ↔
      pascalCenteredXiMellinQuadraticArithmeticDefectEndpoint ε W ≤
        pascalCenteredXiMellinQuadraticArithmeticDefectApproximant ε W X := by
  have hEq := pascalCenteredXiMellinQuadraticArithmeticDefectApproximant_sub_endpoint_eq_tailProjection
    hε W X
  have hscale : 0 < (2 / Real.pi : ℝ) := by positivity
  constructor
  · intro hP
    nlinarith
  · intro horder
    nlinarith

theorem pascalCenteredXiPrimeSideFiniteTailProjection_nonpos_iff_approximant_le_endpoint
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiPrimeSideFiniteTailProjection ε W X ≤ 0 ↔
      pascalCenteredXiMellinQuadraticArithmeticDefectApproximant ε W X ≤
        pascalCenteredXiMellinQuadraticArithmeticDefectEndpoint ε W := by
  have hEq := pascalCenteredXiMellinQuadraticArithmeticDefectApproximant_sub_endpoint_eq_tailProjection
    hε W X
  have hscale : 0 < (2 / Real.pi : ℝ) := by positivity
  constructor
  · intro hP
    nlinarith
  · intro horder
    nlinarith

/-! ## CS12-C: finite PHZ blocks -/

/-- The finite difference of two PHZ partial sums. -/
noncomputable def pascalCenteredXiPrimeSideFinitePrimeBlock
    (W : PascalCenteredXiResidueTransportWindow)
    (X Y : ℕ) (t : ℝ) : ℂ :=
  pascalPrimePowerPHZFiniteUpTo Y
      (pascalSymmetricRectangleRightEdge W.rectangle.σ t) -
    pascalPrimePowerPHZFiniteUpTo X
      (pascalSymmetricRectangleRightEdge W.rectangle.σ t)

theorem pascalCenteredXiPrimeSideFinitePrimeTail_sub_tail_eq_block
    (W : PascalCenteredXiResidueTransportWindow) (X Y : ℕ) (t : ℝ) :
    pascalCenteredXiPrimeSideFinitePrimeTail W X t -
        pascalCenteredXiPrimeSideFinitePrimeTail W Y t =
      pascalCenteredXiPrimeSideFinitePrimeBlock W X Y t := by
  unfold pascalCenteredXiPrimeSideFinitePrimeTail
    pascalCenteredXiPrimeSideFinitePrimeBlock
  ring

/-- The finite signed projection of a PHZ block, kept as a difference of
finite projections so no new integrability or tail exchange is hidden. -/
noncomputable def pascalCenteredXiPrimeSideFinitePrimeBlockProjection
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (X Y : ℕ) : ℝ :=
  pascalCenteredXiPrimeSideFiniteTailProjection ε W X -
    pascalCenteredXiPrimeSideFiniteTailProjection ε W Y

theorem pascalCenteredXiPrimeSideFiniteTailProjection_sub_eq_blockProjection
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X Y : ℕ) :
    pascalCenteredXiPrimeSideFiniteTailProjection ε W X -
        pascalCenteredXiPrimeSideFiniteTailProjection ε W Y =
      pascalCenteredXiPrimeSideFinitePrimeBlockProjection ε W X Y := by
  rfl

theorem pascalCenteredXiPrimeSideFinitePrimeBlockProjection_eq_integral
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X Y : ℕ) :
    pascalCenteredXiPrimeSideFinitePrimeBlockProjection ε W X Y =
      ∫ t in (0 : ℝ)..W.rectangle.T,
        (pascalCenteredXiMellinSecondDifferenceWeight ε 0
          (pascalOrdinaryToCentered
            (pascalSymmetricRectangleRightEdge W.rectangle.σ t)) *
          pascalCenteredXiPrimeSideFinitePrimeBlock W X Y t).re := by
  unfold pascalCenteredXiPrimeSideFinitePrimeBlockProjection
    pascalCenteredXiPrimeSideFiniteTailProjection
  have hX := intervalIntegrable_pascalCenteredXiPrimeSideFiniteCutoffRawDifference
    hε W X
  have hY := intervalIntegrable_pascalCenteredXiPrimeSideFiniteCutoffRawDifference
    hε W Y
  have hX0 : IntervalIntegrable
      (pascalCenteredXiPrimeSideFiniteCutoffRawDifference ε W X)
      volume 0 W.rectangle.T := by
    apply hX.mono_set
    intro t ht
    simp only [Set.mem_uIcc] at ht ⊢
    rcases ht with ht | ht
    · exact Or.inl ⟨by linarith [W.rectangle.hT, ht.1], ht.2⟩
    · exfalso
      linarith [W.rectangle.hT]
  have hY0 : IntervalIntegrable
      (pascalCenteredXiPrimeSideFiniteCutoffRawDifference ε W Y)
      volume 0 W.rectangle.T := by
    apply hY.mono_set
    intro t ht
    simp only [Set.mem_uIcc] at ht ⊢
    rcases ht with ht | ht
    · exact Or.inl ⟨by linarith [W.rectangle.hT, ht.1], ht.2⟩
    · exfalso
      linarith [W.rectangle.hT]
  have hsub :
      IntervalIntegrable
        (fun t : ℝ =>
          (pascalCenteredXiMellinSecondDifferenceWeight ε 0
            (pascalOrdinaryToCentered
              (pascalSymmetricRectangleRightEdge W.rectangle.σ t)) *
            pascalCenteredXiPrimeSideFinitePrimeTail W X t).re)
        volume 0 W.rectangle.T := by
    have hXweighted : IntervalIntegrable
        (fun t : ℝ =>
          pascalCenteredXiMellinSecondDifferenceWeight ε 0
            (pascalOrdinaryToCentered
              (pascalSymmetricRectangleRightEdge W.rectangle.σ t)) *
          pascalCenteredXiPrimeSideFinitePrimeTail W X t)
        volume 0 W.rectangle.T := by
      apply hX0.neg.congr
      intro t ht
      change -pascalCenteredXiPrimeSideFiniteCutoffRawDifference ε W X t = _
      rw [pascalCenteredXiPrimeSideFiniteCutoffRawDifference_eq_neg_weight_mul_primeTail]
      ring
    apply intervalIntegrable_iff.mpr
    simpa [Function.comp_def] using
      (RCLike.reCLM.integrableOn_comp hXweighted.def')
  have hsubY :
      IntervalIntegrable
        (fun t : ℝ =>
          (pascalCenteredXiMellinSecondDifferenceWeight ε 0
            (pascalOrdinaryToCentered
              (pascalSymmetricRectangleRightEdge W.rectangle.σ t)) *
            pascalCenteredXiPrimeSideFinitePrimeTail W Y t).re)
        volume 0 W.rectangle.T := by
    have hYweighted : IntervalIntegrable
        (fun t : ℝ =>
          pascalCenteredXiMellinSecondDifferenceWeight ε 0
            (pascalOrdinaryToCentered
              (pascalSymmetricRectangleRightEdge W.rectangle.σ t)) *
          pascalCenteredXiPrimeSideFinitePrimeTail W Y t)
        volume 0 W.rectangle.T := by
      apply hY0.neg.congr
      intro t ht
      change -pascalCenteredXiPrimeSideFiniteCutoffRawDifference ε W Y t = _
      rw [pascalCenteredXiPrimeSideFiniteCutoffRawDifference_eq_neg_weight_mul_primeTail]
      ring
    apply intervalIntegrable_iff.mpr
    simpa [Function.comp_def] using
      (RCLike.reCLM.integrableOn_comp hYweighted.def')
  rw [← intervalIntegral.integral_sub hsub hsubY]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [] with t ht
  rw [← Complex.sub_re, ← mul_sub,
    pascalCenteredXiPrimeSideFinitePrimeTail_sub_tail_eq_block]

/-! ## CS12-D: finite signed mode kernels -/

/-- The real signed kernel carried by one von Mangoldt mode.  The natural
cutoff convention is retained as `Finset.range (X + 1)` below, including the
repository's totalized `n = 0` term. -/
noncomputable def pascalCenteredXiPrimeSideFiniteModeIntegrand
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (n : ℕ) (t : ℝ) : ℝ :=
  if n = 0 then 0 else
    Complex.re
      ((pascalCenteredXiMellinSecondDifferenceWeight ε 0
          (pascalOrdinaryToCentered
            (pascalSymmetricRectangleRightEdge W.rectangle.σ t))) *
        ((n : ℂ) ^
          (-(pascalSymmetricRectangleRightEdge W.rectangle.σ t))))

/-- The finite half-window mode kernel. -/
noncomputable def pascalCenteredXiPrimeSideFiniteModeKernel
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (n : ℕ) : ℝ :=
  ∫ t in (0 : ℝ)..W.rectangle.T,
    pascalCenteredXiPrimeSideFiniteModeIntegrand ε W n t

private theorem continuous_pascalCenteredXiPrimeSideFiniteModeIntegrand
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
  · letI : NeZero (n : ℂ) := ⟨by exact_mod_cast hn⟩
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

private theorem intervalIntegrable_pascalCenteredXiPrimeSideFiniteModeIntegrand
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (n : ℕ) :
    IntervalIntegrable
      (pascalCenteredXiPrimeSideFiniteModeIntegrand ε W n)
      volume 0 W.rectangle.T :=
  (continuous_pascalCenteredXiPrimeSideFiniteModeIntegrand hε W n).intervalIntegrable
    (μ := volume) 0 W.rectangle.T

private theorem intervalIntegrable_finsetSum_pascalCenteredXiPrimeSideFiniteModeIntegrand
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (s : Finset ℕ) :
    IntervalIntegrable
      (fun t => ∑ n ∈ s,
        pascalCenteredXiPrimeSideFiniteModeIntegrand ε W n t)
      volume 0 W.rectangle.T := by
  have hc : Continuous (fun t => ∑ n ∈ s,
      pascalCenteredXiPrimeSideFiniteModeIntegrand ε W n t) := by
    apply continuous_finsetSum
    intro n hn
    exact (continuous_pascalCenteredXiPrimeSideFiniteModeIntegrand hε W n)
  exact hc.intervalIntegrable (μ := volume) 0 W.rectangle.T

theorem pascalCenteredXiPrimeSideFinitePrimeBlockProjection_eq_mode_sum_difference
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X Y : ℕ) :
    pascalCenteredXiPrimeSideFinitePrimeBlockProjection ε W X Y =
      (∑ n ∈ Finset.range (Y + 1),
        (ArithmeticFunction.vonMangoldt n : ℝ) *
          pascalCenteredXiPrimeSideFiniteModeKernel ε W n) -
      (∑ n ∈ Finset.range (X + 1),
        (ArithmeticFunction.vonMangoldt n : ℝ) *
          pascalCenteredXiPrimeSideFiniteModeKernel ε W n) := by
  rw [pascalCenteredXiPrimeSideFinitePrimeBlockProjection_eq_integral hε W X Y]
  have hblock : ∀ t : ℝ,
      (pascalCenteredXiMellinSecondDifferenceWeight ε 0
          (pascalOrdinaryToCentered
            (pascalSymmetricRectangleRightEdge W.rectangle.σ t)) *
        pascalCenteredXiPrimeSideFinitePrimeBlock W X Y t).re =
        (∑ n ∈ Finset.range (Y + 1),
          (ArithmeticFunction.vonMangoldt n : ℝ) *
            pascalCenteredXiPrimeSideFiniteModeIntegrand ε W n t) -
        (∑ n ∈ Finset.range (X + 1),
          (ArithmeticFunction.vonMangoldt n : ℝ) *
            pascalCenteredXiPrimeSideFiniteModeIntegrand ε W n t) := by
    intro t
    simp only [pascalCenteredXiPrimeSideFinitePrimeBlock,
      pascalPrimePowerPHZFiniteUpTo_eq_vonMangoldt_sum]
    rw [mul_sub, Complex.sub_re, Finset.mul_sum, Finset.mul_sum,
      Complex.re_sum, Complex.re_sum]
    apply congrArg₂ (· - ·)
    · apply Finset.sum_congr rfl
      intro n hn
      by_cases h0 : n = 0
      · subst n
        simp [pascalCenteredXiPrimeSideFiniteModeIntegrand]
      · simp [pascalCenteredXiPrimeSideFiniteModeIntegrand, h0,
          Complex.mul_re]
        ring
    · apply Finset.sum_congr rfl
      intro n hn
      by_cases h0 : n = 0
      · subst n
        simp [pascalCenteredXiPrimeSideFiniteModeIntegrand]
      · simp [pascalCenteredXiPrimeSideFiniteModeIntegrand, h0,
          Complex.mul_re]
        ring
  rw [show (fun t =>
      (pascalCenteredXiMellinSecondDifferenceWeight ε 0
          (pascalOrdinaryToCentered
            (pascalSymmetricRectangleRightEdge W.rectangle.σ t)) *
        pascalCenteredXiPrimeSideFinitePrimeBlock W X Y t).re) =
      (fun t =>
        (∑ n ∈ Finset.range (Y + 1),
          (ArithmeticFunction.vonMangoldt n : ℝ) *
            pascalCenteredXiPrimeSideFiniteModeIntegrand ε W n t) -
        (∑ n ∈ Finset.range (X + 1),
          (ArithmeticFunction.vonMangoldt n : ℝ) *
            pascalCenteredXiPrimeSideFiniteModeIntegrand ε W n t)) by
        funext t; exact hblock t]
  have hsumFY : IntervalIntegrable
      (fun t => ∑ n ∈ Finset.range (Y + 1),
        (ArithmeticFunction.vonMangoldt n : ℝ) *
          pascalCenteredXiPrimeSideFiniteModeIntegrand ε W n t)
      volume 0 W.rectangle.T := by
    have hc : Continuous (fun t => ∑ n ∈ Finset.range (Y + 1),
        (ArithmeticFunction.vonMangoldt n : ℝ) *
          pascalCenteredXiPrimeSideFiniteModeIntegrand ε W n t) := by
      apply continuous_finsetSum
      intro n hn
      exact continuous_const.mul
        (continuous_pascalCenteredXiPrimeSideFiniteModeIntegrand hε W n)
    exact hc.intervalIntegrable (μ := volume) 0 W.rectangle.T
  have hsumFX : IntervalIntegrable
      (fun t => ∑ n ∈ Finset.range (X + 1),
        (ArithmeticFunction.vonMangoldt n : ℝ) *
          pascalCenteredXiPrimeSideFiniteModeIntegrand ε W n t)
      volume 0 W.rectangle.T := by
    have hc : Continuous (fun t => ∑ n ∈ Finset.range (X + 1),
        (ArithmeticFunction.vonMangoldt n : ℝ) *
          pascalCenteredXiPrimeSideFiniteModeIntegrand ε W n t) := by
      apply continuous_finsetSum
      intro n hn
      exact continuous_const.mul
        (continuous_pascalCenteredXiPrimeSideFiniteModeIntegrand hε W n)
    exact hc.intervalIntegrable (μ := volume) 0 W.rectangle.T
  rw [intervalIntegral.integral_sub hsumFY hsumFX]
  have hFY : ∀ n ∈ Finset.range (Y + 1),
      IntervalIntegrable
        (fun t => (ArithmeticFunction.vonMangoldt n : ℝ) *
          pascalCenteredXiPrimeSideFiniteModeIntegrand ε W n t)
        volume 0 W.rectangle.T := by
    intro n hn
    exact (intervalIntegrable_pascalCenteredXiPrimeSideFiniteModeIntegrand
      hε W n).const_mul _
  have hFX : ∀ n ∈ Finset.range (X + 1),
      IntervalIntegrable
        (fun t => (ArithmeticFunction.vonMangoldt n : ℝ) *
          pascalCenteredXiPrimeSideFiniteModeIntegrand ε W n t)
        volume 0 W.rectangle.T := by
    intro n hn
    exact (intervalIntegrable_pascalCenteredXiPrimeSideFiniteModeIntegrand
      hε W n).const_mul _
  rw [intervalIntegral.integral_finsetSum hFY,
    intervalIntegral.integral_finsetSum hFX]
  apply congrArg₂ (· - ·)
  · apply Finset.sum_congr rfl
    intro n hn
    rw [pascalCenteredXiPrimeSideFiniteModeKernel]
    rw [← intervalIntegral.integral_const_mul]
  · apply Finset.sum_congr rfl
    intro n hn
    rw [pascalCenteredXiPrimeSideFiniteModeKernel]
    rw [← intervalIntegral.integral_const_mul]

theorem pascalCenteredXiPrimeSideFiniteModeCoefficient_nonneg (n : ℕ) :
    0 ≤ ArithmeticFunction.vonMangoldt n :=
  ArithmeticFunction.vonMangoldt_nonneg

end DkMath.RH.CFBRCProjection
