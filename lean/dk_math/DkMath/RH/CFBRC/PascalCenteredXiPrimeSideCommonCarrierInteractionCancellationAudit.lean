/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideCanonicalPolarizationSignedMassAudit
import Mathlib.Tactic

/-!
# CS25: common-carrier / interaction cancellation audit

This module returns the CS24 finite polarization to the normalized ray state
`Z`.  The two positive whole energies are decomposed into a common carrier
`|Z|² + 1` and a signed interaction `2 * Re Z`.  The common carrier cancels
from the finite prime source and from the radial deficit exactly.

All statements are finite.  No sign of the interaction, provider, infinite
exchange, endpoint sign, or RH consequence is asserted.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.NumberTheory
open DkMath.NumberTheory.PrimitiveSet
open Filter
open MeasureTheory
open scoped ComplexConjugate Interval Topology

local notation "GεX" => pascalCenteredXiPrimeSideFiniteRadialContactDeficit
local notation "E+εX" => pascalCenteredXiPrimeSideAggregateRayPlusEnergy
local notation "E-εX" => pascalCenteredXiPrimeSideAggregateRayMinusEnergy

/-! ## CS25-A: normalized ray state and pointwise carrier algebra -/

noncomputable def pascalCenteredXiPrimeSideCS25RayState
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (X p : ℕ) (t : ℝ) : ℂ :=
  pascalCenteredXiPrimeSideFinitePrimePowerRayAmplitude ε W X p t

noncomputable def pascalCenteredXiPrimeSideCommonDensity (z : ℂ) : ℝ :=
  Complex.normSq z + 1

noncomputable def pascalCenteredXiPrimeSideInteractionDensity (z : ℂ) : ℝ :=
  2 * z.re

private theorem cs25ComplexAddOneDiv
    {z w : ℂ} (hw : w ≠ 0) :
    z / w + 1 = (z + w) / w := by
  field_simp [hw]

private theorem cs25ComplexSubOneDiv
    {z w : ℂ} (hw : w ≠ 0) :
    z / w - 1 = (z - w) / w := by
  field_simp [hw]

theorem pascalCenteredXiPrimeSideCS25RayState_eq_endpoint_div
    {ε : ℝ} (W : PascalCenteredXiResidueTransportWindow)
    {X p : ℕ} (hp : Nat.Prime p) (t : ℝ) :
    pascalCenteredXiPrimeSideCS25RayState ε W X p t =
      pascalCenteredXiPrimeSideFiniteGeometricRayEndpointAmplitude ε W X p t /
        pascalCenteredXiPrimeSideFiniteGeometricRayDenominatorVector W p t := by
  exact pascalCenteredXiPrimeSideFinitePrimePowerRayAmplitude_eq_endpoint_div W hp t

theorem pascalCenteredXiPrimeSideFiniteGeometricRayPlusDensity_eq_cs25State_normSq_add_one
    {ε : ℝ} (W : PascalCenteredXiResidueTransportWindow)
    {X p : ℕ} (hp : Nat.Prime p) (t : ℝ) :
    pascalCenteredXiPrimeSideFiniteGeometricRayPlusDensity ε W X p t =
      Complex.normSq (pascalCenteredXiPrimeSideCS25RayState ε W X p t + 1) := by
  let A := pascalCenteredXiPrimeSideFiniteGeometricRayEndpointAmplitude ε W X p t
  let B := pascalCenteredXiPrimeSideFiniteGeometricRayDenominatorVector W p t
  have hB : B ≠ 0 := by
    exact pascalCenteredXiPrimeSidePrimeRatioAtRightEdge_one_sub_ne_zero W hp t
  have hstate := pascalCenteredXiPrimeSideCS25RayState_eq_endpoint_div
    (ε := ε) W (X := X) hp t
  rw [hstate, cs25ComplexAddOneDiv hB, Complex.normSq_div]
  unfold pascalCenteredXiPrimeSideFiniteGeometricRayPlusDensity
  rfl

theorem pascalCenteredXiPrimeSideFiniteGeometricRayMinusDensity_eq_cs25State_normSq_sub_one
    {ε : ℝ} (W : PascalCenteredXiResidueTransportWindow)
    {X p : ℕ} (hp : Nat.Prime p) (t : ℝ) :
    pascalCenteredXiPrimeSideFiniteGeometricRayMinusDensity ε W X p t =
      Complex.normSq (pascalCenteredXiPrimeSideCS25RayState ε W X p t - 1) := by
  let A := pascalCenteredXiPrimeSideFiniteGeometricRayEndpointAmplitude ε W X p t
  let B := pascalCenteredXiPrimeSideFiniteGeometricRayDenominatorVector W p t
  have hB : B ≠ 0 := by
    exact pascalCenteredXiPrimeSidePrimeRatioAtRightEdge_one_sub_ne_zero W hp t
  have hstate := pascalCenteredXiPrimeSideCS25RayState_eq_endpoint_div
    (ε := ε) W (X := X) hp t
  rw [hstate, cs25ComplexSubOneDiv hB, Complex.normSq_div]
  unfold pascalCenteredXiPrimeSideFiniteGeometricRayMinusDensity
  rfl

theorem pascalCenteredXiPrimeSideCommonDensity_add_interactionDensity_eq_normSq_add_one
    (z : ℂ) :
    pascalCenteredXiPrimeSideCommonDensity z +
        pascalCenteredXiPrimeSideInteractionDensity z =
      Complex.normSq (z + 1) := by
  simp [pascalCenteredXiPrimeSideCommonDensity,
    pascalCenteredXiPrimeSideInteractionDensity, Complex.normSq_apply]
  ring

theorem pascalCenteredXiPrimeSideCommonDensity_sub_interactionDensity_eq_normSq_sub_one
    (z : ℂ) :
    pascalCenteredXiPrimeSideCommonDensity z -
        pascalCenteredXiPrimeSideInteractionDensity z =
      Complex.normSq (z - 1) := by
  simp [pascalCenteredXiPrimeSideCommonDensity,
    pascalCenteredXiPrimeSideInteractionDensity, Complex.normSq_apply]
  ring

theorem pascalCenteredXiPrimeSideCommonDensity_nonneg (z : ℂ) :
    0 ≤ pascalCenteredXiPrimeSideCommonDensity z := by
  unfold pascalCenteredXiPrimeSideCommonDensity
  exact add_nonneg (Complex.normSq_nonneg _) (by norm_num)

/-! ## CS25-B: finite ray integrability and interaction energies -/

private theorem cs25ContinuousRayState
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) {X p : ℕ}
    (hp : Nat.Prime p) :
    Continuous (pascalCenteredXiPrimeSideCS25RayState ε W X p) := by
  have hpath : Continuous (fun t : ℝ =>
      pascalSymmetricRectangleRightEdge W.rectangle.σ t) := by
    change Continuous (fun t : ℝ =>
      (W.rectangle.σ : ℂ) + (t : ℂ) * Complex.I)
    fun_prop
  have hnode : Continuous (fun t : ℝ =>
      pascalCenteredXiPrimeSideModePhaseNode W t) := by
    unfold pascalCenteredXiPrimeSideModePhaseNode
    change Continuous (fun t : ℝ =>
      pascalSymmetricRectangleRightEdge W.rectangle.σ t - criticalLineCenter)
    exact hpath.sub continuous_const
  have hweight : Continuous (fun t : ℝ =>
      pascalCenteredXiMellinSecondDifferenceWeight ε 0
        (pascalCenteredXiPrimeSideModePhaseNode W t)) :=
    (pascalCenteredXiMellinSecondDifferenceWeight_differentiable
      (ε := ε) (τ := 0) hε).continuous.comp hnode
  have hq : Continuous (fun t : ℝ =>
      pascalCenteredXiPrimeSidePrimeRatioAtRightEdge W p t) := by
    unfold pascalCenteredXiPrimeSidePrimeRatioAtRightEdge
      pascalCenteredXiPrimeSidePrimeRatio
    let _ : NeZero ((p : ℕ) : ℂ) :=
      ⟨by exact_mod_cast hp.ne_zero⟩
    exact (continuous_const_cpow ((p : ℕ) : ℂ)).comp
      (continuous_neg.comp hpath)
  have hqpow : Continuous (fun t : ℝ =>
      pascalCenteredXiPrimeSidePrimeRatioAtRightEdge W p t ^
        (pascalCenteredXiPrimeSidePrimePowerRayLength X p + 1)) :=
    hq.pow _
  have hA : Continuous
      (pascalCenteredXiPrimeSideFiniteGeometricRayEndpointAmplitude ε W X p) := by
    unfold pascalCenteredXiPrimeSideFiniteGeometricRayEndpointAmplitude
    exact hweight.mul (hq.sub hqpow)
  have hB : Continuous
      (pascalCenteredXiPrimeSideFiniteGeometricRayDenominatorVector W p) := by
    unfold pascalCenteredXiPrimeSideFiniteGeometricRayDenominatorVector
    exact continuous_const.sub hq
  have hdiv : Continuous (fun t : ℝ =>
      pascalCenteredXiPrimeSideFiniteGeometricRayEndpointAmplitude ε W X p t /
        pascalCenteredXiPrimeSideFiniteGeometricRayDenominatorVector W p t) :=
    hA.div hB (fun t =>
      (pascalCenteredXiPrimeSidePrimeRatioAtRightEdge_one_sub_ne_zero W hp t))
  unfold pascalCenteredXiPrimeSideCS25RayState
  convert hdiv using 1
  funext t
  rw [pascalCenteredXiPrimeSideFinitePrimePowerRayAmplitude_eq_endpoint_div W hp t]

private theorem cs25ContinuousCommonDensity
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) {X p : ℕ}
    (hp : Nat.Prime p) :
    Continuous (fun t => pascalCenteredXiPrimeSideCommonDensity
      (pascalCenteredXiPrimeSideCS25RayState ε W X p t)) := by
  exact (Complex.continuous_normSq.comp (cs25ContinuousRayState hε W hp)).add
    continuous_const

private theorem cs25ContinuousInteractionDensity
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) {X p : ℕ}
    (hp : Nat.Prime p) :
    Continuous (fun t => pascalCenteredXiPrimeSideInteractionDensity
      (pascalCenteredXiPrimeSideCS25RayState ε W X p t)) := by
  unfold pascalCenteredXiPrimeSideInteractionDensity
  exact continuous_const.mul
    (Complex.continuous_re.comp (cs25ContinuousRayState hε W hp))

private theorem cs25IntervalIntegrableCommonDensity
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) {X p : ℕ}
    (hp : Nat.Prime p) :
    IntervalIntegrable
      (fun t => pascalCenteredXiPrimeSideCommonDensity
        (pascalCenteredXiPrimeSideCS25RayState ε W X p t))
      volume 0 W.rectangle.T :=
  (cs25ContinuousCommonDensity hε W hp).intervalIntegrable (μ := volume)
    0 W.rectangle.T

private theorem cs25IntervalIntegrableInteractionDensity
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) {X p : ℕ}
    (hp : Nat.Prime p) :
    IntervalIntegrable
      (fun t => pascalCenteredXiPrimeSideInteractionDensity
        (pascalCenteredXiPrimeSideCS25RayState ε W X p t))
      volume 0 W.rectangle.T :=
  (cs25ContinuousInteractionDensity hε W hp).intervalIntegrable (μ := volume)
    0 W.rectangle.T

noncomputable def pascalCenteredXiPrimeSideFiniteGeometricRayCommonEnergy
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (X p : ℕ) : ℝ :=
  ∫ t in (0 : ℝ)..W.rectangle.T,
    pascalCenteredXiPrimeSideCommonDensity
      (pascalCenteredXiPrimeSideCS25RayState ε W X p t)

noncomputable def pascalCenteredXiPrimeSideFiniteGeometricRayInteractionEnergy
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (X p : ℕ) : ℝ :=
  ∫ t in (0 : ℝ)..W.rectangle.T,
    pascalCenteredXiPrimeSideInteractionDensity
      (pascalCenteredXiPrimeSideCS25RayState ε W X p t)

theorem pascalCenteredXiPrimeSideFiniteGeometricRayPlusEnergy_eq_common_add_interaction
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) {X p : ℕ}
    (hp : Nat.Prime p) :
    pascalCenteredXiPrimeSideFiniteGeometricRayPlusEnergy ε W X p =
      pascalCenteredXiPrimeSideFiniteGeometricRayCommonEnergy ε W X p +
        pascalCenteredXiPrimeSideFiniteGeometricRayInteractionEnergy ε W X p := by
  unfold pascalCenteredXiPrimeSideFiniteGeometricRayPlusEnergy
    pascalCenteredXiPrimeSideFiniteGeometricRayCommonEnergy
    pascalCenteredXiPrimeSideFiniteGeometricRayInteractionEnergy
  rw [← intervalIntegral.integral_add
    (cs25IntervalIntegrableCommonDensity hε W hp)
    (cs25IntervalIntegrableInteractionDensity hε W hp)]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [] with t ht
  rw [pascalCenteredXiPrimeSideFiniteGeometricRayPlusDensity_eq_cs25State_normSq_add_one
    W hp t]
  exact (pascalCenteredXiPrimeSideCommonDensity_add_interactionDensity_eq_normSq_add_one _).symm

theorem pascalCenteredXiPrimeSideFiniteGeometricRayMinusEnergy_eq_common_sub_interaction
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) {X p : ℕ}
    (hp : Nat.Prime p) :
    pascalCenteredXiPrimeSideFiniteGeometricRayMinusEnergy ε W X p =
      pascalCenteredXiPrimeSideFiniteGeometricRayCommonEnergy ε W X p -
        pascalCenteredXiPrimeSideFiniteGeometricRayInteractionEnergy ε W X p := by
  unfold pascalCenteredXiPrimeSideFiniteGeometricRayMinusEnergy
    pascalCenteredXiPrimeSideFiniteGeometricRayCommonEnergy
    pascalCenteredXiPrimeSideFiniteGeometricRayInteractionEnergy
  rw [← intervalIntegral.integral_sub
    (cs25IntervalIntegrableCommonDensity hε W hp)
    (cs25IntervalIntegrableInteractionDensity hε W hp)]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [] with t ht
  rw [pascalCenteredXiPrimeSideFiniteGeometricRayMinusDensity_eq_cs25State_normSq_sub_one
    W hp t]
  exact (pascalCenteredXiPrimeSideCommonDensity_sub_interactionDensity_eq_normSq_sub_one _).symm

theorem pascalCenteredXiPrimeSideFiniteGeometricRayEnergy_difference_eq_two_interaction
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) {X p : ℕ}
    (hp : Nat.Prime p) :
    pascalCenteredXiPrimeSideFiniteGeometricRayPlusEnergy ε W X p -
        pascalCenteredXiPrimeSideFiniteGeometricRayMinusEnergy ε W X p =
      2 * pascalCenteredXiPrimeSideFiniteGeometricRayInteractionEnergy ε W X p := by
  rw [pascalCenteredXiPrimeSideFiniteGeometricRayPlusEnergy_eq_common_add_interaction
      hε W hp,
    pascalCenteredXiPrimeSideFiniteGeometricRayMinusEnergy_eq_common_sub_interaction
      hε W hp]
  ring

theorem pascalCenteredXiPrimeSideFiniteGeometricRayInteractionEnergy_eq_two_modeKernel
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) {X p : ℕ}
    (hp : Nat.Prime p) :
    pascalCenteredXiPrimeSideFiniteGeometricRayInteractionEnergy ε W X p =
      2 * pascalCenteredXiPrimeSideFinitePrimePowerRayKernel ε W X p := by
  have hnew := pascalCenteredXiPrimeSideFiniteGeometricRayEnergy_difference_eq_two_interaction
    hε W (X := X) (p := p) hp
  have hold := pascalCenteredXiPrimeSideFinitePrimePowerRayKernel_eq_energy_difference
    hε W (X := X) (p := p) hp
  linarith

/-! ## CS25-C: prime-weighted aggregate carrier and interaction -/

noncomputable def pascalCenteredXiPrimeSideAggregateRayCommonEnergy
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) : ℝ :=
  ∑ p ∈ pascalPrimeCoordinateSupportUpTo X,
    Real.log (p : ℝ) *
      pascalCenteredXiPrimeSideFiniteGeometricRayCommonEnergy ε W X p

noncomputable def pascalCenteredXiPrimeSideAggregateRayInteractionEnergy
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) : ℝ :=
  ∑ p ∈ pascalPrimeCoordinateSupportUpTo X,
    Real.log (p : ℝ) *
      pascalCenteredXiPrimeSideFiniteGeometricRayInteractionEnergy ε W X p

theorem pascalCenteredXiPrimeSideAggregateRayPlusEnergy_eq_common_add_interaction
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    E+εX ε W X =
      pascalCenteredXiPrimeSideAggregateRayCommonEnergy ε W X +
        pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W X := by
  classical
  unfold pascalCenteredXiPrimeSideAggregateRayPlusEnergy
    pascalCenteredXiPrimeSideAggregateRayCommonEnergy
    pascalCenteredXiPrimeSideAggregateRayInteractionEnergy
  calc
    (∑ p ∈ pascalPrimeCoordinateSupportUpTo X,
        Real.log (p : ℝ) *
          pascalCenteredXiPrimeSideFiniteGeometricRayPlusEnergy ε W X p) =
      ∑ p ∈ pascalPrimeCoordinateSupportUpTo X,
        Real.log (p : ℝ) *
          (pascalCenteredXiPrimeSideFiniteGeometricRayCommonEnergy ε W X p +
            pascalCenteredXiPrimeSideFiniteGeometricRayInteractionEnergy ε W X p) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [pascalCenteredXiPrimeSideFiniteGeometricRayPlusEnergy_eq_common_add_interaction
        hε W (mem_pascalPrimeCoordinateSupportUpTo_iff.mp hp).1]
    _ = _ := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]

theorem pascalCenteredXiPrimeSideAggregateRayMinusEnergy_eq_common_sub_interaction
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    E-εX ε W X =
      pascalCenteredXiPrimeSideAggregateRayCommonEnergy ε W X -
        pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W X := by
  classical
  unfold pascalCenteredXiPrimeSideAggregateRayMinusEnergy
    pascalCenteredXiPrimeSideAggregateRayCommonEnergy
    pascalCenteredXiPrimeSideAggregateRayInteractionEnergy
  calc
    (∑ p ∈ pascalPrimeCoordinateSupportUpTo X,
        Real.log (p : ℝ) *
          pascalCenteredXiPrimeSideFiniteGeometricRayMinusEnergy ε W X p) =
      ∑ p ∈ pascalPrimeCoordinateSupportUpTo X,
        Real.log (p : ℝ) *
          (pascalCenteredXiPrimeSideFiniteGeometricRayCommonEnergy ε W X p -
            pascalCenteredXiPrimeSideFiniteGeometricRayInteractionEnergy ε W X p) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [pascalCenteredXiPrimeSideFiniteGeometricRayMinusEnergy_eq_common_sub_interaction
        hε W (mem_pascalPrimeCoordinateSupportUpTo_iff.mp hp).1]
    _ = _ := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib]

theorem pascalCenteredXiPrimeSideAggregateRayInteractionEnergy_eq_two_modeSum
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W X =
      2 * (∑ n ∈ Finset.range (X + 1),
        (ArithmeticFunction.vonMangoldt n : ℝ) *
          pascalCenteredXiPrimeSideFiniteModeKernel ε W n) := by
  classical
  have hledger := pascalCenteredXiPrimeSideFiniteModeSum_eq_aggregateRayEnergy_difference
    hε W X
  have hplus := pascalCenteredXiPrimeSideAggregateRayPlusEnergy_eq_common_add_interaction
    hε W X
  have hminus := pascalCenteredXiPrimeSideAggregateRayMinusEnergy_eq_common_sub_interaction
    hε W X
  rw [hplus, hminus] at hledger
  linarith

theorem pascalCenteredXiMellinQuadraticNormalizedPrimeContribution_eq_aggregateInteraction_div_pi
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiMellinQuadraticNormalizedPrimeContribution ε W X =
      pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W X / Real.pi := by
  rw [pascalCenteredXiMellinQuadraticNormalizedPrimeContribution_eq_two_div_pi_modeSum
    hε W X,
    pascalCenteredXiPrimeSideAggregateRayInteractionEnergy_eq_two_modeSum hε W X]
  ring

/-! ## CS25-D: exact common-carrier cancellation -/

theorem pascalCenteredXiPrimeSideIndependentCompleteSourceReal_eq_correction_add_interaction_div_pi
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiPrimeSideIndependentCompleteSourceReal ε W X =
      pascalCenteredXiPrimeSideIndependentCorrectionSourceReal ε W +
        pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W X / Real.pi := by
  rw [pascalCenteredXiPrimeSideIndependentCompleteSourceReal_eq_prime_add_correction
    hε W X,
    pascalCenteredXiMellinQuadraticNormalizedPrimeContribution_eq_aggregateInteraction_div_pi
      hε W X]
  ring

private theorem pascalCenteredXiPrimeSideZeroCutoffDeficit_eq_correction_baseline
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) :
    GεX ε W 0 = Real.pi *
      (pascalCenteredXiFixedRadialSecondMomentFunctional W.R -
        pascalCenteredXiPrimeSideIndependentCorrectionSourceReal ε W) := by
  have hsource := pascalCenteredXiPrimeSideIndependentCompleteSource_radialDeficit_eq
    hε W 0
  have hsplit := pascalCenteredXiPrimeSideIndependentCompleteSourceReal_eq_prime_add_correction
    hε W 0
  have hprime := pascalCenteredXiMellinQuadraticNormalizedPrimeContribution_eq_two_div_pi_modeSum
    hε W 0
  rw [hsource, hsplit, hprime]
  simp

theorem pascalCenteredXiPrimeSideFiniteRadialContactDeficit_eq_zeroCutoff_deficit_sub_interaction
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    GεX ε W X =
      GεX ε W 0 - pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W X := by
  have hsource := pascalCenteredXiPrimeSideIndependentCompleteSource_radialDeficit_eq
    hε W X
  have hcomplete :=
    pascalCenteredXiPrimeSideIndependentCompleteSourceReal_eq_correction_add_interaction_div_pi
      hε W X
  have hbase := pascalCenteredXiPrimeSideZeroCutoffDeficit_eq_correction_baseline hε W
  rw [hsource, hcomplete, hbase]
  field_simp [Real.pi_ne_zero]
  ring

theorem pascalCenteredXiPrimeSideRadialContact_le_iff_interaction_reach
    {ε η : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    GεX ε W X ≤ η ↔
      GεX ε W 0 - η ≤ pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W X := by
  rw [pascalCenteredXiPrimeSideFiniteRadialContactDeficit_eq_zeroCutoff_deficit_sub_interaction
    hε W X]
  constructor <;> intro h <;> linarith

/-! ## CS25-E: common cancellation inside the CS24 signed mass -/

theorem pascalCenteredXiPrimeSideCanonicalPolarizationMass_eq_common_add_interaction_half
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiPrimeSideCanonicalPolarizationMass ε W X =
      (pascalCenteredXiPrimeSideAggregateRayCommonEnergy ε W X +
        pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W X) / 2 := by
  unfold pascalCenteredXiPrimeSideCanonicalPolarizationMass
  rw [pascalCenteredXiPrimeSideAggregateRayPlusEnergy_eq_common_add_interaction hε W X]

theorem pascalCenteredXiPrimeSideCanonicalPolarizationRemainder_eq_zeroCutoff_add_common_sub_interaction_half
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiPrimeSideCanonicalPolarizationRemainder ε W X =
      GεX ε W 0 +
        (pascalCenteredXiPrimeSideAggregateRayCommonEnergy ε W X -
          pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W X) / 2 := by
  have hbase :=
    pascalCenteredXiPrimeSideCanonicalPolarizationRemainder_eq_zeroCutoff_deficit_add_minusMass
      hε W X
  rw [hbase,
    pascalCenteredXiPrimeSideAggregateRayMinusEnergy_eq_common_sub_interaction hε W X]

theorem pascalCenteredXiPrimeSideCanonicalPolarization_common_carrier_cancels
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiPrimeSideCanonicalPolarizationRemainder ε W X -
        pascalCenteredXiPrimeSideCanonicalPolarizationMass ε W X =
      GεX ε W 0 - pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W X := by
  rw [pascalCenteredXiPrimeSideCanonicalPolarizationRemainder_eq_zeroCutoff_add_common_sub_interaction_half
      hε W X,
    pascalCenteredXiPrimeSideCanonicalPolarizationMass_eq_common_add_interaction_half
      hε W X]
  ring

/-! A pure real countermodel records why canonical remainder smallness is not
in general necessary for direct contact: the common carrier may be large while
the interaction already gives the target deficit. -/

theorem pascalCenteredXiPrimeSideCS25_canonical_remainder_strength_countermodel :
    ∃ (G₀ C I : ℝ), G₀ - I = 0 ∧ 0 < G₀ + (C - I) / 2 := by
  refine ⟨0, 2, 0, ?_, ?_⟩ <;> norm_num

inductive PascalCenteredXiPrimeSideAggregateInteractionReachGap : Prop
  | noIndependentCofinalInteractionReachProvider

end DkMath.RH.CFBRCProjection
