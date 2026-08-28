/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.CosmicFormulaZetaContactThresholdPolarizationBridgeAudit
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CosmicFormulaZetaZeroCutoffContactBaselineAudit"

/-!
# CFZP-006P: zero-cutoff contact baseline public decomposition

This module names the signed zero-cutoff radial-contact baseline and exposes
its finite complete-source and correction-source decompositions.  It records
order classifications only; no positivity of the baseline, correction
source, or interaction energy is asserted.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.Analysis
open DkMath.NumberTheory
open DkMath.NumberTheory.PrimitiveSet
open Filter
open MeasureTheory
open Set
open scoped ComplexConjugate Interval Topology

/-! ## A. Signed zero-cutoff baseline -/

noncomputable def cfzpZeroCutoffRadialContactBaseline
    (ε : ℝ)
    (W : PascalCenteredXiResidueTransportWindow) : ℝ :=
  pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W 0

theorem cfzpZeroCutoffRadialContactBaseline_eq_zeroCutoff_deficit :
    cfzpZeroCutoffRadialContactBaseline ε W =
      pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W 0 := by
  rfl

/-! ## B. Complete-source and correction-source decomposition -/

theorem cfzpZeroCutoffRadialContactBaseline_eq_pi_mul_fixedMoment_sub_completeSourceZero
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) :
    cfzpZeroCutoffRadialContactBaseline ε W =
      Real.pi *
        (pascalCenteredXiFixedRadialSecondMomentFunctional W.R -
          pascalCenteredXiPrimeSideIndependentCompleteSourceReal ε W 0) := by
  simpa [cfzpZeroCutoffRadialContactBaseline] using
    (pascalCenteredXiPrimeSideIndependentCompleteSource_radialDeficit_eq
      hε W 0)

theorem cfzpMellinQuadraticNormalizedPrimeContribution_zeroCutoff
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) :
    pascalCenteredXiMellinQuadraticNormalizedPrimeContribution ε W 0 = 0 := by
  rw [pascalCenteredXiMellinQuadraticNormalizedPrimeContribution_eq_two_div_pi_modeSum
    hε W 0]
  simp

theorem cfzpIndependentCompleteSourceReal_zeroCutoff_eq_correctionSourceReal
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) :
    pascalCenteredXiPrimeSideIndependentCompleteSourceReal ε W 0 =
      pascalCenteredXiPrimeSideIndependentCorrectionSourceReal ε W := by
  have hsplit :=
    pascalCenteredXiPrimeSideIndependentCompleteSourceReal_eq_prime_add_correction
      hε W 0
  have hprime := cfzpMellinQuadraticNormalizedPrimeContribution_zeroCutoff hε W
  rw [hsplit, hprime]
  simp

theorem cfzpZeroCutoffRadialContactBaseline_eq_pi_mul_fixedMoment_sub_correctionSource
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) :
    cfzpZeroCutoffRadialContactBaseline ε W =
      Real.pi *
        (pascalCenteredXiFixedRadialSecondMomentFunctional W.R -
          pascalCenteredXiPrimeSideIndependentCorrectionSourceReal ε W) := by
  have hcomplete :=
    cfzpZeroCutoffRadialContactBaseline_eq_pi_mul_fixedMoment_sub_completeSourceZero
      hε W
  have hzero := cfzpIndependentCompleteSourceReal_zeroCutoff_eq_correctionSourceReal hε W
  rw [hzero] at hcomplete
  exact hcomplete

theorem cfzpIndependentCorrectionSourceReal_eq_archimedean_add_elementary_add_top
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) :
    pascalCenteredXiPrimeSideIndependentCorrectionSourceReal ε W =
      pascalCenteredXiMellinQuadraticNormalizedArchimedeanContribution ε W +
        pascalCenteredXiMellinQuadraticNormalizedElementaryContribution ε W +
        pascalCenteredXiMellinQuadraticNormalizedTopContribution ε W := by
  rfl

theorem cfzpZeroCutoffRadialContactBaseline_eq_pi_mul_fixedMoment_sub_correctionComponents
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) :
    cfzpZeroCutoffRadialContactBaseline ε W =
      Real.pi *
        (pascalCenteredXiFixedRadialSecondMomentFunctional W.R -
          (pascalCenteredXiMellinQuadraticNormalizedArchimedeanContribution ε W +
            pascalCenteredXiMellinQuadraticNormalizedElementaryContribution ε W +
            pascalCenteredXiMellinQuadraticNormalizedTopContribution ε W)) := by
  have h := cfzpZeroCutoffRadialContactBaseline_eq_pi_mul_fixedMoment_sub_correctionSource
    hε W
  rw [cfzpIndependentCorrectionSourceReal_eq_archimedean_add_elementary_add_top] at h
  exact h

/-! ## C. Baseline sign/order classification -/

theorem cfzpZeroCutoffRadialContactBaseline_eq_zero_iff_correctionSource_eq_fixedMoment
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) :
    cfzpZeroCutoffRadialContactBaseline ε W = 0 ↔
      pascalCenteredXiPrimeSideIndependentCorrectionSourceReal ε W =
        pascalCenteredXiFixedRadialSecondMomentFunctional W.R := by
  have h := cfzpZeroCutoffRadialContactBaseline_eq_pi_mul_fixedMoment_sub_correctionSource
    hε W
  rw [h]
  constructor
  · intro hz
    have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    have hdiff := (mul_eq_zero.mp hz).resolve_left hpi
    linarith
  · intro hs
    rw [hs]
    simp

theorem cfzpZeroCutoffRadialContactBaseline_nonneg_iff_correctionSource_le_fixedMoment
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) :
    0 ≤ cfzpZeroCutoffRadialContactBaseline ε W ↔
      pascalCenteredXiPrimeSideIndependentCorrectionSourceReal ε W ≤
        pascalCenteredXiFixedRadialSecondMomentFunctional W.R := by
  have h := cfzpZeroCutoffRadialContactBaseline_eq_pi_mul_fixedMoment_sub_correctionSource
    hε W
  rw [h]
  rw [mul_nonneg_iff_of_pos_left Real.pi_pos]
  constructor <;> intro hs <;> linarith

theorem cfzpZeroCutoffRadialContactBaseline_nonpos_iff_fixedMoment_le_correctionSource
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) :
    cfzpZeroCutoffRadialContactBaseline ε W ≤ 0 ↔
      pascalCenteredXiFixedRadialSecondMomentFunctional W.R ≤
        pascalCenteredXiPrimeSideIndependentCorrectionSourceReal ε W := by
  have h := cfzpZeroCutoffRadialContactBaseline_eq_pi_mul_fixedMoment_sub_correctionSource
    hε W
  rw [h]
  constructor
  · intro hs
    rcases (mul_nonpos_iff.mp hs) with hs | hs
    · linarith
    · linarith [Real.pi_pos]
  · intro hs
    exact mul_nonpos_of_nonneg_of_nonpos Real.pi_pos.le (by linarith)

/-! ## D. Zero-cutoff finite interaction ledger -/

theorem cfzpAggregateRayInteractionEnergy_zeroCutoff
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) :
    pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W 0 = 0 := by
  rw [pascalCenteredXiPrimeSideAggregateRayInteractionEnergy_eq_two_modeSum hε W 0]
  simp

/-! ## E. Named-baseline contact bridge -/

section FiniteLedger

variable {ε : ℝ} (hε : 0 < ε)
variable {W : PascalCenteredXiResidueTransportWindow} {X : ℕ}
variable (hSafe : IsPascalCenteredXiTopLogDerivDecompositionSafe W)
variable (hZeta : IntervalIntegrable
  (fun u : ℝ =>
    pascalCenteredXiMellinSecondDifferenceWeight ε 0
      (pascalOrdinaryToCentered
        (pascalSymmetricRectangleTopEdge u W.rectangle.T)) *
    pascalXiOrdinaryZetaNegLogDeriv
      (pascalSymmetricRectangleTopEdge u W.rectangle.T))
  volume W.rectangle.σ (1 - W.rectangle.σ))
variable (hPHZ : IntervalIntegrable
  (fun u : ℝ =>
    pascalCenteredXiMellinSecondDifferenceWeight ε 0
      (pascalOrdinaryToCentered
        (pascalSymmetricRectangleTopEdge u W.rectangle.T)) *
    pascalPrimePowerPHZFiniteUpTo X
      (pascalSymmetricRectangleTopEdge u W.rectangle.T))
  volume W.rectangle.σ (1 - W.rectangle.σ))
variable (hWeighted : IntervalIntegrable
  (fun u : ℝ =>
    pascalCenteredXiPrimeSideFiniteResidualTopMellinWeight ε W u *
      pascalCenteredXiPrimeSideFiniteResidualLogRate X W u)
  volume W.rectangle.σ (1 - W.rectangle.σ))
variable (hρ : IntervalIntegrable
  (pascalCenteredXiPrimeSideFiniteResidualScalarDensity ε X W)
  volume W.rectangle.σ (1 - W.rectangle.σ))
variable (hρm : IntervalIntegrable
  (fun u : ℝ => pascalCenteredXiPrimeSideFiniteResidualScalarDensity
    ε X W (1 - u))
  volume W.rectangle.σ (1 - W.rectangle.σ))
variable (hPairLeft : IntervalIntegrable
  (pascalCenteredXiPrimeSideFiniteResidualMirrorScalarDensity ε X W)
  volume W.rectangle.σ (1 / 2 : ℝ))
variable (hPairRight : IntervalIntegrable
  (pascalCenteredXiPrimeSideFiniteResidualMirrorScalarDensity ε X W)
  volume (1 / 2 : ℝ) (1 - W.rectangle.σ))
variable (hArch : IntervalIntegrable
  (fun u : ℝ =>
    pascalCenteredXiMellinSecondDifferenceWeight ε 0
      (pascalOrdinaryToCentered
        (pascalSymmetricRectangleTopEdge u W.rectangle.T)) *
    pascalXiArchimedeanLogDeriv
      (pascalSymmetricRectangleTopEdge u W.rectangle.T))
  volume W.rectangle.σ (1 - W.rectangle.σ))
variable (hElem : IntervalIntegrable
  (fun u : ℝ =>
    pascalCenteredXiMellinSecondDifferenceWeight ε 0
      (pascalOrdinaryToCentered
        (pascalSymmetricRectangleTopEdge u W.rectangle.T)) *
    pascalXiElementaryLogDerivCorrection
      (pascalSymmetricRectangleTopEdge u W.rectangle.T))
  volume W.rectangle.σ (1 - W.rectangle.σ))

include hε hSafe hZeta hPHZ hWeighted hρ hρm hPairLeft hPairRight hArch hElem

theorem cfzpIntegratedPolarizedContactSlack_eq_four_mul_zeroCutoffBaseline_sub_interaction :
    cfzpIntegratedPolarizedContactSlack ε X W =
      4 *
        (cfzpZeroCutoffRadialContactBaseline ε W -
          pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W X) := by
  simpa [cfzpZeroCutoffRadialContactBaseline] using
    (cfzpIntegratedPolarizedContactSlack_eq_four_mul_zeroCutoffDeficit_sub_interaction
      hε hSafe hZeta hPHZ hWeighted hρ hρm hPairLeft hPairRight hArch hElem)

theorem cfzpIntegratedPolarizedImbalance_eq_contactThreshold_iff_interaction_reaches_zeroCutoffBaseline :
    cfzpIntegratedPolarizedImbalance ε X W =
        cfzpIntegratedPolarizedContactThresholdLevel ε X W ↔
      pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W X =
        cfzpZeroCutoffRadialContactBaseline ε W := by
  have hslack :=
    cfzpIntegratedPolarizedContactSlack_eq_four_mul_zeroCutoffBaseline_sub_interaction
      hε hSafe hZeta hPHZ hWeighted hρ hρm hPairLeft hPairRight hArch hElem
  have hfold :=
    cfzpIntegratedPolarizedContactSlack_eq_threshold_sub_imbalance
      (ε := ε) (X := X) (W := W)
  constructor
  · intro hcontact
    rw [hcontact] at hfold
    have hzero : cfzpIntegratedPolarizedContactSlack ε X W = 0 := by
      linarith [hfold]
    linarith [hslack]
  · intro hreach
    have hzero : cfzpIntegratedPolarizedContactSlack ε X W = 0 := by
      rw [hslack, hreach]
      ring
    linarith [hfold, hzero]

theorem cfzpIntegratedPolarizedContactSlack_nonneg_iff_interaction_le_zeroCutoffBaseline :
    0 ≤ cfzpIntegratedPolarizedContactSlack ε X W ↔
      pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W X ≤
        cfzpZeroCutoffRadialContactBaseline ε W := by
  have h :=
    cfzpIntegratedPolarizedContactSlack_eq_four_mul_zeroCutoffBaseline_sub_interaction
      hε hSafe hZeta hPHZ hWeighted hρ hρm hPairLeft hPairRight hArch hElem
  rw [h]
  rw [mul_nonneg_iff_of_pos_left (by norm_num : (0 : ℝ) < 4)]
  constructor <;> intro hs <;> linarith

theorem cfzpIntegratedPolarizedContactSlack_nonpos_iff_zeroCutoffBaseline_le_interaction :
    cfzpIntegratedPolarizedContactSlack ε X W ≤ 0 ↔
      cfzpZeroCutoffRadialContactBaseline ε W ≤
        pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W X := by
  have h :=
    cfzpIntegratedPolarizedContactSlack_eq_four_mul_zeroCutoffBaseline_sub_interaction
      hε hSafe hZeta hPHZ hWeighted hρ hρm hPairLeft hPairRight hArch hElem
  rw [h]
  constructor
  · intro hs
    rcases (mul_nonpos_iff.mp hs) with hs | hs
    · linarith
    · norm_num at hs
  · intro hs
    exact mul_nonpos_of_nonneg_of_nonpos (by norm_num) (by linarith)

theorem cfzpIntegratedPolarizedImbalance_le_contactThreshold_iff_interaction_le_zeroCutoffBaseline :
    cfzpIntegratedPolarizedImbalance ε X W ≤
        cfzpIntegratedPolarizedContactThresholdLevel ε X W ↔
      pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W X ≤
        cfzpZeroCutoffRadialContactBaseline ε W := by
  have hslack :=
    cfzpIntegratedPolarizedContactSlack_nonneg_iff_interaction_le_zeroCutoffBaseline
      hε hSafe hZeta hPHZ hWeighted hρ hρm hPairLeft hPairRight hArch hElem
  have hfold :=
    cfzpIntegratedPolarizedContactSlack_eq_threshold_sub_imbalance
      (ε := ε) (X := X) (W := W)
  constructor
  · intro h
    apply hslack.mp
    linarith [hfold]
  · intro h
    have hs := hslack.mpr h
    linarith [hfold, hs]

theorem cfzpIntegratedPolarizedContactThreshold_le_imbalance_iff_zeroCutoffBaseline_le_interaction :
    cfzpIntegratedPolarizedContactThresholdLevel ε X W ≤
        cfzpIntegratedPolarizedImbalance ε X W ↔
      cfzpZeroCutoffRadialContactBaseline ε W ≤
        pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W X := by
  have hslack :=
    cfzpIntegratedPolarizedContactSlack_nonpos_iff_zeroCutoffBaseline_le_interaction
      hε hSafe hZeta hPHZ hWeighted hρ hρm hPairLeft hPairRight hArch hElem
  have hfold :=
    cfzpIntegratedPolarizedContactSlack_eq_threshold_sub_imbalance
      (ε := ε) (X := X) (W := W)
  constructor
  · intro h
    apply hslack.mp
    linarith [hfold]
  · intro h
    have hs := hslack.mpr h
    linarith [hfold, hs]

end FiniteLedger

/-! ## F. Explicit sign frontier -/

inductive CfzpZeroCutoffBaselineNonnegativityGap : Prop
  | noIndependentCorrectionSourceBelowFixedMomentProvider

end DkMath.RH.CFBRCProjection
