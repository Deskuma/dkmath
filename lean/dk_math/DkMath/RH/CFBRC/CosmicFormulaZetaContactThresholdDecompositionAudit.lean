/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.CosmicFormulaZetaIntegratedPolarizedBalanceThresholdAudit
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CosmicFormulaZetaContactThresholdDecompositionAudit"

/-!
# CFZP-006N: contact threshold decomposition audit

The contact threshold is named as a level, not as a mass.  The existing
finite ledgers decompose it into the integrated polarized imbalance plus
the radial-contact or completion slack.  No sign is assigned to the level
or to any slack term.

The independent complete-source decomposition is retained as a second
exact finite ledger.  No pointwise, source-zero, zeta-zero, infinite, or RH
consequence is introduced.
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

/-! ## A. Named finite levels -/

noncomputable def cfzpIntegratedPolarizedImbalance
    (ε : ℝ) (X : ℕ)
    (W : PascalCenteredXiResidueTransportWindow) : ℝ :=
  cfzpProjectedMirrorForwardIntegratedMinusMass ε X W -
    cfzpProjectedMirrorForwardIntegratedPlusMass ε X W

noncomputable def cfzpIntegratedPolarizedContactThresholdLevel
    (ε : ℝ) (X : ℕ)
    (W : PascalCenteredXiResidueTransportWindow) : ℝ :=
  4 * Real.pi * pascalCenteredXiPrimeSideFiniteRectangleBackground ε W X

/-! ## B. Pure finite arithmetic folds -/

private theorem cFZP_threshold_eq_imbalance_add_radial_slack
    {B G Δ : ℝ}
    (hLedger : G = Real.pi * B - Δ / 4) :
    4 * Real.pi * B = Δ + 4 * G := by
  linarith [hLedger]

private theorem cFZP_threshold_eq_imbalance_add_completion_slack
    {B R Δ : ℝ}
    (hLedger : B = (1 / Real.pi) * (Δ / 4) + R) :
    4 * Real.pi * B = Δ + 4 * Real.pi * R := by
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have h := hLedger
  field_simp [hpi] at h
  linarith

/-! ## C. Shared finite ledger hypotheses -/

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

/-! ## D. Radial and completion slack decompositions -/

theorem cfzpIntegratedPolarizedContactThresholdLevel_eq_imbalance_add_four_mul_radialContactDeficit :
    cfzpIntegratedPolarizedContactThresholdLevel ε X W =
      cfzpIntegratedPolarizedImbalance ε X W +
        4 * pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W X := by
  have hLedger :=
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit_eq_pi_mul_background_sub_integratedMass_difference
      hε hSafe hZeta hPHZ hWeighted hρ hρm hPairLeft hPairRight hArch hElem
  unfold cfzpIntegratedPolarizedContactThresholdLevel
    cfzpIntegratedPolarizedImbalance
  exact cFZP_threshold_eq_imbalance_add_radial_slack hLedger

theorem cfzpIntegratedPolarizedContactThresholdLevel_sub_imbalance_eq_four_mul_radialContactDeficit :
    cfzpIntegratedPolarizedContactThresholdLevel ε X W -
        cfzpIntegratedPolarizedImbalance ε X W =
      4 * pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W X := by
  have h :=
    cfzpIntegratedPolarizedContactThresholdLevel_eq_imbalance_add_four_mul_radialContactDeficit
      hε hSafe hZeta hPHZ hWeighted hρ hρm hPairLeft hPairRight hArch hElem
  linarith

omit hArch hElem in
theorem cfzpIntegratedPolarizedContactThresholdLevel_eq_imbalance_add_four_pi_mul_completionRemainder :
    cfzpIntegratedPolarizedContactThresholdLevel ε X W =
      cfzpIntegratedPolarizedImbalance ε X W +
        4 * Real.pi * cfzpFiniteRectangleCompletionRemainder ε W X := by
  have hLedger :=
    pascalCenteredXiPrimeSideFiniteRectangleBackground_eq_integratedMass_difference_add_completionRemainder
      hε hSafe hZeta hPHZ hWeighted hρ hρm hPairLeft hPairRight
  unfold cfzpIntegratedPolarizedContactThresholdLevel
    cfzpIntegratedPolarizedImbalance
  exact cFZP_threshold_eq_imbalance_add_completion_slack hLedger

omit hArch hElem in
theorem cfzpIntegratedPolarizedContactThresholdLevel_sub_imbalance_eq_four_pi_mul_completionRemainder :
    cfzpIntegratedPolarizedContactThresholdLevel ε X W -
        cfzpIntegratedPolarizedImbalance ε X W =
      4 * Real.pi * cfzpFiniteRectangleCompletionRemainder ε W X := by
  have h :=
    cfzpIntegratedPolarizedContactThresholdLevel_eq_imbalance_add_four_pi_mul_completionRemainder
      hε hSafe hZeta hPHZ hWeighted hρ hρm hPairLeft hPairRight
  linarith

/-! ## E. Independent complete-source ledger -/

theorem cfzpIntegratedPolarizedContactThresholdLevel_eq_imbalance_add_independentCompleteSourceSlack :
    cfzpIntegratedPolarizedContactThresholdLevel ε X W =
      cfzpIntegratedPolarizedImbalance ε X W +
        4 * Real.pi *
          (pascalCenteredXiFixedRadialSecondMomentFunctional W.R -
            pascalCenteredXiPrimeSideIndependentCompleteSourceReal ε W X) := by
  have hLedger :=
    pascalCenteredXiPrimeSideFiniteRectangleBackground_eq_forwardPolarized_add_independentCompletionLedger
      hε hSafe hZeta hPHZ hWeighted hρ hρm hPairLeft hPairRight hArch hElem
  have hInteraction :=
    cfzpProjectedMirrorForwardPolarizedInteractionIntegral_eq_integratedMass_difference
      hε hSafe X
  rw [hInteraction] at hLedger
  unfold cfzpIntegratedPolarizedContactThresholdLevel
    cfzpIntegratedPolarizedImbalance
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp [hpi] at hLedger
  linarith

theorem cfzpIntegratedPolarizedContactThresholdLevel_sub_imbalance_eq_independentCompleteSourceSlack :
    cfzpIntegratedPolarizedContactThresholdLevel ε X W -
        cfzpIntegratedPolarizedImbalance ε X W =
      4 * Real.pi *
        (pascalCenteredXiFixedRadialSecondMomentFunctional W.R -
          pascalCenteredXiPrimeSideIndependentCompleteSourceReal ε W X) := by
  have h :=
    cfzpIntegratedPolarizedContactThresholdLevel_eq_imbalance_add_independentCompleteSourceSlack
      hε hSafe hZeta hPHZ hWeighted hρ hρm hPairLeft hPairRight hArch hElem
  linarith

/-! ## F. Named threshold classification -/

omit hArch hElem in
theorem cfzpIntegratedPolarizedImbalance_eq_contactThreshold_iff_completionRemainder_eq_zero :
    cfzpIntegratedPolarizedImbalance ε X W =
        cfzpIntegratedPolarizedContactThresholdLevel ε X W ↔
      cfzpFiniteRectangleCompletionRemainder ε W X = 0 := by
  have h :=
    cfzpFiniteRectangleCompletionRemainder_eq_zero_iff_integratedPolarizedMass_contact_threshold
      hε hSafe hZeta hPHZ hWeighted hρ hρm hPairLeft hPairRight
  simpa [cfzpIntegratedPolarizedImbalance,
    cfzpIntegratedPolarizedContactThresholdLevel] using h.symm

theorem cfzpIntegratedPolarizedImbalance_eq_contactThreshold_iff_radialContactDeficit_eq_zero :
    cfzpIntegratedPolarizedImbalance ε X W =
        cfzpIntegratedPolarizedContactThresholdLevel ε X W ↔
      pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W X = 0 := by
  have h :=
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit_eq_zero_iff_integratedPolarizedMass_contact_threshold
      hε hSafe hZeta hPHZ hWeighted hρ hρm hPairLeft hPairRight hArch hElem
  simpa [cfzpIntegratedPolarizedImbalance,
    cfzpIntegratedPolarizedContactThresholdLevel] using h.symm

omit hArch hElem in
theorem cfzpIntegratedPolarizedImbalance_le_contactThreshold_iff_completionRemainder_nonneg :
    cfzpIntegratedPolarizedImbalance ε X W ≤
        cfzpIntegratedPolarizedContactThresholdLevel ε X W ↔
      0 ≤ cfzpFiniteRectangleCompletionRemainder ε W X := by
  have h :=
    cfzpFiniteRectangleCompletionRemainder_nonneg_iff_integratedPolarizedMass_below_contact_threshold
      hε hSafe hZeta hPHZ hWeighted hρ hρm hPairLeft hPairRight
  simpa [cfzpIntegratedPolarizedImbalance,
    cfzpIntegratedPolarizedContactThresholdLevel] using h.symm

theorem cfzpIntegratedPolarizedImbalance_le_contactThreshold_iff_radialContactDeficit_nonneg :
    cfzpIntegratedPolarizedImbalance ε X W ≤
        cfzpIntegratedPolarizedContactThresholdLevel ε X W ↔
      0 ≤ pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W X := by
  have h :=
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit_nonneg_iff_integratedPolarizedMass_below_contact_threshold
      hε hSafe hZeta hPHZ hWeighted hρ hρm hPairLeft hPairRight hArch hElem
  simpa [cfzpIntegratedPolarizedImbalance,
    cfzpIntegratedPolarizedContactThresholdLevel] using h.symm

omit hArch hElem in
theorem cfzpIntegratedPolarizedContactThreshold_le_imbalance_iff_completionRemainder_nonpos :
    cfzpIntegratedPolarizedContactThresholdLevel ε X W ≤
        cfzpIntegratedPolarizedImbalance ε X W ↔
      cfzpFiniteRectangleCompletionRemainder ε W X ≤ 0 := by
  have h :=
    cfzpFiniteRectangleCompletionRemainder_nonpos_iff_integratedPolarizedMass_above_contact_threshold
      hε hSafe hZeta hPHZ hWeighted hρ hρm hPairLeft hPairRight
  simpa [cfzpIntegratedPolarizedImbalance,
    cfzpIntegratedPolarizedContactThresholdLevel] using h.symm

theorem cfzpIntegratedPolarizedContactThreshold_le_imbalance_iff_radialContactDeficit_nonpos :
    cfzpIntegratedPolarizedContactThresholdLevel ε X W ≤
        cfzpIntegratedPolarizedImbalance ε X W ↔
      pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W X ≤ 0 := by
  have h :=
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit_nonpos_iff_integratedPolarizedMass_above_contact_threshold
      hε hSafe hZeta hPHZ hWeighted hρ hρm hPairLeft hPairRight hArch hElem
  simpa [cfzpIntegratedPolarizedImbalance,
    cfzpIntegratedPolarizedContactThresholdLevel] using h.symm

/-! ## G. Polarized balance remains distinct from contact balance -/

theorem cfzpIntegratedPolarizedContactThresholdLevel_eq_four_mul_radialContactDeficit_of_polarized_balance
    (hBal : cfzpProjectedMirrorForwardIntegratedMinusMass ε X W =
      cfzpProjectedMirrorForwardIntegratedPlusMass ε X W) :
    cfzpIntegratedPolarizedContactThresholdLevel ε X W =
      4 * pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W X := by
  have h :=
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit_eq_pi_mul_rectangleBackground_of_integratedPolarizedMass_balance
      hε hSafe hZeta hPHZ hWeighted hρ hρm hPairLeft hPairRight hArch hElem hBal
  unfold cfzpIntegratedPolarizedContactThresholdLevel
  linarith

omit hε hSafe hZeta hPHZ hWeighted hρ hρm hPairLeft hPairRight hArch hElem in
theorem cfzpIntegratedPolarizedContactThresholdLevel_eq_zero_iff_rectangleBackground_eq_zero :
    cfzpIntegratedPolarizedContactThresholdLevel ε X W = 0 ↔
      pascalCenteredXiPrimeSideFiniteRectangleBackground ε W X = 0 := by
  unfold cfzpIntegratedPolarizedContactThresholdLevel
  constructor
  · intro h
    nlinarith [Real.pi_pos]
  · intro h
    rw [h]
    ring

/-! ## H. Frontier marker -/

inductive CfzpContactThresholdLevelNonnegativityGap : Prop
  | noIndependentThresholdLevelNonnegativityProvider

end FiniteLedger

end DkMath.RH.CFBRCProjection
