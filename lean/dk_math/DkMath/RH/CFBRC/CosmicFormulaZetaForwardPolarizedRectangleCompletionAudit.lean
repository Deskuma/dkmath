/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.CosmicFormulaZetaProjectedMirrorPolarizationAudit
import DkMath.RH.CFBRC.CosmicFormulaZetaSourceCompletionGeometryAudit
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CosmicFormulaZetaForwardPolarizedRectangleCompletionAudit"

/-!
# CFZP-006K: forward polarized rectangle completion ledger

The reverse-oriented CFZP-006J TopMismatch identity is transported to the
positive-direction interval `1 / 2 .. σ`.  Its integrand is deliberately the
signed interaction `Mminus - Mplus`.  The resulting identity is inserted
into the existing rectangle completion and radial-contact ledgers.

The completion remainder is kept independent and no sign provider is added.
The forward interaction is not called a nonnegative mass, and no separate
integrals of the two pointwise masses are introduced.
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

/-! ## A. Forward signed polarized interaction -/

noncomputable def cfzpProjectedMirrorForwardPolarizedInteractionIntegral
    (ε : ℝ) (X : ℕ)
    (W : PascalCenteredXiResidueTransportWindow) : ℝ :=
  ∫ u in (1 / 2 : ℝ)..W.rectangle.σ,
    (cfzpProjectedMirrorPolarizedMinusMass ε X W u -
      cfzpProjectedMirrorPolarizedPlusMass ε X W u) / 4

theorem pascalCenteredXiPrimeSideFiniteTopZetaMismatchScalar_eq_forwardPolarizedInteraction_div_pi
    {ε : ℝ} (hε : 0 < ε)
    {W : PascalCenteredXiResidueTransportWindow} {X : ℕ}
    (hSafe : IsPascalCenteredXiTopLogDerivDecompositionSafe W)
    (hZeta : IntervalIntegrable
      (fun u : ℝ =>
        pascalCenteredXiMellinSecondDifferenceWeight ε 0
          (pascalOrdinaryToCentered
            (pascalSymmetricRectangleTopEdge u W.rectangle.T)) *
        pascalXiOrdinaryZetaNegLogDeriv
          (pascalSymmetricRectangleTopEdge u W.rectangle.T))
      volume W.rectangle.σ (1 - W.rectangle.σ))
    (hPHZ : IntervalIntegrable
      (fun u : ℝ =>
        pascalCenteredXiMellinSecondDifferenceWeight ε 0
          (pascalOrdinaryToCentered
            (pascalSymmetricRectangleTopEdge u W.rectangle.T)) *
        pascalPrimePowerPHZFiniteUpTo X
          (pascalSymmetricRectangleTopEdge u W.rectangle.T))
      volume W.rectangle.σ (1 - W.rectangle.σ))
    (hWeighted : IntervalIntegrable
      (fun u : ℝ =>
        pascalCenteredXiPrimeSideFiniteResidualTopMellinWeight ε W u *
          pascalCenteredXiPrimeSideFiniteResidualLogRate X W u)
      volume W.rectangle.σ (1 - W.rectangle.σ))
    (hρ : IntervalIntegrable
      (pascalCenteredXiPrimeSideFiniteResidualScalarDensity ε X W)
      volume W.rectangle.σ (1 - W.rectangle.σ))
    (hρm : IntervalIntegrable
      (fun u : ℝ => pascalCenteredXiPrimeSideFiniteResidualScalarDensity
        ε X W (1 - u))
      volume W.rectangle.σ (1 - W.rectangle.σ))
    (hPairLeft : IntervalIntegrable
      (pascalCenteredXiPrimeSideFiniteResidualMirrorScalarDensity ε X W)
      volume W.rectangle.σ (1 / 2 : ℝ))
    (hPairRight : IntervalIntegrable
      (pascalCenteredXiPrimeSideFiniteResidualMirrorScalarDensity ε X W)
      volume (1 / 2 : ℝ) (1 - W.rectangle.σ)) :
    pascalCenteredXiPrimeSideFiniteTopZetaMismatchScalar ε W X =
      (1 / Real.pi) *
        cfzpProjectedMirrorForwardPolarizedInteractionIntegral ε X W := by
  have hbase :=
    pascalCenteredXiPrimeSideFiniteTopZetaMismatchScalar_eq_projectedPolarized_half_integral
      hε hSafe hZeta hPHZ hWeighted hρ hρm hPairLeft hPairRight
  rw [hbase]
  unfold cfzpProjectedMirrorForwardPolarizedInteractionIntegral
  rw [intervalIntegral.integral_symm]
  rw [← intervalIntegral.integral_neg]
  congr 1
  apply intervalIntegral.integral_congr
  intro u hu
  ring

/-! ## B. Rectangle background and completion remainder -/

theorem pascalCenteredXiPrimeSideFiniteRectangleBackground_eq_forwardPolarized_add_completionRemainder
    {ε : ℝ} (hε : 0 < ε)
    {W : PascalCenteredXiResidueTransportWindow} {X : ℕ}
    (hSafe : IsPascalCenteredXiTopLogDerivDecompositionSafe W)
    (hZeta : IntervalIntegrable
      (fun u : ℝ =>
        pascalCenteredXiMellinSecondDifferenceWeight ε 0
          (pascalOrdinaryToCentered
            (pascalSymmetricRectangleTopEdge u W.rectangle.T)) *
        pascalXiOrdinaryZetaNegLogDeriv
          (pascalSymmetricRectangleTopEdge u W.rectangle.T))
      volume W.rectangle.σ (1 - W.rectangle.σ))
    (hPHZ : IntervalIntegrable
      (fun u : ℝ =>
        pascalCenteredXiMellinSecondDifferenceWeight ε 0
          (pascalOrdinaryToCentered
            (pascalSymmetricRectangleTopEdge u W.rectangle.T)) *
        pascalPrimePowerPHZFiniteUpTo X
          (pascalSymmetricRectangleTopEdge u W.rectangle.T))
      volume W.rectangle.σ (1 - W.rectangle.σ))
    (hWeighted : IntervalIntegrable
      (fun u : ℝ =>
        pascalCenteredXiPrimeSideFiniteResidualTopMellinWeight ε W u *
          pascalCenteredXiPrimeSideFiniteResidualLogRate X W u)
      volume W.rectangle.σ (1 - W.rectangle.σ))
    (hρ : IntervalIntegrable
      (pascalCenteredXiPrimeSideFiniteResidualScalarDensity ε X W)
      volume W.rectangle.σ (1 - W.rectangle.σ))
    (hρm : IntervalIntegrable
      (fun u : ℝ => pascalCenteredXiPrimeSideFiniteResidualScalarDensity
        ε X W (1 - u))
      volume W.rectangle.σ (1 - W.rectangle.σ))
    (hPairLeft : IntervalIntegrable
      (pascalCenteredXiPrimeSideFiniteResidualMirrorScalarDensity ε X W)
      volume W.rectangle.σ (1 / 2 : ℝ))
    (hPairRight : IntervalIntegrable
      (pascalCenteredXiPrimeSideFiniteResidualMirrorScalarDensity ε X W)
      volume (1 / 2 : ℝ) (1 - W.rectangle.σ)) :
    pascalCenteredXiPrimeSideFiniteRectangleBackground ε W X =
      (1 / Real.pi) *
          cfzpProjectedMirrorForwardPolarizedInteractionIntegral ε X W +
        cfzpFiniteRectangleCompletionRemainder ε W X := by
  rw [cfzpFiniteRectangleBackground_eq_mismatch_add_completionRemainder]
  rw [pascalCenteredXiPrimeSideFiniteTopZetaMismatchScalar_eq_forwardPolarizedInteraction_div_pi
    hε hSafe hZeta hPHZ hWeighted hρ hρm hPairLeft hPairRight]

theorem cfzpFiniteRectangleCompletionRemainder_eq_background_sub_forwardPolarized
    {ε : ℝ} (hε : 0 < ε)
    {W : PascalCenteredXiResidueTransportWindow} {X : ℕ}
    (hSafe : IsPascalCenteredXiTopLogDerivDecompositionSafe W)
    (hZeta : IntervalIntegrable
      (fun u : ℝ =>
        pascalCenteredXiMellinSecondDifferenceWeight ε 0
          (pascalOrdinaryToCentered
            (pascalSymmetricRectangleTopEdge u W.rectangle.T)) *
        pascalXiOrdinaryZetaNegLogDeriv
          (pascalSymmetricRectangleTopEdge u W.rectangle.T))
      volume W.rectangle.σ (1 - W.rectangle.σ))
    (hPHZ : IntervalIntegrable
      (fun u : ℝ =>
        pascalCenteredXiMellinSecondDifferenceWeight ε 0
          (pascalOrdinaryToCentered
            (pascalSymmetricRectangleTopEdge u W.rectangle.T)) *
        pascalPrimePowerPHZFiniteUpTo X
          (pascalSymmetricRectangleTopEdge u W.rectangle.T))
      volume W.rectangle.σ (1 - W.rectangle.σ))
    (hWeighted : IntervalIntegrable
      (fun u : ℝ =>
        pascalCenteredXiPrimeSideFiniteResidualTopMellinWeight ε W u *
          pascalCenteredXiPrimeSideFiniteResidualLogRate X W u)
      volume W.rectangle.σ (1 - W.rectangle.σ))
    (hρ : IntervalIntegrable
      (pascalCenteredXiPrimeSideFiniteResidualScalarDensity ε X W)
      volume W.rectangle.σ (1 - W.rectangle.σ))
    (hρm : IntervalIntegrable
      (fun u : ℝ => pascalCenteredXiPrimeSideFiniteResidualScalarDensity
        ε X W (1 - u))
      volume W.rectangle.σ (1 - W.rectangle.σ))
    (hPairLeft : IntervalIntegrable
      (pascalCenteredXiPrimeSideFiniteResidualMirrorScalarDensity ε X W)
      volume W.rectangle.σ (1 / 2 : ℝ))
    (hPairRight : IntervalIntegrable
      (pascalCenteredXiPrimeSideFiniteResidualMirrorScalarDensity ε X W)
      volume (1 / 2 : ℝ) (1 - W.rectangle.σ)) :
    cfzpFiniteRectangleCompletionRemainder ε W X =
      pascalCenteredXiPrimeSideFiniteRectangleBackground ε W X -
        (1 / Real.pi) *
          cfzpProjectedMirrorForwardPolarizedInteractionIntegral ε X W := by
  unfold cfzpFiniteRectangleCompletionRemainder
  rw [pascalCenteredXiPrimeSideFiniteTopZetaMismatchScalar_eq_forwardPolarizedInteraction_div_pi
    hε hSafe hZeta hPHZ hWeighted hρ hρm hPairLeft hPairRight]

/-! ## C. Direct radial-contact ledger -/

theorem pascalCenteredXiPrimeSideFiniteRadialContactDeficit_eq_pi_mul_background_sub_forwardPolarized
    {ε : ℝ} (hε : 0 < ε)
    {W : PascalCenteredXiResidueTransportWindow} {X : ℕ}
    (hSafe : IsPascalCenteredXiTopLogDerivDecompositionSafe W)
    (hZeta : IntervalIntegrable
      (fun u : ℝ =>
        pascalCenteredXiMellinSecondDifferenceWeight ε 0
          (pascalOrdinaryToCentered
            (pascalSymmetricRectangleTopEdge u W.rectangle.T)) *
        pascalXiOrdinaryZetaNegLogDeriv
          (pascalSymmetricRectangleTopEdge u W.rectangle.T))
      volume W.rectangle.σ (1 - W.rectangle.σ))
    (hPHZ : IntervalIntegrable
      (fun u : ℝ =>
        pascalCenteredXiMellinSecondDifferenceWeight ε 0
          (pascalOrdinaryToCentered
            (pascalSymmetricRectangleTopEdge u W.rectangle.T)) *
        pascalPrimePowerPHZFiniteUpTo X
          (pascalSymmetricRectangleTopEdge u W.rectangle.T))
      volume W.rectangle.σ (1 - W.rectangle.σ))
    (hWeighted : IntervalIntegrable
      (fun u : ℝ =>
        pascalCenteredXiPrimeSideFiniteResidualTopMellinWeight ε W u *
          pascalCenteredXiPrimeSideFiniteResidualLogRate X W u)
      volume W.rectangle.σ (1 - W.rectangle.σ))
    (hρ : IntervalIntegrable
      (pascalCenteredXiPrimeSideFiniteResidualScalarDensity ε X W)
      volume W.rectangle.σ (1 - W.rectangle.σ))
    (hρm : IntervalIntegrable
      (fun u : ℝ => pascalCenteredXiPrimeSideFiniteResidualScalarDensity
        ε X W (1 - u))
      volume W.rectangle.σ (1 - W.rectangle.σ))
    (hPairLeft : IntervalIntegrable
      (pascalCenteredXiPrimeSideFiniteResidualMirrorScalarDensity ε X W)
      volume W.rectangle.σ (1 / 2 : ℝ))
    (hPairRight : IntervalIntegrable
      (pascalCenteredXiPrimeSideFiniteResidualMirrorScalarDensity ε X W)
      volume (1 / 2 : ℝ) (1 - W.rectangle.σ))
    (hArch : IntervalIntegrable
      (fun u : ℝ =>
        pascalCenteredXiMellinSecondDifferenceWeight ε 0
          (pascalOrdinaryToCentered
            (pascalSymmetricRectangleTopEdge u W.rectangle.T)) *
        pascalXiArchimedeanLogDeriv
          (pascalSymmetricRectangleTopEdge u W.rectangle.T))
      volume W.rectangle.σ (1 - W.rectangle.σ))
    (hElem : IntervalIntegrable
      (fun u : ℝ =>
        pascalCenteredXiMellinSecondDifferenceWeight ε 0
          (pascalOrdinaryToCentered
            (pascalSymmetricRectangleTopEdge u W.rectangle.T)) *
        pascalXiElementaryLogDerivCorrection
          (pascalSymmetricRectangleTopEdge u W.rectangle.T))
      volume W.rectangle.σ (1 - W.rectangle.σ)) :
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W X =
      Real.pi * pascalCenteredXiPrimeSideFiniteRectangleBackground ε W X -
        cfzpProjectedMirrorForwardPolarizedInteractionIntegral ε X W := by
  rw [cfzpFiniteRadialContactDeficit_eq_pi_mul_completionRemainder
    hε hSafe hZeta hArch hElem X]
  rw [cfzpFiniteRectangleCompletionRemainder_eq_background_sub_forwardPolarized
    hε hSafe hZeta hPHZ hWeighted hρ hρm hPairLeft hPairRight]
  field_simp [Real.pi_ne_zero]

/-! ## D. Independent completion ledger -/

theorem pascalCenteredXiPrimeSideFiniteRectangleBackground_eq_forwardPolarized_add_independentCompletionLedger
    {ε : ℝ} (hε : 0 < ε)
    {W : PascalCenteredXiResidueTransportWindow} {X : ℕ}
    (hSafe : IsPascalCenteredXiTopLogDerivDecompositionSafe W)
    (hZeta : IntervalIntegrable
      (fun u : ℝ =>
        pascalCenteredXiMellinSecondDifferenceWeight ε 0
          (pascalOrdinaryToCentered
            (pascalSymmetricRectangleTopEdge u W.rectangle.T)) *
        pascalXiOrdinaryZetaNegLogDeriv
          (pascalSymmetricRectangleTopEdge u W.rectangle.T))
      volume W.rectangle.σ (1 - W.rectangle.σ))
    (hPHZ : IntervalIntegrable
      (fun u : ℝ =>
        pascalCenteredXiMellinSecondDifferenceWeight ε 0
          (pascalOrdinaryToCentered
            (pascalSymmetricRectangleTopEdge u W.rectangle.T)) *
        pascalPrimePowerPHZFiniteUpTo X
          (pascalSymmetricRectangleTopEdge u W.rectangle.T))
      volume W.rectangle.σ (1 - W.rectangle.σ))
    (hWeighted : IntervalIntegrable
      (fun u : ℝ =>
        pascalCenteredXiPrimeSideFiniteResidualTopMellinWeight ε W u *
          pascalCenteredXiPrimeSideFiniteResidualLogRate X W u)
      volume W.rectangle.σ (1 - W.rectangle.σ))
    (hρ : IntervalIntegrable
      (pascalCenteredXiPrimeSideFiniteResidualScalarDensity ε X W)
      volume W.rectangle.σ (1 - W.rectangle.σ))
    (hρm : IntervalIntegrable
      (fun u : ℝ => pascalCenteredXiPrimeSideFiniteResidualScalarDensity
        ε X W (1 - u))
      volume W.rectangle.σ (1 - W.rectangle.σ))
    (hPairLeft : IntervalIntegrable
      (pascalCenteredXiPrimeSideFiniteResidualMirrorScalarDensity ε X W)
      volume W.rectangle.σ (1 / 2 : ℝ))
    (hPairRight : IntervalIntegrable
      (pascalCenteredXiPrimeSideFiniteResidualMirrorScalarDensity ε X W)
      volume (1 / 2 : ℝ) (1 - W.rectangle.σ))
    (hArch : IntervalIntegrable
      (fun u : ℝ =>
        pascalCenteredXiMellinSecondDifferenceWeight ε 0
          (pascalOrdinaryToCentered
            (pascalSymmetricRectangleTopEdge u W.rectangle.T)) *
        pascalXiArchimedeanLogDeriv
          (pascalSymmetricRectangleTopEdge u W.rectangle.T))
      volume W.rectangle.σ (1 - W.rectangle.σ))
    (hElem : IntervalIntegrable
      (fun u : ℝ =>
        pascalCenteredXiMellinSecondDifferenceWeight ε 0
          (pascalOrdinaryToCentered
            (pascalSymmetricRectangleTopEdge u W.rectangle.T)) *
        pascalXiElementaryLogDerivCorrection
          (pascalSymmetricRectangleTopEdge u W.rectangle.T))
      volume W.rectangle.σ (1 - W.rectangle.σ)) :
    pascalCenteredXiPrimeSideFiniteRectangleBackground ε W X =
      (1 / Real.pi) *
          cfzpProjectedMirrorForwardPolarizedInteractionIntegral ε X W +
        pascalCenteredXiFixedRadialSecondMomentFunctional W.R -
          pascalCenteredXiPrimeSideIndependentCompleteSourceReal ε W X := by
  rw [pascalCenteredXiPrimeSideFiniteRectangleBackground_eq_forwardPolarized_add_completionRemainder
    hε hSafe hZeta hPHZ hWeighted hρ hρm hPairLeft hPairRight]
  rw [cfzpFiniteRectangleCompletionRemainder_eq_radialMoment_sub_completeSource
    hε hSafe hZeta hArch hElem X]
  ring

end DkMath.RH.CFBRCProjection
