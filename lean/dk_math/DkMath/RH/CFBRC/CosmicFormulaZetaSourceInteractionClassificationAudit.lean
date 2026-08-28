/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.CosmicFormulaZetaSourceCompletionGeometryAudit
import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideCommonCarrierInteractionCancellationAudit
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CosmicFormulaZetaSourceInteractionClassificationAudit"

/-!
# CFZP-006B: source interaction classification audit

The finite rectangle completion remainder is classified here as a normalized
zero-cutoff baseline minus a signed ray interaction.  The same interaction is
also the difference of two positive integrated ray energies, so the remainder
has the signed polarization form `baseline + minus mass - plus mass`.

The two positive ray energies are CS24/CS25 geometric observables.  They are
not identified with the CFZP-004 amplitude plus/minus ledger.  No
nonnegative-gap conclusion, quadratic Gram form, norm-square sum expansion,
or RH statement is introduced.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.Analysis
open DkMath.NumberTheory
open DkMath.NumberTheory.PrimitiveSet
open MeasureTheory
open Set
open scoped ComplexConjugate Interval Topology

/-! ## Normalized source quantities -/

/-- The zero-cutoff radial deficit, normalized by `π`. -/
noncomputable def cfzpFiniteSourceZeroCutoffBaseline
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) : ℝ :=
  pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W 0 / Real.pi

/-- The signed aggregate ray interaction, normalized by `π`. -/
noncomputable def cfzpFiniteSourceInteraction
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (X : ℕ) : ℝ :=
  pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W X / Real.pi

/-- The positive aggregate ray plus energy, normalized by `2π`. -/
noncomputable def cfzpFiniteSourcePlusMass
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (X : ℕ) : ℝ :=
  pascalCenteredXiPrimeSideAggregateRayPlusEnergy ε W X /
    (2 * Real.pi)

/-- The positive aggregate ray minus energy, normalized by `2π`. -/
noncomputable def cfzpFiniteSourceMinusMass
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (X : ℕ) : ℝ :=
  pascalCenteredXiPrimeSideAggregateRayMinusEnergy ε W X /
    (2 * Real.pi)

/-! ## Completion remainder as baseline minus signed interaction -/

theorem cfzpFiniteRectangleCompletionRemainder_eq_baseline_sub_interaction
    {ε : ℝ} (hε : 0 < ε)
    {W : PascalCenteredXiResidueTransportWindow}
    (hSafe : IsPascalCenteredXiTopLogDerivDecompositionSafe W)
    (hZeta : IntervalIntegrable
      (fun u : ℝ =>
        pascalCenteredXiMellinSecondDifferenceWeight ε 0
          (pascalOrdinaryToCentered
            (pascalSymmetricRectangleTopEdge u W.rectangle.T)) *
        pascalXiOrdinaryZetaNegLogDeriv
          (pascalSymmetricRectangleTopEdge u W.rectangle.T))
      volume W.rectangle.σ (1 - W.rectangle.σ))
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
      volume W.rectangle.σ (1 - W.rectangle.σ))
    (X : ℕ) :
    cfzpFiniteRectangleCompletionRemainder ε W X =
      cfzpFiniteSourceZeroCutoffBaseline ε W -
        cfzpFiniteSourceInteraction ε W X := by
  have hR := cfzpFiniteRectangleCompletionRemainder_eq_radialDeficit_div_pi
    hε hSafe hZeta hArch hElem X
  have hI := pascalCenteredXiPrimeSideFiniteRadialContactDeficit_eq_zeroCutoff_deficit_sub_interaction
    hε W X
  calc
    cfzpFiniteRectangleCompletionRemainder ε W X =
        pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W X / Real.pi := hR
    _ = (pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W 0 -
          pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W X) /
        Real.pi := by rw [hI]
    _ = cfzpFiniteSourceZeroCutoffBaseline ε W -
          cfzpFiniteSourceInteraction ε W X := by
      unfold cfzpFiniteSourceZeroCutoffBaseline cfzpFiniteSourceInteraction
      ring

/-! ## Signed interaction as plus mass minus minus mass -/

theorem cfzpFiniteSourceInteraction_eq_plusMass_sub_minusMass
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    cfzpFiniteSourceInteraction ε W X =
      cfzpFiniteSourcePlusMass ε W X -
        cfzpFiniteSourceMinusMass ε W X := by
  unfold cfzpFiniteSourceInteraction cfzpFiniteSourcePlusMass
    cfzpFiniteSourceMinusMass
  rw [pascalCenteredXiPrimeSideAggregateRayPlusEnergy_eq_common_add_interaction
      hε W X,
    pascalCenteredXiPrimeSideAggregateRayMinusEnergy_eq_common_sub_interaction
      hε W X]
  ring

/-! ## Canonical signed polarization form -/

theorem cfzpFiniteRectangleCompletionRemainder_eq_baseline_add_minusMass_sub_plusMass
    {ε : ℝ} (hε : 0 < ε)
    {W : PascalCenteredXiResidueTransportWindow}
    (hSafe : IsPascalCenteredXiTopLogDerivDecompositionSafe W)
    (hZeta : IntervalIntegrable
      (fun u : ℝ =>
        pascalCenteredXiMellinSecondDifferenceWeight ε 0
          (pascalOrdinaryToCentered
            (pascalSymmetricRectangleTopEdge u W.rectangle.T)) *
        pascalXiOrdinaryZetaNegLogDeriv
          (pascalSymmetricRectangleTopEdge u W.rectangle.T))
      volume W.rectangle.σ (1 - W.rectangle.σ))
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
      volume W.rectangle.σ (1 - W.rectangle.σ))
    (X : ℕ) :
    cfzpFiniteRectangleCompletionRemainder ε W X =
      cfzpFiniteSourceZeroCutoffBaseline ε W +
        cfzpFiniteSourceMinusMass ε W X -
          cfzpFiniteSourcePlusMass ε W X := by
  rw [cfzpFiniteRectangleCompletionRemainder_eq_baseline_sub_interaction
    hε hSafe hZeta hArch hElem X,
    cfzpFiniteSourceInteraction_eq_plusMass_sub_minusMass hε W X]
  ring

/-! ## Positive whole masses -/

theorem cfzpFiniteSourcePlusMass_nonneg
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    0 ≤ cfzpFiniteSourcePlusMass ε W X := by
  unfold cfzpFiniteSourcePlusMass
  exact div_nonneg
    (pascalCenteredXiPrimeSideAggregateRayPlusEnergy_nonneg hε W X)
    (by positivity)

theorem cfzpFiniteSourceMinusMass_nonneg
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    0 ≤ cfzpFiniteSourceMinusMass ε W X := by
  unfold cfzpFiniteSourceMinusMass
  exact div_nonneg
    (pascalCenteredXiPrimeSideAggregateRayMinusEnergy_nonneg hε W X)
    (by positivity)

/-! ## Optional common-carrier wrapper -/

noncomputable def cfzpFiniteSourceCommonMass
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (X : ℕ) : ℝ :=
  pascalCenteredXiPrimeSideAggregateRayCommonEnergy ε W X /
    (2 * Real.pi)

theorem cfzpFiniteSourcePlusMass_eq_commonMass_add_half_interaction
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    cfzpFiniteSourcePlusMass ε W X =
      cfzpFiniteSourceCommonMass ε W X +
        cfzpFiniteSourceInteraction ε W X / 2 := by
  unfold cfzpFiniteSourcePlusMass cfzpFiniteSourceCommonMass
    cfzpFiniteSourceInteraction
  rw [pascalCenteredXiPrimeSideAggregateRayPlusEnergy_eq_common_add_interaction
    hε W X]
  ring

theorem cfzpFiniteSourceMinusMass_eq_commonMass_sub_half_interaction
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    cfzpFiniteSourceMinusMass ε W X =
      cfzpFiniteSourceCommonMass ε W X -
        cfzpFiniteSourceInteraction ε W X / 2 := by
  unfold cfzpFiniteSourceMinusMass cfzpFiniteSourceCommonMass
    cfzpFiniteSourceInteraction
  rw [pascalCenteredXiPrimeSideAggregateRayMinusEnergy_eq_common_sub_interaction
    hε W X]
  ring

/-! The sign of the remainder is intentionally left provider-dependent. -/

inductive CfzpSourcePositiveGapIdentificationGap : Prop
  | noQuadraticNonnegativeSourceGapProvider

end DkMath.RH.CFBRCProjection
