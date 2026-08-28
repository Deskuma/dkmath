/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.CosmicFormulaZetaZeroCutoffContactBaselineAudit
import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideWholeSurfaceEnergyAudit
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CosmicFormulaZetaZeroCutoffRadialBudgetAudit"

/-!
# CFZP-006Q: zero-cutoff radial budget and correction orientation

The finite contact ledger is rewritten as a signed radial-budget balance:

`π * radial reference = π * correction source + prime-side interaction`.

The radial reference is nonnegative on a safe finite window.  The correction
source and the interaction remain signed, and this module supplies no
dominance, monotonicity, reach, source-zero, zeta-zero, or RH theorem.
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

/-! ## A. Radial budget reference -/

theorem cfzpFixedRadialSecondMomentFunctional_nonneg
    (W : PascalCenteredXiResidueTransportWindow) :
    0 ≤ pascalCenteredXiFixedRadialSecondMomentFunctional W.R := by
  exact pascalCenteredXiFixedRadialSecondMomentFunctional_nonneg W.circle_safe

/-! ## B. Oriented correction scalar -/

theorem cfzpPiMulIndependentCorrectionSourceReal_eq_orientedCorrectionScalar
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) :
    Real.pi * pascalCenteredXiPrimeSideIndependentCorrectionSourceReal ε W =
      (pascalCenteredXiVerticalDeorient
        (pascalCenteredXiMellinQuadraticOrientedArchimedeanSurface ε W)).re +
      (pascalCenteredXiVerticalDeorient
        (pascalCenteredXiMellinQuadraticOrientedElementarySurface ε W)).re +
      (pascalCenteredXiMellinQuadraticHorizontalBase ε W).im := by
  have harch :=
    pascalCenteredXiMellinQuadraticOrientedArchimedeanSurface_deorient_re_eq_pi_mul_normalized
      ε W
  have helem :=
    pascalCenteredXiMellinQuadraticOrientedElementarySurface_deorient_re_eq_pi_mul_normalized
      ε W
  have htop :=
    pascalCenteredXiMellinQuadraticNormalizedTopContribution_eq_im_div_pi ε W
  change Real.pi *
      (pascalCenteredXiMellinQuadraticNormalizedArchimedeanContribution ε W +
        pascalCenteredXiMellinQuadraticNormalizedElementaryContribution ε W +
        pascalCenteredXiMellinQuadraticNormalizedTopContribution ε W) = _
  rw [harch, helem]
  have htop' :
      pascalCenteredXiMellinQuadraticNormalizedTopContribution ε W =
        (pascalCenteredXiMellinQuadraticHorizontalBase ε W).im / Real.pi := by
    simpa [pascalCenteredXiMellinQuadraticHorizontalBase] using htop
  rw [htop']
  field_simp [Real.pi_ne_zero]

/-! ## C. Baseline as radial budget minus oriented correction -/

theorem cfzpZeroCutoffRadialContactBaseline_eq_radialBudget_sub_orientedCorrectionScalar
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) :
    cfzpZeroCutoffRadialContactBaseline ε W =
      Real.pi * pascalCenteredXiFixedRadialSecondMomentFunctional W.R -
        ((pascalCenteredXiVerticalDeorient
          (pascalCenteredXiMellinQuadraticOrientedArchimedeanSurface ε W)).re +
          (pascalCenteredXiVerticalDeorient
            (pascalCenteredXiMellinQuadraticOrientedElementarySurface ε W)).re +
          (pascalCenteredXiMellinQuadraticHorizontalBase ε W).im) := by
  have hbase :=
    cfzpZeroCutoffRadialContactBaseline_eq_pi_mul_fixedMoment_sub_correctionSource
      hε W
  have horiented := cfzpPiMulIndependentCorrectionSourceReal_eq_orientedCorrectionScalar ε W
  calc
    cfzpZeroCutoffRadialContactBaseline ε W =
        Real.pi *
          (pascalCenteredXiFixedRadialSecondMomentFunctional W.R -
            pascalCenteredXiPrimeSideIndependentCorrectionSourceReal ε W) := hbase
    _ = Real.pi * pascalCenteredXiFixedRadialSecondMomentFunctional W.R -
          Real.pi * pascalCenteredXiPrimeSideIndependentCorrectionSourceReal ε W := by ring
    _ = Real.pi * pascalCenteredXiFixedRadialSecondMomentFunctional W.R -
          ((pascalCenteredXiVerticalDeorient
            (pascalCenteredXiMellinQuadraticOrientedArchimedeanSurface ε W)).re +
            (pascalCenteredXiVerticalDeorient
              (pascalCenteredXiMellinQuadraticOrientedElementarySurface ε W)).re +
            (pascalCenteredXiMellinQuadraticHorizontalBase ε W).im) := by rw [horiented]

/-! ## D. Radial-budget residual -/

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

theorem cfzpIntegratedPolarizedContactSlack_eq_four_mul_radialBudgetResidual :
    cfzpIntegratedPolarizedContactSlack ε X W =
      4 *
        (Real.pi * pascalCenteredXiFixedRadialSecondMomentFunctional W.R -
          (Real.pi * pascalCenteredXiPrimeSideIndependentCorrectionSourceReal ε W +
            pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W X)) := by
  have hslack :=
    cfzpIntegratedPolarizedContactSlack_eq_four_mul_zeroCutoffBaseline_sub_interaction
      hε hSafe hZeta hPHZ hWeighted hρ hρm hPairLeft hPairRight hArch hElem
  have hbase :=
    cfzpZeroCutoffRadialContactBaseline_eq_pi_mul_fixedMoment_sub_correctionSource
      hε W
  calc
    cfzpIntegratedPolarizedContactSlack ε X W =
        4 *
          (cfzpZeroCutoffRadialContactBaseline ε W -
            pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W X) := hslack
    _ = 4 *
        (Real.pi * pascalCenteredXiFixedRadialSecondMomentFunctional W.R -
          (Real.pi * pascalCenteredXiPrimeSideIndependentCorrectionSourceReal ε W +
            pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W X)) := by
      rw [hbase]
      ring

theorem cfzpIntegratedPolarizedContactSlack_eq_zero_iff_radialBudget_balance :
    cfzpIntegratedPolarizedContactSlack ε X W = 0 ↔
      Real.pi * pascalCenteredXiFixedRadialSecondMomentFunctional W.R =
        Real.pi * pascalCenteredXiPrimeSideIndependentCorrectionSourceReal ε W +
          pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W X := by
  have h :=
    cfzpIntegratedPolarizedContactSlack_eq_four_mul_radialBudgetResidual
      hε hSafe hZeta hPHZ hWeighted hρ hρm hPairLeft hPairRight hArch hElem
  constructor
  · intro hs
    linarith [h]
  · intro hb
    rw [hb] at h
    norm_num at h ⊢
    exact h

theorem cfzpIntegratedPolarizedImbalance_eq_contactThreshold_iff_radialBudget_balance :
    cfzpIntegratedPolarizedImbalance ε X W =
        cfzpIntegratedPolarizedContactThresholdLevel ε X W ↔
      Real.pi * pascalCenteredXiFixedRadialSecondMomentFunctional W.R =
        Real.pi * pascalCenteredXiPrimeSideIndependentCorrectionSourceReal ε W +
          pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W X := by
  have hcontact :=
    cfzpIntegratedPolarizedImbalance_eq_contactThreshold_iff_interaction_reaches_zeroCutoffBaseline
      hε hSafe hZeta hPHZ hWeighted hρ hρm hPairLeft hPairRight hArch hElem
  have hbase :=
    cfzpZeroCutoffRadialContactBaseline_eq_pi_mul_fixedMoment_sub_correctionSource
      hε W
  rw [hbase] at hcontact
  constructor
  · intro h
    have hi := hcontact.mp h
    linarith
  · intro h
    apply hcontact.mpr
    linarith

/-! ## E. Radial-budget order classification -/

theorem cfzpIntegratedPolarizedContactSlack_nonneg_iff_radialBudget_order :
    0 ≤ cfzpIntegratedPolarizedContactSlack ε X W ↔
      Real.pi * pascalCenteredXiPrimeSideIndependentCorrectionSourceReal ε W +
          pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W X ≤
        Real.pi * pascalCenteredXiFixedRadialSecondMomentFunctional W.R := by
  have h :=
    cfzpIntegratedPolarizedContactSlack_eq_four_mul_radialBudgetResidual
      hε hSafe hZeta hPHZ hWeighted hρ hρm hPairLeft hPairRight hArch hElem
  constructor
  · intro hs
    linarith [h]
  · intro hs
    linarith [h]

theorem cfzpIntegratedPolarizedContactSlack_nonpos_iff_radialBudget_order :
    cfzpIntegratedPolarizedContactSlack ε X W ≤ 0 ↔
      Real.pi * pascalCenteredXiFixedRadialSecondMomentFunctional W.R ≤
        Real.pi * pascalCenteredXiPrimeSideIndependentCorrectionSourceReal ε W +
          pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W X := by
  have h :=
    cfzpIntegratedPolarizedContactSlack_eq_four_mul_radialBudgetResidual
      hε hSafe hZeta hPHZ hWeighted hρ hρm hPairLeft hPairRight hArch hElem
  constructor
  · intro hs
    linarith [h]
  · intro hs
    linarith [h]

theorem cfzpIntegratedPolarizedImbalance_le_contactThreshold_iff_radialBudget_order :
    cfzpIntegratedPolarizedImbalance ε X W ≤
        cfzpIntegratedPolarizedContactThresholdLevel ε X W ↔
      Real.pi * pascalCenteredXiPrimeSideIndependentCorrectionSourceReal ε W +
          pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W X ≤
        Real.pi * pascalCenteredXiFixedRadialSecondMomentFunctional W.R := by
  have horder :=
    cfzpIntegratedPolarizedContactSlack_nonneg_iff_radialBudget_order
      hε hSafe hZeta hPHZ hWeighted hρ hρm hPairLeft hPairRight hArch hElem
  have hfold :=
    cfzpIntegratedPolarizedContactSlack_eq_threshold_sub_imbalance
      (ε := ε) (X := X) (W := W)
  constructor
  · intro h
    apply horder.mp
    linarith [hfold]
  · intro h
    have hs := horder.mpr h
    linarith [hfold, hs]

theorem cfzpIntegratedPolarizedContactThreshold_le_imbalance_iff_radialBudget_order :
    cfzpIntegratedPolarizedContactThresholdLevel ε X W ≤
        cfzpIntegratedPolarizedImbalance ε X W ↔
      Real.pi * pascalCenteredXiFixedRadialSecondMomentFunctional W.R ≤
        Real.pi * pascalCenteredXiPrimeSideIndependentCorrectionSourceReal ε W +
          pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W X := by
  have horder :=
    cfzpIntegratedPolarizedContactSlack_nonpos_iff_radialBudget_order
      hε hSafe hZeta hPHZ hWeighted hρ hρm hPairLeft hPairRight hArch hElem
  have hfold :=
    cfzpIntegratedPolarizedContactSlack_eq_threshold_sub_imbalance
      (ε := ε) (X := X) (W := W)
  constructor
  · intro h
    apply horder.mp
    linarith [hfold]
  · intro h
    have hs := horder.mpr h
    linarith [hfold, hs]

/-! ## F. Component-expanded radial budget -/

theorem cfzpIntegratedPolarizedImbalance_eq_contactThreshold_iff_componentExpandedRadialBudget_balance :
    cfzpIntegratedPolarizedImbalance ε X W =
        cfzpIntegratedPolarizedContactThresholdLevel ε X W ↔
      Real.pi * pascalCenteredXiFixedRadialSecondMomentFunctional W.R =
        Real.pi * pascalCenteredXiMellinQuadraticNormalizedArchimedeanContribution ε W +
          Real.pi * pascalCenteredXiMellinQuadraticNormalizedElementaryContribution ε W +
          Real.pi * pascalCenteredXiMellinQuadraticNormalizedTopContribution ε W +
          pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W X := by
  have hbalance :=
    cfzpIntegratedPolarizedImbalance_eq_contactThreshold_iff_radialBudget_balance
      hε hSafe hZeta hPHZ hWeighted hρ hρm hPairLeft hPairRight hArch hElem
  have hcomponents :=
    cfzpIndependentCorrectionSourceReal_eq_archimedean_add_elementary_add_top ε W
  constructor
  · intro h
    have hb := hbalance.mp h
    rw [hcomponents] at hb
    simpa [mul_add, add_assoc] using hb
  · intro h
    apply hbalance.mpr
    rw [hcomponents]
    simpa [mul_add, add_assoc] using h

end FiniteLedger

/-! ## G. Explicit quantitative frontiers -/

inductive CfzpZeroCutoffRadialBudgetDominanceGap : Prop
  | noIndependentCorrectionPlusInteractionLeRadialBudgetProvider

inductive CfzpZeroCutoffCorrectionComponentSignGap : Prop
  | noIndependentArchimedeanElementaryTopSignProvider

end DkMath.RH.CFBRCProjection
