/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.CosmicFormulaZetaContactThresholdDecompositionAudit
import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideCommonCarrierInteractionCancellationAudit
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CosmicFormulaZetaContactThresholdPolarizationBridgeAudit"

/-!
# CFZP-006O: source polarization threshold bridge

The signed contact slack is connected to the two existing finite ledgers:
the CS24 canonical polarization difference and the CS25 zero-cutoff versus
interaction difference.  No positivity provider is introduced.

All statements are finite.  The existing interaction-reach frontier and the
distinction from pointwise/source/zeta-zero statements are preserved.
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

/-! ## A. Signed contact slack -/

noncomputable def cfzpIntegratedPolarizedContactSlack
    (ε : ℝ) (X : ℕ)
    (W : PascalCenteredXiResidueTransportWindow) : ℝ :=
  cfzpIntegratedPolarizedContactThresholdLevel ε X W -
    cfzpIntegratedPolarizedImbalance ε X W

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

/-! ## B. Radial and completion folds -/

omit hε hSafe hZeta hPHZ hWeighted hρ hρm hPairLeft hPairRight hArch hElem in
theorem cfzpIntegratedPolarizedContactSlack_eq_threshold_sub_imbalance :
    cfzpIntegratedPolarizedContactSlack ε X W =
      cfzpIntegratedPolarizedContactThresholdLevel ε X W -
        cfzpIntegratedPolarizedImbalance ε X W := by
  rfl

theorem cfzpIntegratedPolarizedContactSlack_eq_four_mul_radialContactDeficit :
    cfzpIntegratedPolarizedContactSlack ε X W =
      4 * pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W X := by
  have h :=
    cfzpIntegratedPolarizedContactThresholdLevel_sub_imbalance_eq_four_mul_radialContactDeficit
      hε hSafe hZeta hPHZ hWeighted hρ hρm hPairLeft hPairRight hArch hElem
  exact h

omit hArch hElem in
theorem cfzpIntegratedPolarizedContactSlack_eq_four_pi_mul_completionRemainder :
    cfzpIntegratedPolarizedContactSlack ε X W =
      4 * Real.pi * cfzpFiniteRectangleCompletionRemainder ε W X := by
  have h :=
    cfzpIntegratedPolarizedContactThresholdLevel_sub_imbalance_eq_four_pi_mul_completionRemainder
      hε hSafe hZeta hPHZ hWeighted hρ hρm hPairLeft hPairRight
  exact h

/-! ## C. CS24 canonical polarization bridge -/

theorem cfzpIntegratedPolarizedContactSlack_eq_four_mul_canonicalPolarizationRemainder_sub_mass :
    cfzpIntegratedPolarizedContactSlack ε X W =
      4 *
        (pascalCenteredXiPrimeSideCanonicalPolarizationRemainder ε W X -
          pascalCenteredXiPrimeSideCanonicalPolarizationMass ε W X) := by
  have hslack :=
    cfzpIntegratedPolarizedContactSlack_eq_four_mul_radialContactDeficit
      hε hSafe hZeta hPHZ hWeighted hρ hρm hPairLeft hPairRight hArch hElem
  have hcanonical :=
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit_eq_canonicalRemainder_sub_mass
      hε W X
  rw [hcanonical] at hslack
  exact hslack

theorem cfzpIntegratedPolarizedContactThresholdLevel_eq_imbalance_add_four_mul_canonicalPolarizationSlack :
    cfzpIntegratedPolarizedContactThresholdLevel ε X W =
      cfzpIntegratedPolarizedImbalance ε X W +
        4 *
          (pascalCenteredXiPrimeSideCanonicalPolarizationRemainder ε W X -
            pascalCenteredXiPrimeSideCanonicalPolarizationMass ε W X) := by
  have hslack :=
    cfzpIntegratedPolarizedContactSlack_eq_four_mul_canonicalPolarizationRemainder_sub_mass
      hε hSafe hZeta hPHZ hWeighted hρ hρm hPairLeft hPairRight hArch hElem
  have hfold :=
    cfzpIntegratedPolarizedContactSlack_eq_threshold_sub_imbalance
      (ε := ε) (X := X) (W := W)
  linarith [hslack, hfold]

theorem cfzpIntegratedPolarizedContactSlack_eq_zero_iff_canonicalPolarization_balance :
    cfzpIntegratedPolarizedContactSlack ε X W = 0 ↔
      pascalCenteredXiPrimeSideCanonicalPolarizationRemainder ε W X =
        pascalCenteredXiPrimeSideCanonicalPolarizationMass ε W X := by
  have h :=
    cfzpIntegratedPolarizedContactSlack_eq_four_mul_canonicalPolarizationRemainder_sub_mass
      hε hSafe hZeta hPHZ hWeighted hρ hρm hPairLeft hPairRight hArch hElem
  constructor
  · intro hs
    linarith [h]
  · intro hb
    rw [hb] at h
    linarith

theorem cfzpIntegratedPolarizedContactSlack_nonneg_iff_canonicalPolarization_mass_le_remainder :
    0 ≤ cfzpIntegratedPolarizedContactSlack ε X W ↔
      pascalCenteredXiPrimeSideCanonicalPolarizationMass ε W X ≤
        pascalCenteredXiPrimeSideCanonicalPolarizationRemainder ε W X := by
  have h :=
    cfzpIntegratedPolarizedContactSlack_eq_four_mul_canonicalPolarizationRemainder_sub_mass
      hε hSafe hZeta hPHZ hWeighted hρ hρm hPairLeft hPairRight hArch hElem
  constructor
  · intro hs
    linarith [h]
  · intro hb
    linarith [h]

theorem cfzpIntegratedPolarizedContactSlack_nonpos_iff_canonicalPolarization_remainder_le_mass :
    cfzpIntegratedPolarizedContactSlack ε X W ≤ 0 ↔
      pascalCenteredXiPrimeSideCanonicalPolarizationRemainder ε W X ≤
        pascalCenteredXiPrimeSideCanonicalPolarizationMass ε W X := by
  have h :=
    cfzpIntegratedPolarizedContactSlack_eq_four_mul_canonicalPolarizationRemainder_sub_mass
      hε hSafe hZeta hPHZ hWeighted hρ hρm hPairLeft hPairRight hArch hElem
  constructor
  · intro hs
    linarith [h]
  · intro hb
    linarith [h]

theorem cfzpIntegratedPolarizedImbalance_eq_contactThreshold_iff_canonicalPolarization_balance :
    cfzpIntegratedPolarizedImbalance ε X W =
        cfzpIntegratedPolarizedContactThresholdLevel ε X W ↔
      pascalCenteredXiPrimeSideCanonicalPolarizationRemainder ε W X =
        pascalCenteredXiPrimeSideCanonicalPolarizationMass ε W X := by
  have hcontact :=
    cfzpIntegratedPolarizedImbalance_eq_contactThreshold_iff_radialContactDeficit_eq_zero
      hε hSafe hZeta hPHZ hWeighted hρ hρm hPairLeft hPairRight hArch hElem
  have hcanonical :=
    cfzpIntegratedPolarizedContactSlack_eq_zero_iff_canonicalPolarization_balance
      hε hSafe hZeta hPHZ hWeighted hρ hρm hPairLeft hPairRight hArch hElem
  have hslack :=
    cfzpIntegratedPolarizedContactSlack_eq_threshold_sub_imbalance
      (ε := ε) (X := X) (W := W)
  constructor
  · intro h
    rw [h] at hslack
    apply hcanonical.mp
    linarith [hslack]
  · intro h
    have hs := hcanonical.mpr h
    linarith [hslack, hs]

theorem cfzpIntegratedPolarizedImbalance_le_contactThreshold_iff_canonicalPolarization_mass_le_remainder :
    cfzpIntegratedPolarizedImbalance ε X W ≤
        cfzpIntegratedPolarizedContactThresholdLevel ε X W ↔
      pascalCenteredXiPrimeSideCanonicalPolarizationMass ε W X ≤
        pascalCenteredXiPrimeSideCanonicalPolarizationRemainder ε W X := by
  have hcanonical :=
    cfzpIntegratedPolarizedContactSlack_nonneg_iff_canonicalPolarization_mass_le_remainder
      hε hSafe hZeta hPHZ hWeighted hρ hρm hPairLeft hPairRight hArch hElem
  have hslack :=
    cfzpIntegratedPolarizedContactSlack_eq_threshold_sub_imbalance
      (ε := ε) (X := X) (W := W)
  constructor
  · intro h
    apply hcanonical.mp
    linarith [hslack]
  · intro h
    have hs := hcanonical.mpr h
    linarith [hslack, hs]

theorem cfzpIntegratedPolarizedContactThreshold_le_imbalance_iff_canonicalPolarization_remainder_le_mass :
    cfzpIntegratedPolarizedContactThresholdLevel ε X W ≤
        cfzpIntegratedPolarizedImbalance ε X W ↔
      pascalCenteredXiPrimeSideCanonicalPolarizationRemainder ε W X ≤
        pascalCenteredXiPrimeSideCanonicalPolarizationMass ε W X := by
  have hcanonical :=
    cfzpIntegratedPolarizedContactSlack_nonpos_iff_canonicalPolarization_remainder_le_mass
      hε hSafe hZeta hPHZ hWeighted hρ hρm hPairLeft hPairRight hArch hElem
  have hslack :=
    cfzpIntegratedPolarizedContactSlack_eq_threshold_sub_imbalance
      (ε := ε) (X := X) (W := W)
  constructor
  · intro h
    apply hcanonical.mp
    linarith [hslack]
  · intro h
    have hs := hcanonical.mpr h
    linarith [hslack, hs]

/-! ## D. CS25 zero-cutoff / interaction bridge -/

theorem cfzpIntegratedPolarizedContactSlack_eq_four_mul_zeroCutoffDeficit_sub_interaction :
    cfzpIntegratedPolarizedContactSlack ε X W =
      4 *
        (pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W 0 -
          pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W X) := by
  have hslack :=
    cfzpIntegratedPolarizedContactSlack_eq_four_mul_radialContactDeficit
      hε hSafe hZeta hPHZ hWeighted hρ hρm hPairLeft hPairRight hArch hElem
  have hinteraction :=
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit_eq_zeroCutoff_deficit_sub_interaction
      hε W X
  rw [hinteraction] at hslack
  exact hslack

theorem cfzpIntegratedPolarizedContactThresholdLevel_eq_imbalance_add_four_mul_zeroCutoffDeficit_sub_interaction :
    cfzpIntegratedPolarizedContactThresholdLevel ε X W =
      cfzpIntegratedPolarizedImbalance ε X W +
        4 *
          (pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W 0 -
            pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W X) := by
  have hslack :=
    cfzpIntegratedPolarizedContactSlack_eq_four_mul_zeroCutoffDeficit_sub_interaction
      hε hSafe hZeta hPHZ hWeighted hρ hρm hPairLeft hPairRight hArch hElem
  have hfold :=
    cfzpIntegratedPolarizedContactSlack_eq_threshold_sub_imbalance
      (ε := ε) (X := X) (W := W)
  linarith [hslack, hfold]

theorem cfzpIntegratedPolarizedContactSlack_eq_zero_iff_zeroCutoffDeficit_eq_interaction :
    cfzpIntegratedPolarizedContactSlack ε X W = 0 ↔
      pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W 0 =
        pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W X := by
  have h :=
    cfzpIntegratedPolarizedContactSlack_eq_four_mul_zeroCutoffDeficit_sub_interaction
      hε hSafe hZeta hPHZ hWeighted hρ hρm hPairLeft hPairRight hArch hElem
  constructor
  · intro hs
    linarith [h]
  · intro hb
    rw [hb] at h
    linarith

theorem cfzpIntegratedPolarizedContactSlack_nonneg_iff_interaction_le_zeroCutoffDeficit :
    0 ≤ cfzpIntegratedPolarizedContactSlack ε X W ↔
      pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W X ≤
        pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W 0 := by
  have h :=
    cfzpIntegratedPolarizedContactSlack_eq_four_mul_zeroCutoffDeficit_sub_interaction
      hε hSafe hZeta hPHZ hWeighted hρ hρm hPairLeft hPairRight hArch hElem
  constructor
  · intro hs
    linarith [h]
  · intro hb
    linarith [h]

theorem cfzpIntegratedPolarizedContactSlack_nonpos_iff_zeroCutoffDeficit_le_interaction :
    cfzpIntegratedPolarizedContactSlack ε X W ≤ 0 ↔
      pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W 0 ≤
        pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W X := by
  have h :=
    cfzpIntegratedPolarizedContactSlack_eq_four_mul_zeroCutoffDeficit_sub_interaction
      hε hSafe hZeta hPHZ hWeighted hρ hρm hPairLeft hPairRight hArch hElem
  constructor
  · intro hs
    linarith [h]
  · intro hb
    linarith [h]

theorem cfzpIntegratedPolarizedImbalance_eq_contactThreshold_iff_zeroCutoffDeficit_eq_interaction :
    cfzpIntegratedPolarizedImbalance ε X W =
        cfzpIntegratedPolarizedContactThresholdLevel ε X W ↔
      pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W 0 =
        pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W X := by
  have hcontact :=
    cfzpIntegratedPolarizedImbalance_eq_contactThreshold_iff_radialContactDeficit_eq_zero
      hε hSafe hZeta hPHZ hWeighted hρ hρm hPairLeft hPairRight hArch hElem
  have hreach :=
    cfzpIntegratedPolarizedContactSlack_eq_zero_iff_zeroCutoffDeficit_eq_interaction
      hε hSafe hZeta hPHZ hWeighted hρ hρm hPairLeft hPairRight hArch hElem
  have hslack :=
    cfzpIntegratedPolarizedContactSlack_eq_threshold_sub_imbalance
      (ε := ε) (X := X) (W := W)
  constructor
  · intro h
    rw [h] at hslack
    apply hreach.mp
    linarith [hslack]
  · intro h
    have hs := hreach.mpr h
    linarith [hslack, hs]

theorem cfzpIntegratedPolarizedImbalance_le_contactThreshold_iff_interaction_le_zeroCutoffDeficit :
    cfzpIntegratedPolarizedImbalance ε X W ≤
        cfzpIntegratedPolarizedContactThresholdLevel ε X W ↔
      pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W X ≤
        pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W 0 := by
  have hreach :=
    cfzpIntegratedPolarizedContactSlack_nonneg_iff_interaction_le_zeroCutoffDeficit
      hε hSafe hZeta hPHZ hWeighted hρ hρm hPairLeft hPairRight hArch hElem
  have hslack :=
    cfzpIntegratedPolarizedContactSlack_eq_threshold_sub_imbalance
      (ε := ε) (X := X) (W := W)
  constructor
  · intro h
    apply hreach.mp
    linarith [hslack]
  · intro h
    have hs := hreach.mpr h
    linarith [hslack, hs]

theorem cfzpIntegratedPolarizedContactThreshold_le_imbalance_iff_zeroCutoffDeficit_le_interaction :
    cfzpIntegratedPolarizedContactThresholdLevel ε X W ≤
        cfzpIntegratedPolarizedImbalance ε X W ↔
      pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W 0 ≤
        pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W X := by
  have hreach :=
    cfzpIntegratedPolarizedContactSlack_nonpos_iff_zeroCutoffDeficit_le_interaction
      hε hSafe hZeta hPHZ hWeighted hρ hρm hPairLeft hPairRight hArch hElem
  have hslack :=
    cfzpIntegratedPolarizedContactSlack_eq_threshold_sub_imbalance
      (ε := ε) (X := X) (W := W)
  constructor
  · intro h
    apply hreach.mp
    linarith [hslack]
  · intro h
    have hs := hreach.mpr h
    linarith [hslack, hs]

/-! ## E. Dual balance classification -/

theorem cfzpIntegratedPolarizedImbalance_eq_contactThreshold_iff_canonicalBalance_and_interactionReach :
    (cfzpIntegratedPolarizedImbalance ε X W =
        cfzpIntegratedPolarizedContactThresholdLevel ε X W) ↔
      (pascalCenteredXiPrimeSideCanonicalPolarizationRemainder ε W X =
          pascalCenteredXiPrimeSideCanonicalPolarizationMass ε W X ∧
        pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W 0 =
          pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W X) := by
  have hcanonical :=
    cfzpIntegratedPolarizedImbalance_eq_contactThreshold_iff_canonicalPolarization_balance
      hε hSafe hZeta hPHZ hWeighted hρ hρm hPairLeft hPairRight hArch hElem
  have hinteraction :=
    cfzpIntegratedPolarizedImbalance_eq_contactThreshold_iff_zeroCutoffDeficit_eq_interaction
      hε hSafe hZeta hPHZ hWeighted hρ hρm hPairLeft hPairRight hArch hElem
  constructor
  · intro h
    exact ⟨hcanonical.mp h, hinteraction.mp h⟩
  · rintro ⟨hc, hi⟩
    have hs := hcanonical.mpr hc
    have hslack :=
      cfzpIntegratedPolarizedContactSlack_eq_threshold_sub_imbalance
        (ε := ε) (X := X) (W := W)
    linarith [hslack, hs]

/-! ## F. Frontier markers -/

inductive CfzpContactThresholdCanonicalPolarizationDominanceGap : Prop
  | noIndependentCanonicalPolarizationDominanceProvider

inductive CfzpContactThresholdInteractionReachGap : Prop
  | noIndependentZeroCutoffInteractionReachProvider

inductive CfzpContactSlackToPrimeMirrorGapIdentificationGap : Prop
  | noExactPrimeMirrorGapIdentificationProvided

end FiniteLedger

end DkMath.RH.CFBRCProjection
