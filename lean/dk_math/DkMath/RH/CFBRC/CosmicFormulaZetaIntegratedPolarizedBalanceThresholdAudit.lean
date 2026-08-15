/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.CosmicFormulaZetaForwardIntegratedPolarizedMassAudit
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CosmicFormulaZetaIntegratedPolarizedBalanceThresholdAudit"

/-!
# CFZP-006M: integrated polarized balance threshold audit

The forward integrated masses are nonnegative individually, but their
difference is signed.  This file separates the polarized balance
`Pminus = Pplus` from the radial-contact threshold
`Pminus - Pplus = 4 * pi * RectangleBackground`.

Only exact finite ledger translations are recorded.  No completion or
radial sign provider, pointwise balance, source-zero statement, zeta-zero
identification, infinite limit, or RH consequence is introduced.
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

/-! ## A. Pure arithmetic threshold lemmas -/

private theorem cFZP_completion_zero_iff_threshold
    {B R Δ : ℝ}
    (hLedger : B = (1 / Real.pi) * (Δ / 4) + R) :
    R = 0 ↔ Δ = 4 * Real.pi * B := by
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  constructor
  · intro hR
    have h := hLedger
    rw [hR] at h
    field_simp [hpi] at h
    linarith
  · intro hΔ
    have h := hLedger
    rw [hΔ] at h
    field_simp [hpi] at h
    linarith

private theorem cFZP_radial_zero_iff_threshold
    {B G Δ : ℝ}
    (hLedger : G = Real.pi * B - Δ / 4) :
    G = 0 ↔ Δ = 4 * Real.pi * B := by
  constructor <;> intro h
  · linarith [hLedger]
  · linarith [hLedger]

private theorem cFZP_completion_threshold_sign_iff
    {B R Δ : ℝ}
    (hLedger : B = (1 / Real.pi) * (Δ / 4) + R) :
    0 ≤ R ↔ Δ ≤ 4 * Real.pi * B := by
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hrel : 4 * Real.pi * B - Δ = 4 * Real.pi * R := by
    have h := hLedger
    field_simp [hpi] at h
    linarith
  have hc : 0 < 4 * Real.pi := by positivity
  constructor
  · intro hR
    have hprod : 0 ≤ 4 * Real.pi * R := mul_nonneg (le_of_lt hc) hR
    linarith
  · intro hΔ
    have hprod : 0 ≤ 4 * Real.pi * R := by linarith
    by_contra hR
    have hR' : R < 0 := lt_of_not_ge hR
    have hprod' : 4 * Real.pi * R < 0 := mul_neg_of_pos_of_neg hc hR'
    linarith

private theorem cFZP_completion_threshold_reverse_sign_iff
    {B R Δ : ℝ}
    (hLedger : B = (1 / Real.pi) * (Δ / 4) + R) :
    R ≤ 0 ↔ 4 * Real.pi * B ≤ Δ := by
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hrel : 4 * Real.pi * B - Δ = 4 * Real.pi * R := by
    have h := hLedger
    field_simp [hpi] at h
    linarith
  have hc : 0 < 4 * Real.pi := by positivity
  constructor
  · intro hR
    have hprod : 4 * Real.pi * R ≤ 0 := mul_nonpos_of_nonneg_of_nonpos
      (le_of_lt hc) hR
    linarith
  · intro hΔ
    have hprod : 4 * Real.pi * R ≤ 0 := by linarith
    by_contra hR
    have hR' : 0 < R := lt_of_not_ge hR
    have hprod' : 0 < 4 * Real.pi * R := mul_pos hc hR'
    linarith

private theorem cFZP_radial_threshold_sign_iff
    {B G Δ : ℝ}
    (hLedger : G = Real.pi * B - Δ / 4) :
    0 ≤ G ↔ Δ ≤ 4 * Real.pi * B := by
  have hpi : 0 < Real.pi := Real.pi_pos
  constructor
  · intro hG
    linarith [hLedger]
  · intro hΔ
    by_contra hG
    have hG' : G < 0 := lt_of_not_ge hG
    linarith [hLedger]

private theorem cFZP_radial_threshold_reverse_sign_iff
    {B G Δ : ℝ}
    (hLedger : G = Real.pi * B - Δ / 4) :
    G ≤ 0 ↔ 4 * Real.pi * B ≤ Δ := by
  have hpi : 0 < Real.pi := Real.pi_pos
  constructor
  · intro hG
    linarith [hLedger]
  · intro hΔ
    by_contra hG
    have hG' : 0 < G := lt_of_not_ge hG
    linarith [hLedger]

private theorem cFZP_top_zero_iff_balance
    {T Δ : ℝ}
    (hTop : T = (1 / Real.pi) * (Δ / 4)) :
    Δ = 0 ↔ T = 0 := by
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  constructor
  · intro hΔ
    rw [hTop, hΔ]
    norm_num
  · intro hT
    have h := hTop
    rw [hT] at h
    field_simp [hpi] at h
    linarith

/-! ## B. Polarized balance and TopMismatch zero -/

theorem pascalCenteredXiPrimeSideFiniteTopZetaMismatchScalar_eq_zero_iff_integratedPolarizedMass_balance
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
    cfzpProjectedMirrorForwardIntegratedMinusMass ε X W =
        cfzpProjectedMirrorForwardIntegratedPlusMass ε X W ↔
      pascalCenteredXiPrimeSideFiniteTopZetaMismatchScalar ε W X = 0 := by
  have hTop :=
    pascalCenteredXiPrimeSideFiniteTopZetaMismatchScalar_eq_integratedMass_difference_div_pi
      hε hSafe hZeta hPHZ hWeighted hρ hρm hPairLeft hPairRight
  simpa [sub_eq_zero] using cFZP_top_zero_iff_balance hTop

/-! ## C. Contact threshold and completion/radial zero -/

theorem cfzpFiniteRectangleCompletionRemainder_eq_zero_iff_integratedPolarizedMass_contact_threshold
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
    cfzpFiniteRectangleCompletionRemainder ε W X = 0 ↔
      cfzpProjectedMirrorForwardIntegratedMinusMass ε X W -
          cfzpProjectedMirrorForwardIntegratedPlusMass ε X W =
        4 * Real.pi * pascalCenteredXiPrimeSideFiniteRectangleBackground ε W X := by
  have hLedger :=
    pascalCenteredXiPrimeSideFiniteRectangleBackground_eq_integratedMass_difference_add_completionRemainder
      hε hSafe hZeta hPHZ hWeighted hρ hρm hPairLeft hPairRight
  exact cFZP_completion_zero_iff_threshold hLedger

theorem pascalCenteredXiPrimeSideFiniteRadialContactDeficit_eq_zero_iff_integratedPolarizedMass_contact_threshold
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
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W X = 0 ↔
      cfzpProjectedMirrorForwardIntegratedMinusMass ε X W -
          cfzpProjectedMirrorForwardIntegratedPlusMass ε X W =
        4 * Real.pi * pascalCenteredXiPrimeSideFiniteRectangleBackground ε W X := by
  have hLedger :=
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit_eq_pi_mul_background_sub_integratedMass_difference
      hε hSafe hZeta hPHZ hWeighted hρ hρm hPairLeft hPairRight hArch hElem
  exact cFZP_radial_zero_iff_threshold hLedger

/-! ## D. Exact sign translations -/

theorem cfzpFiniteRectangleCompletionRemainder_nonneg_iff_integratedPolarizedMass_below_contact_threshold
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
    0 ≤ cfzpFiniteRectangleCompletionRemainder ε W X ↔
      cfzpProjectedMirrorForwardIntegratedMinusMass ε X W -
          cfzpProjectedMirrorForwardIntegratedPlusMass ε X W ≤
        4 * Real.pi * pascalCenteredXiPrimeSideFiniteRectangleBackground ε W X := by
  have hLedger :=
    pascalCenteredXiPrimeSideFiniteRectangleBackground_eq_integratedMass_difference_add_completionRemainder
      hε hSafe hZeta hPHZ hWeighted hρ hρm hPairLeft hPairRight
  exact cFZP_completion_threshold_sign_iff hLedger

theorem cfzpFiniteRectangleCompletionRemainder_nonpos_iff_integratedPolarizedMass_above_contact_threshold
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
    cfzpFiniteRectangleCompletionRemainder ε W X ≤ 0 ↔
      4 * Real.pi * pascalCenteredXiPrimeSideFiniteRectangleBackground ε W X ≤
        cfzpProjectedMirrorForwardIntegratedMinusMass ε X W -
          cfzpProjectedMirrorForwardIntegratedPlusMass ε X W := by
  have hLedger :=
    pascalCenteredXiPrimeSideFiniteRectangleBackground_eq_integratedMass_difference_add_completionRemainder
      hε hSafe hZeta hPHZ hWeighted hρ hρm hPairLeft hPairRight
  exact cFZP_completion_threshold_reverse_sign_iff hLedger

/-! ## E. Radial sign translations -/

theorem pascalCenteredXiPrimeSideFiniteRadialContactDeficit_nonneg_iff_integratedPolarizedMass_below_contact_threshold
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
    0 ≤ pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W X ↔
      cfzpProjectedMirrorForwardIntegratedMinusMass ε X W -
          cfzpProjectedMirrorForwardIntegratedPlusMass ε X W ≤
        4 * Real.pi * pascalCenteredXiPrimeSideFiniteRectangleBackground ε W X := by
  have hLedger :=
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit_eq_pi_mul_background_sub_integratedMass_difference
      hε hSafe hZeta hPHZ hWeighted hρ hρm hPairLeft hPairRight hArch hElem
  exact cFZP_radial_threshold_sign_iff hLedger

theorem pascalCenteredXiPrimeSideFiniteRadialContactDeficit_nonpos_iff_integratedPolarizedMass_above_contact_threshold
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
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W X ≤ 0 ↔
      4 * Real.pi * pascalCenteredXiPrimeSideFiniteRectangleBackground ε W X ≤
        cfzpProjectedMirrorForwardIntegratedMinusMass ε X W -
          cfzpProjectedMirrorForwardIntegratedPlusMass ε X W := by
  have hLedger :=
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit_eq_pi_mul_background_sub_integratedMass_difference
      hε hSafe hZeta hPHZ hWeighted hρ hρm hPairLeft hPairRight hArch hElem
  exact cFZP_radial_threshold_reverse_sign_iff hLedger

/-! ## F. What remains under polarized balance -/

theorem cfzpFiniteRectangleCompletionRemainder_eq_rectangleBackground_of_integratedPolarizedMass_balance
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
    (hBal : cfzpProjectedMirrorForwardIntegratedMinusMass ε X W =
      cfzpProjectedMirrorForwardIntegratedPlusMass ε X W) :
    cfzpFiniteRectangleCompletionRemainder ε W X =
      pascalCenteredXiPrimeSideFiniteRectangleBackground ε W X := by
  have hLedger :=
    pascalCenteredXiPrimeSideFiniteRectangleBackground_eq_integratedMass_difference_add_completionRemainder
      hε hSafe hZeta hPHZ hWeighted hρ hρm hPairLeft hPairRight
  rw [hBal] at hLedger
  linarith

theorem pascalCenteredXiPrimeSideFiniteRadialContactDeficit_eq_pi_mul_rectangleBackground_of_integratedPolarizedMass_balance
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
      volume W.rectangle.σ (1 - W.rectangle.σ))
    (hBal : cfzpProjectedMirrorForwardIntegratedMinusMass ε X W =
      cfzpProjectedMirrorForwardIntegratedPlusMass ε X W) :
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W X =
      Real.pi * pascalCenteredXiPrimeSideFiniteRectangleBackground ε W X := by
  have hLedger :=
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit_eq_pi_mul_background_sub_integratedMass_difference
      hε hSafe hZeta hPHZ hWeighted hρ hρm hPairLeft hPairRight hArch hElem
  rw [hBal] at hLedger
  linarith

theorem pascalCenteredXiPrimeSideFiniteRadialContactDeficit_eq_zero_iff_rectangleBackground_eq_zero_of_integratedPolarizedMass_balance
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
      volume W.rectangle.σ (1 - W.rectangle.σ))
    (hBal : cfzpProjectedMirrorForwardIntegratedMinusMass ε X W =
      cfzpProjectedMirrorForwardIntegratedPlusMass ε X W) :
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W X = 0 ↔
      pascalCenteredXiPrimeSideFiniteRectangleBackground ε W X = 0 := by
  have hRad :=
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit_eq_pi_mul_rectangleBackground_of_integratedPolarizedMass_balance
      hε hSafe hZeta hPHZ hWeighted hρ hρm hPairLeft hPairRight hArch hElem hBal
  constructor
  · intro h
    rw [hRad] at h
    nlinarith [Real.pi_pos]
  · intro h
    rw [hRad, h]
    ring

/-! ## G. Frontier markers -/

inductive CfzpIntegratedMassBalanceToPointwiseProjectedDensityGap : Prop
  | noPointwiseVanishingFromIntegratedBalanceProvided

inductive CfzpIntegratedMassBalanceToZetaZeroGap : Prop
  | noZetaZeroIdentificationProvided

inductive CfzpRadialContactThresholdSignProviderGap : Prop
  | noIndependentThresholdInequalityProviderProvided

end DkMath.RH.CFBRCProjection
