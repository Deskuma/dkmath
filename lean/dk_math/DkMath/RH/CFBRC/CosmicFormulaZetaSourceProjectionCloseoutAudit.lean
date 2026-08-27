/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.CosmicFormulaZetaPrimePowerCenteredPhaseCellCoverageAudit
import DkMath.RH.CFBRC.CosmicFormulaZetaSourceInteractionClassificationAudit
import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideCommonCarrierInteractionCancellationAudit
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CosmicFormulaZetaSourceProjectionCloseoutAudit"

/-!
# CFZP-006Z: source-projection closeout / common-baseline defect audit

The finite radial contact deficit and the nonnegative ray-minus whole share
the same interaction term.  This file cancels that interaction and records
the remaining signed common-baseline defect.  It deliberately does not
identify that defect with zero, and it does not identify the ray-minus whole
with the earlier amplitude-side Gap.
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

/-! ## A. The common-baseline defect -/

noncomputable def cfzp006CommonBaselineDefect
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) : ℝ :=
  pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W 0 -
    pascalCenteredXiPrimeSideAggregateRayCommonEnergy ε W X

theorem cfzp006RadialContactDeficit_eq_rayMinusEnergy_add_commonBaselineDefect
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W X =
      pascalCenteredXiPrimeSideAggregateRayMinusEnergy ε W X +
        cfzp006CommonBaselineDefect ε W X := by
  rw [pascalCenteredXiPrimeSideFiniteRadialContactDeficit_eq_zeroCutoff_deficit_sub_interaction
    hε W X,
    pascalCenteredXiPrimeSideAggregateRayMinusEnergy_eq_common_sub_interaction
      hε W X]
  unfold cfzp006CommonBaselineDefect
  ring

theorem cfzp006RadialContactDeficit_sub_rayMinusEnergy_eq_commonBaselineDefect
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W X -
        pascalCenteredXiPrimeSideAggregateRayMinusEnergy ε W X =
      cfzp006CommonBaselineDefect ε W X := by
  rw [cfzp006RadialContactDeficit_eq_rayMinusEnergy_add_commonBaselineDefect
    hε W X]
  ring

theorem cfzp006RadialContactDeficit_eq_rayMinusEnergy_iff_commonBaselineDefect_eq_zero
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W X =
        pascalCenteredXiPrimeSideAggregateRayMinusEnergy ε W X ↔
      cfzp006CommonBaselineDefect ε W X = 0 := by
  constructor
  · intro h
    have hd := cfzp006RadialContactDeficit_sub_rayMinusEnergy_eq_commonBaselineDefect
      hε W X
    rw [h] at hd
    simpa using hd.symm
  · intro h
    rw [cfzp006RadialContactDeficit_eq_rayMinusEnergy_add_commonBaselineDefect
      hε W X, h, add_zero]

/-! ## B. Rectangle completion form -/

theorem cfzp006PiMulCompletionRemainder_eq_rayMinusEnergy_add_commonBaselineDefect
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
    Real.pi * cfzpFiniteRectangleCompletionRemainder ε W X =
      pascalCenteredXiPrimeSideAggregateRayMinusEnergy ε W X +
        cfzp006CommonBaselineDefect ε W X := by
  have hR := cfzpFiniteRadialContactDeficit_eq_pi_mul_completionRemainder
    hε hSafe hZeta hArch hElem X
  calc
    Real.pi * cfzpFiniteRectangleCompletionRemainder ε W X =
        pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W X := hR.symm
    _ = pascalCenteredXiPrimeSideAggregateRayMinusEnergy ε W X +
        cfzp006CommonBaselineDefect ε W X :=
      cfzp006RadialContactDeficit_eq_rayMinusEnergy_add_commonBaselineDefect hε W X

theorem cfzp006CompletionRemainder_eq_rayMinusEnergy_div_pi_add_defect_div_pi
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
        pascalCenteredXiPrimeSideAggregateRayMinusEnergy ε W X / Real.pi +
          cfzp006CommonBaselineDefect ε W X / Real.pi := by
  have h := cfzp006PiMulCompletionRemainder_eq_rayMinusEnergy_add_commonBaselineDefect
    hε hSafe hZeta hArch hElem X
  field_simp [Real.pi_ne_zero]
  linarith

/-! ## C. Alignment and conditional nonnegativity -/

theorem cfzp006CompletionRemainder_eq_normalizedRayMinusEnergy_iff_commonBaselineDefect_eq_zero
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
        pascalCenteredXiPrimeSideAggregateRayMinusEnergy ε W X / Real.pi ↔
      cfzp006CommonBaselineDefect ε W X = 0 := by
  have h := cfzp006PiMulCompletionRemainder_eq_rayMinusEnergy_add_commonBaselineDefect
    hε hSafe hZeta hArch hElem X
  constructor
  · intro hR
    have hmul : Real.pi * cfzpFiniteRectangleCompletionRemainder ε W X =
        pascalCenteredXiPrimeSideAggregateRayMinusEnergy ε W X := by
      rw [hR]
      field_simp [Real.pi_ne_zero]
    linarith [h, hmul]
  · intro hD
    apply (eq_div_iff Real.pi_ne_zero).2
    rw [cfzp006CommonBaselineDefect] at hD
    rw [cfzp006CommonBaselineDefect] at h
    rw [hD] at h
    simpa [mul_comm] using h

theorem cfzp006CompletionRemainder_nonneg_of_commonBaselineDefect_eq_zero
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
    (X : ℕ)
    (hD : cfzp006CommonBaselineDefect ε W X = 0) :
    0 ≤ cfzpFiniteRectangleCompletionRemainder ε W X := by
  have h := cfzp006PiMulCompletionRemainder_eq_rayMinusEnergy_add_commonBaselineDefect
    hε hSafe hZeta hArch hElem X
  rw [hD, add_zero] at h
  have hminus := pascalCenteredXiPrimeSideAggregateRayMinusEnergy_nonneg hε W X
  nlinarith [Real.pi_pos]

theorem cfzp006RadialContactDeficit_eq_zero_iff_rayMinusEnergy_eq_zero_of_commonBaselineDefect_eq_zero
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ)
    (hD : cfzp006CommonBaselineDefect ε W X = 0) :
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W X = 0 ↔
      pascalCenteredXiPrimeSideAggregateRayMinusEnergy ε W X = 0 := by
  rw [cfzp006RadialContactDeficit_eq_rayMinusEnergy_add_commonBaselineDefect
    hε W X, hD, add_zero]

theorem cfzp006CompletionRemainder_eq_zero_iff_rayMinusEnergy_eq_zero_of_commonBaselineDefect_eq_zero
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
    (X : ℕ)
    (hD : cfzp006CommonBaselineDefect ε W X = 0) :
    cfzpFiniteRectangleCompletionRemainder ε W X = 0 ↔
      pascalCenteredXiPrimeSideAggregateRayMinusEnergy ε W X = 0 := by
  have h := cfzp006PiMulCompletionRemainder_eq_rayMinusEnergy_add_commonBaselineDefect
    hε hSafe hZeta hArch hElem X
  rw [hD, add_zero] at h
  constructor
  · intro hR
    rw [hR] at h
    simpa using h.symm
  · intro hE
    have hzero : Real.pi * cfzpFiniteRectangleCompletionRemainder ε W X = 0 := by
      simpa [hE] using h
    exact (mul_eq_zero.mp hzero).resolve_left Real.pi_ne_zero

/-! ## D. The two source-side gaps remain distinct -/

inductive Cfzp006AmplitudeGapToRayMinusWholeProjectionGap : Prop
  | noExactAmplitudeGapToRayMinusWholeProjectionProvider

theorem cfzp006CommonBaselineAlignment_not_forced_by_commonInteractionAlgebra :
    ∃ (G₀ C I G Eminus : ℝ),
      G = G₀ - I ∧ Eminus = C - I ∧ 0 ≤ Eminus ∧ G ≠ Eminus := by
  refine ⟨1, 0, 0, 1, 0, ?_⟩
  norm_num

/-! ## E. One-surface closeout theorem -/

theorem cfzp006SourceProjection_closeout
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
    (Real.pi * cfzpFiniteRectangleCompletionRemainder ε W X =
        pascalCenteredXiPrimeSideAggregateRayMinusEnergy ε W X +
          cfzp006CommonBaselineDefect ε W X) ∧
      (cfzpFiniteRectangleCompletionRemainder ε W X =
        pascalCenteredXiPrimeSideAggregateRayMinusEnergy ε W X / Real.pi ↔
          cfzp006CommonBaselineDefect ε W X = 0) ∧
      (cfzp006CommonBaselineDefect ε W X = 0 →
        0 ≤ cfzpFiniteRectangleCompletionRemainder ε W X) := by
  refine ⟨
    cfzp006PiMulCompletionRemainder_eq_rayMinusEnergy_add_commonBaselineDefect
      hε hSafe hZeta hArch hElem X,
    cfzp006CompletionRemainder_eq_normalizedRayMinusEnergy_iff_commonBaselineDefect_eq_zero
      hε hSafe hZeta hArch hElem X, ?_⟩
  intro hD
  exact cfzp006CompletionRemainder_nonneg_of_commonBaselineDefect_eq_zero
    hε hSafe hZeta hArch hElem X hD

end DkMath.RH.CFBRCProjection
