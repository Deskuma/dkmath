/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.CosmicFormulaZetaCriticalLineProjectivePhaseNormalizationAudit
import DkMath.RH.CFBRC.CosmicFormulaZetaSourceProjectionCloseoutAudit
import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideCanonicalPolarizationSignedMassAudit
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CosmicFormulaZetaCommonBaselineAlignmentReachAudit"

/-!
# CFZP-009: common-baseline alignment as a finite reach problem

The two polarized whole masses have the exact form `C + I` and `C - I`.
Their average therefore recovers the common energy `C`, while the signed
CFZP-006 defect is the zero-cutoff baseline minus that common energy.

This module fixes the correct quantifiers for finite alignment.  It does not
provide a reach witness, a monotonicity theorem, a cofinal limit, or a source
projection bridge.  The finite reach and cofinal reach providers remain an
explicit frontier.
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

/-! ## A. Common energy as the average of the two whole masses -/

theorem cfzp009_two_mul_commonEnergy_eq_plusEnergy_add_minusEnergy
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    2 * pascalCenteredXiPrimeSideAggregateRayCommonEnergy ε W X =
      pascalCenteredXiPrimeSideAggregateRayPlusEnergy ε W X +
        pascalCenteredXiPrimeSideAggregateRayMinusEnergy ε W X := by
  have hplus := pascalCenteredXiPrimeSideAggregateRayPlusEnergy_eq_common_add_interaction
    hε W X
  have hminus := pascalCenteredXiPrimeSideAggregateRayMinusEnergy_eq_common_sub_interaction
    hε W X
  linarith

theorem cfzp009_commonEnergy_eq_plusEnergy_add_minusEnergy_div_two
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiPrimeSideAggregateRayCommonEnergy ε W X =
      (pascalCenteredXiPrimeSideAggregateRayPlusEnergy ε W X +
        pascalCenteredXiPrimeSideAggregateRayMinusEnergy ε W X) / 2 := by
  have h := cfzp009_two_mul_commonEnergy_eq_plusEnergy_add_minusEnergy hε W X
  linarith

theorem cfzp009_commonEnergy_nonneg
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    0 ≤ pascalCenteredXiPrimeSideAggregateRayCommonEnergy ε W X := by
  rw [cfzp009_commonEnergy_eq_plusEnergy_add_minusEnergy_div_two hε W X]
  exact div_nonneg
    (add_nonneg
      (pascalCenteredXiPrimeSideAggregateRayPlusEnergy_nonneg hε W X)
      (pascalCenteredXiPrimeSideAggregateRayMinusEnergy_nonneg hε W X))
    (by norm_num)

/-! ## B. Polarized whole-mass form of the signed defect -/

theorem cfzp009CommonBaselineDefect_eq_zeroCutoff_sub_averageWholeEnergy
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    cfzp006CommonBaselineDefect ε W X =
      pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W 0 -
        (pascalCenteredXiPrimeSideAggregateRayPlusEnergy ε W X +
          pascalCenteredXiPrimeSideAggregateRayMinusEnergy ε W X) / 2 := by
  unfold cfzp006CommonBaselineDefect
  rw [cfzp009_commonEnergy_eq_plusEnergy_add_minusEnergy_div_two hε W X]

theorem cfzp009CommonBaselineDefect_eq_zero_iff_commonEnergy_eq_zeroCutoff
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    cfzp006CommonBaselineDefect ε W X = 0 ↔
      pascalCenteredXiPrimeSideAggregateRayCommonEnergy ε W X =
        pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W 0 := by
  unfold cfzp006CommonBaselineDefect
  constructor <;> intro h <;> linarith

theorem cfzp009CommonBaselineDefect_eq_zero_iff_wholeEnergy_sum_eq_two_zeroCutoff
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    cfzp006CommonBaselineDefect ε W X = 0 ↔
      pascalCenteredXiPrimeSideAggregateRayPlusEnergy ε W X +
          pascalCenteredXiPrimeSideAggregateRayMinusEnergy ε W X =
        2 * pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W 0 := by
  rw [cfzp009CommonBaselineDefect_eq_zeroCutoff_sub_averageWholeEnergy hε W X]
  constructor <;> intro h <;> linarith

theorem cfzp009CommonBaselineDefect_nonneg_iff_commonEnergy_le_zeroCutoff
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    0 ≤ cfzp006CommonBaselineDefect ε W X ↔
      pascalCenteredXiPrimeSideAggregateRayCommonEnergy ε W X ≤
        pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W 0 := by
  unfold cfzp006CommonBaselineDefect
  constructor <;> intro h <;> linarith

theorem cfzp009CommonBaselineDefect_nonpos_iff_zeroCutoff_le_commonEnergy
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    cfzp006CommonBaselineDefect ε W X ≤ 0 ↔
      pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W 0 ≤
        pascalCenteredXiPrimeSideAggregateRayCommonEnergy ε W X := by
  unfold cfzp006CommonBaselineDefect
  constructor <;> intro h <;> linarith

/-! ## C. Cutoff-zero audit -/

theorem cfzp009AggregateRayCommonEnergy_zero
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) :
    pascalCenteredXiPrimeSideAggregateRayCommonEnergy ε W 0 = 0 := by
  have h := cfzp009_two_mul_commonEnergy_eq_plusEnergy_add_minusEnergy hε W 0
  rw [pascalCenteredXiPrimeSideAggregateRayPlusEnergy_zero hε W,
    pascalCenteredXiPrimeSideAggregateRayMinusEnergy_zero hε W] at h
  linarith

theorem cfzp009CommonBaselineDefect_zeroCutoff
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) :
    cfzp006CommonBaselineDefect ε W 0 =
      pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W 0 := by
  unfold cfzp006CommonBaselineDefect
  rw [cfzp009AggregateRayCommonEnergy_zero hε W]
  ring

/-! ## D. Universal alignment quantifier audit -/

theorem cfzp009_universalCommonBaselineAlignment_implies_zeroCutoffDeficit_eq_zero
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow)
    (hAll : ∀ X : ℕ, cfzp006CommonBaselineDefect ε W X = 0) :
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W 0 = 0 := by
  have h0 := hAll 0
  rw [cfzp009CommonBaselineDefect_zeroCutoff hε W] at h0
  exact h0

theorem cfzp009_zeroCutoffDeficit_ne_zero_excludes_universalCommonBaselineAlignment
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow)
    (h0 : pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W 0 ≠ 0) :
    ¬ (∀ X : ℕ, cfzp006CommonBaselineDefect ε W X = 0) := by
  intro hAll
  exact h0 (cfzp009_universalCommonBaselineAlignment_implies_zeroCutoffDeficit_eq_zero
    hε W hAll)

/-! ## E. Finite baseline reach as a first-class proposition -/

def CfzpCommonBaselineReachedAt
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) : Prop :=
  pascalCenteredXiPrimeSideAggregateRayCommonEnergy ε W X =
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W 0

theorem cfzpCommonBaselineReachedAt_iff_commonBaselineDefect_eq_zero
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    CfzpCommonBaselineReachedAt ε W X ↔
      cfzp006CommonBaselineDefect ε W X = 0 := by
  unfold CfzpCommonBaselineReachedAt
  exact (cfzp009CommonBaselineDefect_eq_zero_iff_commonEnergy_eq_zeroCutoff
    ε W X).symm

theorem cfzpCommonBaselineReachedAt_iff_wholeEnergy_sum_eq_two_zeroCutoff
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    CfzpCommonBaselineReachedAt ε W X ↔
      pascalCenteredXiPrimeSideAggregateRayPlusEnergy ε W X +
          pascalCenteredXiPrimeSideAggregateRayMinusEnergy ε W X =
        2 * pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W 0 := by
  rw [cfzpCommonBaselineReachedAt_iff_commonBaselineDefect_eq_zero ε W X]
  exact cfzp009CommonBaselineDefect_eq_zero_iff_wholeEnergy_sum_eq_two_zeroCutoff
    hε W X

theorem cfzp009_existsFiniteCommonBaselineReach_iff_existsCommonBaselineDefect_zero
    {ε : ℝ} (W : PascalCenteredXiResidueTransportWindow) :
    (∃ X : ℕ, CfzpCommonBaselineReachedAt ε W X) ↔
      ∃ X : ℕ, cfzp006CommonBaselineDefect ε W X = 0 := by
  constructor
  · rintro ⟨X, hX⟩
    exact ⟨X, (cfzpCommonBaselineReachedAt_iff_commonBaselineDefect_eq_zero
      ε W X).mp hX⟩
  · rintro ⟨X, hX⟩
    exact ⟨X, (cfzpCommonBaselineReachedAt_iff_commonBaselineDefect_eq_zero
      ε W X).mpr hX⟩

/-! ## F. Reach frontier -/

inductive CfzpCommonBaselineFiniteOrCofinalReachGap : Prop
  | noIndependentCommonEnergyBaselineReachProvider

end DkMath.RH.CFBRCProjection
