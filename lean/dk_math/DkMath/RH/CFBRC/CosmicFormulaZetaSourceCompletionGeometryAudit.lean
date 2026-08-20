/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.CosmicFormulaZetaMellinSourceProjection
import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideFiniteEulerRenormalizedZetaResidualAudit
import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideIndependentRadialContactProviderAudit
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CosmicFormulaZetaSourceCompletionGeometryAudit"

/-!
# CFZP-006: source completion geometry audit

This module separates the functional-reflection source into its cycle-height
displacement and same-height critical-mirror channels.  It then identifies the
finite rectangle completion remainder with the existing CS30 radial-contact
deficit and the CS23 fixed-radial-moment minus complete-source ledger.

The remainder is deliberately named `CompletionRemainder`, not `Gap`.  No
nonnegativity provider, coordinate-Gap identification, infinite product,
phase branch, or RH statement is introduced here.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.Analysis
open DkMath.NumberTheory
open DkMath.NumberTheory.PrimitiveSet
open MeasureTheory
open Set
open scoped ComplexConjugate Interval Topology

/-! ## Functional reflection versus same-height mirror -/

/-- The cycle-height displacement between `1 - s` and `criticalMirror s`. -/
noncomputable def cfzpFunctionalVsSameHeightCycleDisplacementMode
    (q : ℕ) (s : ℂ) : ℂ :=
  (q : ℂ) ^ (-(1 - s)) -
    (q : ℂ) ^ (-(criticalMirror s))

theorem cfzpFunctionalReflectionModeDifference_eq_cycleDisplacement_add_sameHeight
    (q : ℕ) (s : ℂ) :
    cfzpFunctionalReflectionModeDifference q s =
      cfzpFunctionalVsSameHeightCycleDisplacementMode q s +
        cfzpSameHeightMirrorModeDifference q s := by
  unfold cfzpFunctionalReflectionModeDifference
    cfzpFunctionalVsSameHeightCycleDisplacementMode
    cfzpSameHeightMirrorModeDifference
  ring

theorem cfzpFunctionalVsSameHeightCycleDisplacementMode_eq_polar
    {q : ℕ} (hq : 0 < q) (s : ℂ) :
    cfzpFunctionalVsSameHeightCycleDisplacementMode q s =
      cfzpPrimePowerCommonRadialCarrier q *
        (primeMirrorRightAmplitude q (centeredSigma s.re) : ℂ) *
          (cfzpPrimePowerCycleState q (-s.im) -
            cfzpPrimePowerCycleState q s.im) := by
  unfold cfzpFunctionalVsSameHeightCycleDisplacementMode
  rw [natCpowNeg_one_sub_eq_commonRadial_mul_rightAmplitude_mul_cycle hq s,
    natCpowNeg_criticalMirror_eq_commonRadial_mul_rightAmplitude_mul_cycle hq s]
  ring

theorem one_sub_eq_criticalMirror_iff_im_eq_zero (s : ℂ) :
    1 - s = criticalMirror s ↔ s.im = 0 := by
  constructor
  · intro h
    have him := congrArg Complex.im h
    have him' : -s.im = s.im := by
      simpa [criticalMirror] using him
    linarith
  · intro hs
    apply Complex.ext
    · simp [criticalMirror]
    · simp [criticalMirror, hs]

theorem cfzpFunctionalVsSameHeightCycleDisplacementMode_eq_zero_of_im_eq_zero
    {q : ℕ} {s : ℂ} (hs : s.im = 0) :
    cfzpFunctionalVsSameHeightCycleDisplacementMode q s = 0 := by
  have hmirror : 1 - s = criticalMirror s :=
    (one_sub_eq_criticalMirror_iff_im_eq_zero s).2 hs
  simp [cfzpFunctionalVsSameHeightCycleDisplacementMode, hmirror]

theorem cfzpSameHeightMirrorModeDifference_eq_zero_of_re_eq_half
    {q : ℕ} {s : ℂ} (hs : s.re = (1 : ℝ) / 2) :
    cfzpSameHeightMirrorModeDifference q s = 0 := by
  unfold cfzpSameHeightMirrorModeDifference
  rw [(criticalMirror_eq_self_iff_re_eq_half s).2 hs]
  ring

theorem cfzpFunctionalReflectionModeDifference_eq_cycleDisplacement_of_re_eq_half
    {q : ℕ} {s : ℂ} (hs : s.re = (1 : ℝ) / 2) :
    cfzpFunctionalReflectionModeDifference q s =
      cfzpFunctionalVsSameHeightCycleDisplacementMode q s := by
  rw [cfzpFunctionalReflectionModeDifference_eq_cycleDisplacement_add_sameHeight,
    cfzpSameHeightMirrorModeDifference_eq_zero_of_re_eq_half hs]
  ring

/-! ## Finite canonical source decomposition -/

noncomputable def cfzpCanonicalCycleDisplacementLinearSourceUpTo
    (X : ℕ) (s : ℂ) : ℂ :=
  ∑ q ∈ canonicalPrimePowerSupportUpTo X,
    (canonicalPrimePowerShadowCost q : ℂ) *
      cfzpFunctionalVsSameHeightCycleDisplacementMode q s

theorem cfzpCanonicalFunctionalReflectionLinearSourceUpTo_eq_cycleDisplacement_add_sameHeight
    (X : ℕ) (s : ℂ) :
    cfzpCanonicalFunctionalReflectionLinearSourceUpTo X s =
      cfzpCanonicalCycleDisplacementLinearSourceUpTo X s +
        cfzpCanonicalSameHeightMirrorLinearSourceUpTo X s := by
  unfold cfzpCanonicalFunctionalReflectionLinearSourceUpTo
    cfzpCanonicalCycleDisplacementLinearSourceUpTo
    cfzpCanonicalSameHeightMirrorLinearSourceUpTo
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  rw [cfzpFunctionalReflectionModeDifference_eq_cycleDisplacement_add_sameHeight]
  ring

theorem cfzpCanonicalCycleDisplacementLinearSourceUpTo_eq_PHZ_difference
    (X : ℕ) (s : ℂ) :
    cfzpCanonicalCycleDisplacementLinearSourceUpTo X s =
      pascalPrimePowerPHZCanonicalUpTo X (1 - s) -
        pascalPrimePowerPHZCanonicalUpTo X (criticalMirror s) := by
  unfold cfzpCanonicalCycleDisplacementLinearSourceUpTo
    cfzpFunctionalVsSameHeightCycleDisplacementMode
  rw [pascalPrimePowerPHZCanonicalUpTo_eq_support_sum,
    pascalPrimePowerPHZCanonicalUpTo_eq_support_sum,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  ring

/-! ## Mellin Euler channel decomposition -/

noncomputable def cfzpFiniteMellinSameHeightMirrorDensity
    (ε : ℝ) (X : ℕ)
    (W : PascalCenteredXiResidueTransportWindow)
    (u : ℝ) : ℝ :=
  (pascalCenteredXiPrimeSideFiniteResidualTopMellinWeight ε W u *
    cfzpCanonicalSameHeightMirrorLinearSourceUpTo X
      (pascalSymmetricRectangleTopEdge u W.rectangle.T)).im

noncomputable def cfzpFiniteMellinCycleDisplacementDensity
    (ε : ℝ) (X : ℕ)
    (W : PascalCenteredXiResidueTransportWindow)
    (u : ℝ) : ℝ :=
  (pascalCenteredXiPrimeSideFiniteResidualTopMellinWeight ε W u *
    cfzpCanonicalCycleDisplacementLinearSourceUpTo X
      (pascalSymmetricRectangleTopEdge u W.rectangle.T)).im

theorem cfzpFiniteMellinSymmetricEulerDensity_eq_cycleDisplacement_add_sameHeight
    (ε : ℝ) (X : ℕ)
    (W : PascalCenteredXiResidueTransportWindow)
    (u : ℝ) :
    cfzpFiniteMellinSymmetricEulerDensity ε X W u =
      cfzpFiniteMellinCycleDisplacementDensity ε X W u +
        cfzpFiniteMellinSameHeightMirrorDensity ε X W u := by
  unfold cfzpFiniteMellinSymmetricEulerDensity
    cfzpFiniteMellinCycleDisplacementDensity
    cfzpFiniteMellinSameHeightMirrorDensity
  rw [cfzpCanonicalFunctionalReflectionLinearSourceUpTo_eq_cycleDisplacement_add_sameHeight]
  rw [mul_add, Complex.add_im]

theorem pascalCenteredXiPrimeSideFiniteSymmetricEulerMirrorDensity_eq_cycleDisplacement_add_sameHeight
    (ε : ℝ) (X : ℕ)
    (W : PascalCenteredXiResidueTransportWindow)
    (u : ℝ) :
    pascalCenteredXiPrimeSideFiniteSymmetricEulerMirrorDensity ε X W u =
      cfzpFiniteMellinCycleDisplacementDensity ε X W u +
        cfzpFiniteMellinSameHeightMirrorDensity ε X W u := by
  rw [← cfzpFiniteMellinSymmetricEulerDensity_eq_cs38]
  exact cfzpFiniteMellinSymmetricEulerDensity_eq_cycleDisplacement_add_sameHeight
    ε X W u

/-! ## Named rectangle completion remainder -/

noncomputable def cfzpFiniteRectangleCompletionRemainder
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (X : ℕ) : ℝ :=
  pascalCenteredXiPrimeSideFiniteRectangleBackground ε W X -
    pascalCenteredXiPrimeSideFiniteTopZetaMismatchScalar ε W X

theorem cfzpFiniteRectangleBackground_eq_mismatch_add_completionRemainder
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (X : ℕ) :
    pascalCenteredXiPrimeSideFiniteRectangleBackground ε W X =
      pascalCenteredXiPrimeSideFiniteTopZetaMismatchScalar ε W X +
        cfzpFiniteRectangleCompletionRemainder ε W X := by
  unfold cfzpFiniteRectangleCompletionRemainder
  ring

theorem cfzpFiniteRadialContactDeficit_eq_pi_mul_completionRemainder
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
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W X =
      Real.pi * cfzpFiniteRectangleCompletionRemainder ε W X := by
  simpa [cfzpFiniteRectangleCompletionRemainder] using
    (pascalCenteredXiPrimeSideFiniteRadialContactDeficit_eq_pi_mul_background_sub_mismatch
      hε hSafe hZeta hArch hElem X)

theorem cfzpFiniteRectangleCompletionRemainder_eq_radialDeficit_div_pi
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
      pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W X / Real.pi := by
  rw [cfzpFiniteRadialContactDeficit_eq_pi_mul_completionRemainder
    hε hSafe hZeta hArch hElem X]
  field_simp [Real.pi_ne_zero]

theorem cfzpFiniteRectangleCompletionRemainder_eq_radialMoment_sub_completeSource
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
      pascalCenteredXiFixedRadialSecondMomentFunctional W.R -
        pascalCenteredXiPrimeSideIndependentCompleteSourceReal ε W X := by
  have hR := cfzpFiniteRadialContactDeficit_eq_pi_mul_completionRemainder
    hε hSafe hZeta hArch hElem X
  have hS := pascalCenteredXiPrimeSideIndependentCompleteSource_radialDeficit_eq
    hε W X
  have hmul :
      Real.pi * cfzpFiniteRectangleCompletionRemainder ε W X =
        Real.pi *
          (pascalCenteredXiFixedRadialSecondMomentFunctional W.R -
            pascalCenteredXiPrimeSideIndependentCompleteSourceReal ε W X) := by
    calc
      Real.pi * cfzpFiniteRectangleCompletionRemainder ε W X =
          pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W X := hR.symm
      _ = Real.pi *
          (pascalCenteredXiFixedRadialSecondMomentFunctional W.R -
            pascalCenteredXiPrimeSideIndependentCompleteSourceReal ε W X) := hS
  exact mul_left_cancel₀ Real.pi_ne_zero hmul

/-! ## Sign frontier -/

theorem cfzpFiniteRectangleCompletionRemainder_nonneg_iff_radialDeficit_nonneg
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
    0 ≤ cfzpFiniteRectangleCompletionRemainder ε W X ↔
      0 ≤ pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W X := by
  rw [cfzpFiniteRadialContactDeficit_eq_pi_mul_completionRemainder
    hε hSafe hZeta hArch hElem X]
  constructor
  · intro h
    exact mul_nonneg (le_of_lt Real.pi_pos) h
  · intro h
    nlinarith [Real.pi_pos]

end DkMath.RH.CFBRCProjection
