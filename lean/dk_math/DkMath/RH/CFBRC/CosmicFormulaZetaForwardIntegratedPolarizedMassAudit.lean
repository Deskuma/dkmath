/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.CosmicFormulaZetaForwardPolarizedRectangleCompletionAudit
import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideFiniteResidualIntervalLocalRegularityAudit
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CosmicFormulaZetaForwardIntegratedPolarizedMassAudit"

/-!
# CFZP-006L: forward integrated polarized masses

The safe finite top interval supplies continuity for the total projected
source.  The two pointwise square masses from CFZP-006J therefore become
genuine nonnegative forward interval masses.  The signed CFZP-006K
interaction is their difference divided by four.

No pointwise balance, source-zero statement, completion-remainder sign, or
infinite/RH consequence is introduced.
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

/-! ## A. Forward interval geometry -/

theorem cfzpForwardInterval_mem_safe_top_interval
    {W : PascalCenteredXiResidueTransportWindow} {u : ℝ}
    (hu : u ∈ Set.Icc (1 / 2 : ℝ) W.rectangle.σ) :
    u ∈ Set.uIcc W.rectangle.σ (1 - W.rectangle.σ) := by
  have hσ : 1 - W.rectangle.σ ≤ W.rectangle.σ := by
    linarith [W.rectangle.hσ]
  have hhalf : (1 / 2 : ℝ) ≤ W.rectangle.σ := by
    linarith [W.rectangle.hσ]
  rw [Set.uIcc_of_ge hσ]
  exact ⟨by linarith [hu.1, hhalf], hu.2⟩

/-! ## B. Source rewrite and safe continuity -/

theorem cfzpProjectedMirrorComplexSource_eq_weight_mul_residualMirrorRate
    {ε : ℝ} {X : ℕ} {W : PascalCenteredXiResidueTransportWindow}
    {u : ℝ}
    (hSafe : IsPascalCenteredXiTopLogDerivDecompositionSafe W)
    (hu : u ∈ Set.uIcc W.rectangle.σ (1 - W.rectangle.σ)) :
    cfzpProjectedMirrorComplexSource ε X W u =
      pascalCenteredXiPrimeSideFiniteResidualTopMellinWeight ε W u *
        pascalCenteredXiPrimeSideFiniteResidualMirrorRate X W u := by
  rw [cfzpProjectedMirrorComplexSource_eq_channel_sum,
    cfzpFiniteMellinSymmetricEulerComplexSource_eq_weight_mul_eulerRate]
  rw [pascalCenteredXiPrimeSideFiniteResidualMirrorRate_eq_functionalEquationRate
    hSafe hu]
  unfold cfzpFiniteMellinCompletedMirrorComplexSource
    cfzpFiniteMellinGammaMirrorComplexSource
    pascalCenteredXiPrimeSideFiniteMirrorFunctionalEquationRate
  ring

private theorem cfzpTopMellinWeight_continuousOn_of_pos
    {ε : ℝ} (hε : 0 < ε) (W : PascalCenteredXiResidueTransportWindow) :
    ContinuousOn (pascalCenteredXiPrimeSideFiniteResidualTopMellinWeight ε W)
      (Set.uIcc W.rectangle.σ (1 - W.rectangle.σ)) := by
  have hw := (pascalCenteredXiMellinSecondDifferenceWeight_differentiable
    (ε := ε) (τ := 0) hε).continuous
  have hpath : Continuous (fun u : ℝ =>
      pascalOrdinaryToCentered
        (pascalSymmetricRectangleTopEdge u W.rectangle.T)) := by
    change Continuous (fun u : ℝ =>
      (u : ℂ) + (W.rectangle.T : ℂ) * Complex.I - criticalLineCenter)
    fun_prop
  exact (hw.comp hpath).continuousOn

private theorem cfzpResidualMirrorRate_continuousOn_of_safe
    {W : PascalCenteredXiResidueTransportWindow}
    (hSafe : IsPascalCenteredXiTopLogDerivDecompositionSafe W) (X : ℕ) :
    ContinuousOn (pascalCenteredXiPrimeSideFiniteResidualMirrorRate X W)
      (Set.uIcc W.rectangle.σ (1 - W.rectangle.σ)) := by
  let S : Set ℝ := Set.uIcc W.rectangle.σ (1 - W.rectangle.σ)
  have hlog := pascalCenteredXiPrimeSideFiniteResidualLogRate_continuousOn_of_safe
    hSafe X
  have hmapGlobal : Continuous (fun u : ℝ => 1 - u) := by fun_prop
  have hmap : ContinuousOn (fun u : ℝ => 1 - u) S :=
    hmapGlobal.continuousOn
  have hmirror : ∀ u ∈ S, 1 - u ∈ S := by
    intro u hu
    exact pascalCenteredXiPrimeSideFiniteResidual_top_safe_mirror hu
  have hlogMirror : ContinuousOn
      (fun u : ℝ =>
        pascalCenteredXiPrimeSideFiniteResidualLogRate X W (1 - u)) S := by
    exact hlog.comp hmap hmirror
  have hconj : ContinuousOn
      (fun u : ℝ => starRingEnd ℂ
        (pascalCenteredXiPrimeSideFiniteResidualLogRate X W (1 - u))) S := by
    exact Complex.continuous_conj.continuousOn.comp hlogMirror
      (fun _ _ => Set.mem_univ _)
  unfold pascalCenteredXiPrimeSideFiniteResidualMirrorRate
  exact hlog.sub hconj

theorem cfzpProjectedMirrorComplexSource_continuousOn_of_safe
    {ε : ℝ} (hε : 0 < ε)
    {W : PascalCenteredXiResidueTransportWindow}
    (hSafe : IsPascalCenteredXiTopLogDerivDecompositionSafe W) (X : ℕ) :
    ContinuousOn (cfzpProjectedMirrorComplexSource ε X W)
      (Set.uIcc W.rectangle.σ (1 - W.rectangle.σ)) := by
  have hw := cfzpTopMellinWeight_continuousOn_of_pos hε W
  have hr := cfzpResidualMirrorRate_continuousOn_of_safe hSafe X
  have hprod : ContinuousOn
      (fun u : ℝ =>
        pascalCenteredXiPrimeSideFiniteResidualTopMellinWeight ε W u *
          pascalCenteredXiPrimeSideFiniteResidualMirrorRate X W u)
      (Set.uIcc W.rectangle.σ (1 - W.rectangle.σ)) :=
    hw.mul hr
  have heq : Set.EqOn
      (cfzpProjectedMirrorComplexSource ε X W)
      (fun u : ℝ =>
        pascalCenteredXiPrimeSideFiniteResidualTopMellinWeight ε W u *
          pascalCenteredXiPrimeSideFiniteResidualMirrorRate X W u)
      (Set.uIcc W.rectangle.σ (1 - W.rectangle.σ)) := by
    intro u hu
    exact cfzpProjectedMirrorComplexSource_eq_weight_mul_residualMirrorRate
      hSafe hu
  exact hprod.congr heq

theorem cfzpProjectedMirrorComplexSource_continuousOn_forward_of_safe
    {ε : ℝ} (hε : 0 < ε)
    {W : PascalCenteredXiResidueTransportWindow}
    (hSafe : IsPascalCenteredXiTopLogDerivDecompositionSafe W) (X : ℕ) :
    ContinuousOn (cfzpProjectedMirrorComplexSource ε X W)
      (Set.Icc (1 / 2 : ℝ) W.rectangle.σ) := by
  exact (cfzpProjectedMirrorComplexSource_continuousOn_of_safe hε hSafe X).mono
    (fun u hu => cfzpForwardInterval_mem_safe_top_interval hu)

theorem cfzpProjectedMirrorDeorientedSource_continuousOn_forward_of_safe
    {ε : ℝ} (hε : 0 < ε)
    {W : PascalCenteredXiResidueTransportWindow}
    (hSafe : IsPascalCenteredXiTopLogDerivDecompositionSafe W) (X : ℕ) :
    ContinuousOn (cfzpProjectedMirrorDeorientedSource ε X W)
      (Set.Icc (1 / 2 : ℝ) W.rectangle.σ) := by
  have hsource := cfzpProjectedMirrorComplexSource_continuousOn_forward_of_safe
    hε hSafe X
  unfold cfzpProjectedMirrorDeorientedSource
  exact continuousOn_const.mul hsource

private theorem cfzpProjectedMirrorPolarizedPlusMass_continuousOn_forward_of_safe
    {ε : ℝ} (hε : 0 < ε)
    {W : PascalCenteredXiResidueTransportWindow}
    (hSafe : IsPascalCenteredXiTopLogDerivDecompositionSafe W) (X : ℕ) :
    ContinuousOn (cfzpProjectedMirrorPolarizedPlusMass ε X W)
      (Set.Icc (1 / 2 : ℝ) W.rectangle.σ) := by
  have hD := cfzpProjectedMirrorDeorientedSource_continuousOn_forward_of_safe
    hε hSafe X
  have hshift : ContinuousOn
      (fun u : ℝ => cfzpProjectedMirrorDeorientedSource ε X W u + 1)
      (Set.Icc (1 / 2 : ℝ) W.rectangle.σ) := by
    exact hD.add continuousOn_const
  unfold cfzpProjectedMirrorPolarizedPlusMass
  exact Complex.continuous_normSq.continuousOn.comp hshift
    (fun _ _ => Set.mem_univ _)

private theorem cfzpProjectedMirrorPolarizedMinusMass_continuousOn_forward_of_safe
    {ε : ℝ} (hε : 0 < ε)
    {W : PascalCenteredXiResidueTransportWindow}
    (hSafe : IsPascalCenteredXiTopLogDerivDecompositionSafe W) (X : ℕ) :
    ContinuousOn (cfzpProjectedMirrorPolarizedMinusMass ε X W)
      (Set.Icc (1 / 2 : ℝ) W.rectangle.σ) := by
  have hD := cfzpProjectedMirrorDeorientedSource_continuousOn_forward_of_safe
    hε hSafe X
  have hshift : ContinuousOn
      (fun u : ℝ => cfzpProjectedMirrorDeorientedSource ε X W u - 1)
      (Set.Icc (1 / 2 : ℝ) W.rectangle.σ) := by
    exact hD.sub continuousOn_const
  unfold cfzpProjectedMirrorPolarizedMinusMass
  exact Complex.continuous_normSq.continuousOn.comp hshift
    (fun _ _ => Set.mem_univ _)

/-! ## C. Forward interval-integrability and integrated masses -/

theorem cfzpProjectedMirrorPolarizedPlusMass_intervalIntegrable_of_safe
    {ε : ℝ} (hε : 0 < ε)
    {W : PascalCenteredXiResidueTransportWindow}
    (hSafe : IsPascalCenteredXiTopLogDerivDecompositionSafe W) (X : ℕ) :
    IntervalIntegrable (cfzpProjectedMirrorPolarizedPlusMass ε X W)
      volume (1 / 2 : ℝ) W.rectangle.σ := by
  have hhalf : (1 / 2 : ℝ) ≤ W.rectangle.σ := by
    linarith [W.rectangle.hσ]
  have hcont := cfzpProjectedMirrorPolarizedPlusMass_continuousOn_forward_of_safe
    hε hSafe X
  have hcontUIcc : ContinuousOn
      (cfzpProjectedMirrorPolarizedPlusMass ε X W)
      (Set.uIcc (1 / 2 : ℝ) W.rectangle.σ) := by
    rw [Set.uIcc_of_le hhalf]
    exact hcont
  exact hcontUIcc.intervalIntegrable

theorem cfzpProjectedMirrorPolarizedMinusMass_intervalIntegrable_of_safe
    {ε : ℝ} (hε : 0 < ε)
    {W : PascalCenteredXiResidueTransportWindow}
    (hSafe : IsPascalCenteredXiTopLogDerivDecompositionSafe W) (X : ℕ) :
    IntervalIntegrable (cfzpProjectedMirrorPolarizedMinusMass ε X W)
      volume (1 / 2 : ℝ) W.rectangle.σ := by
  have hhalf : (1 / 2 : ℝ) ≤ W.rectangle.σ := by
    linarith [W.rectangle.hσ]
  have hcont := cfzpProjectedMirrorPolarizedMinusMass_continuousOn_forward_of_safe
    hε hSafe X
  have hcontUIcc : ContinuousOn
      (cfzpProjectedMirrorPolarizedMinusMass ε X W)
      (Set.uIcc (1 / 2 : ℝ) W.rectangle.σ) := by
    rw [Set.uIcc_of_le hhalf]
    exact hcont
  exact hcontUIcc.intervalIntegrable

noncomputable def cfzpProjectedMirrorForwardIntegratedPlusMass
    (ε : ℝ) (X : ℕ)
    (W : PascalCenteredXiResidueTransportWindow) : ℝ :=
  ∫ u in (1 / 2 : ℝ)..W.rectangle.σ,
    cfzpProjectedMirrorPolarizedPlusMass ε X W u

noncomputable def cfzpProjectedMirrorForwardIntegratedMinusMass
    (ε : ℝ) (X : ℕ)
    (W : PascalCenteredXiResidueTransportWindow) : ℝ :=
  ∫ u in (1 / 2 : ℝ)..W.rectangle.σ,
    cfzpProjectedMirrorPolarizedMinusMass ε X W u

theorem cfzpProjectedMirrorForwardIntegratedPlusMass_nonneg
    {ε : ℝ} (_hε : 0 < ε)
    {W : PascalCenteredXiResidueTransportWindow}
    (_hSafe : IsPascalCenteredXiTopLogDerivDecompositionSafe W) (X : ℕ) :
    0 ≤ cfzpProjectedMirrorForwardIntegratedPlusMass ε X W := by
  unfold cfzpProjectedMirrorForwardIntegratedPlusMass
  apply intervalIntegral.integral_nonneg_of_ae
    (by linarith [W.rectangle.hσ])
  exact Filter.Eventually.of_forall (fun u =>
    cfzpProjectedMirrorPolarizedPlusMass_nonneg ε X W u)

theorem cfzpProjectedMirrorForwardIntegratedMinusMass_nonneg
    {ε : ℝ} (_hε : 0 < ε)
    {W : PascalCenteredXiResidueTransportWindow}
    (_hSafe : IsPascalCenteredXiTopLogDerivDecompositionSafe W) (X : ℕ) :
    0 ≤ cfzpProjectedMirrorForwardIntegratedMinusMass ε X W := by
  unfold cfzpProjectedMirrorForwardIntegratedMinusMass
  apply intervalIntegral.integral_nonneg_of_ae
    (by linarith [W.rectangle.hσ])
  exact Filter.Eventually.of_forall (fun u =>
    cfzpProjectedMirrorPolarizedMinusMass_nonneg ε X W u)

/-! ## D. Difference fold -/

theorem cfzpProjectedMirrorForwardPolarizedInteractionIntegral_eq_integratedMass_difference
    {ε : ℝ} (hε : 0 < ε)
    {W : PascalCenteredXiResidueTransportWindow}
    (hSafe : IsPascalCenteredXiTopLogDerivDecompositionSafe W) (X : ℕ) :
    cfzpProjectedMirrorForwardPolarizedInteractionIntegral ε X W =
      (cfzpProjectedMirrorForwardIntegratedMinusMass ε X W -
        cfzpProjectedMirrorForwardIntegratedPlusMass ε X W) / 4 := by
  unfold cfzpProjectedMirrorForwardPolarizedInteractionIntegral
    cfzpProjectedMirrorForwardIntegratedMinusMass
    cfzpProjectedMirrorForwardIntegratedPlusMass
  rw [intervalIntegral.integral_div]
  rw [intervalIntegral.integral_sub
    (cfzpProjectedMirrorPolarizedMinusMass_intervalIntegrable_of_safe hε hSafe X)
    (cfzpProjectedMirrorPolarizedPlusMass_intervalIntegrable_of_safe hε hSafe X)]

/-! ## E. Existing ledgers in integrated-mass form -/

theorem pascalCenteredXiPrimeSideFiniteTopZetaMismatchScalar_eq_integratedMass_difference_div_pi
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
        ((cfzpProjectedMirrorForwardIntegratedMinusMass ε X W -
          cfzpProjectedMirrorForwardIntegratedPlusMass ε X W) / 4) := by
  rw [pascalCenteredXiPrimeSideFiniteTopZetaMismatchScalar_eq_forwardPolarizedInteraction_div_pi
    hε hSafe hZeta hPHZ hWeighted hρ hρm hPairLeft hPairRight,
    cfzpProjectedMirrorForwardPolarizedInteractionIntegral_eq_integratedMass_difference
      hε hSafe X]

theorem pascalCenteredXiPrimeSideFiniteRectangleBackground_eq_integratedMass_difference_add_completionRemainder
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
          ((cfzpProjectedMirrorForwardIntegratedMinusMass ε X W -
            cfzpProjectedMirrorForwardIntegratedPlusMass ε X W) / 4) +
        cfzpFiniteRectangleCompletionRemainder ε W X := by
  rw [pascalCenteredXiPrimeSideFiniteRectangleBackground_eq_forwardPolarized_add_completionRemainder
    hε hSafe hZeta hPHZ hWeighted hρ hρm hPairLeft hPairRight,
    cfzpProjectedMirrorForwardPolarizedInteractionIntegral_eq_integratedMass_difference
      hε hSafe X]

theorem pascalCenteredXiPrimeSideFiniteRadialContactDeficit_eq_pi_mul_background_sub_integratedMass_difference
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
        (cfzpProjectedMirrorForwardIntegratedMinusMass ε X W -
          cfzpProjectedMirrorForwardIntegratedPlusMass ε X W) / 4 := by
  rw [pascalCenteredXiPrimeSideFiniteRadialContactDeficit_eq_pi_mul_background_sub_forwardPolarized
    hε hSafe hZeta hPHZ hWeighted hρ hρm hPairLeft hPairRight hArch hElem,
    cfzpProjectedMirrorForwardPolarizedInteractionIntegral_eq_integratedMass_difference
      hε hSafe X]

inductive CfzpIntegratedPolarizedBalanceToPointwiseBalanceGap : Prop
  | noPointwiseBalanceFromIntegratedCancellationProvided

end DkMath.RH.CFBRCProjection
