/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.CosmicFormulaZetaZeroCutoffRadialBudgetAudit
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CosmicFormulaZetaInteractionCutoffDynamicsAudit"

/-!
# CFZP-006R: prime-side interaction cutoff dynamics

The moving finite interaction ledger is driven by signed one-step updates:

`I (X + 1) = I X + 2 * Λ (X + 1) * K (X + 1)`.

The same update is subtracted from the signed radial-budget residual and the
radial contact deficit.  No sign, monotonicity, convergence, reach, zeta-zero,
or RH conclusion is supplied here.
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

/-! ## A. Signed cutoff increment and finite-sum fold -/

noncomputable def cfzpPrimeSideInteractionCutoffIncrement
    (ε : ℝ)
    (W : PascalCenteredXiResidueTransportWindow)
    (n : ℕ) : ℝ :=
  2 * (ArithmeticFunction.vonMangoldt n : ℝ) *
    pascalCenteredXiPrimeSideFiniteModeKernel ε W n

theorem cfzpPrimeSideInteractionCutoffIncrement_eq
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (n : ℕ) :
    cfzpPrimeSideInteractionCutoffIncrement ε W n =
      2 * (ArithmeticFunction.vonMangoldt n : ℝ) *
        pascalCenteredXiPrimeSideFiniteModeKernel ε W n := by
  rfl

theorem cfzpAggregateRayInteractionEnergy_eq_sum_cutoffIncrement
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W X =
      ∑ n ∈ Finset.range (X + 1),
        cfzpPrimeSideInteractionCutoffIncrement ε W n := by
  rw [pascalCenteredXiPrimeSideAggregateRayInteractionEnergy_eq_two_modeSum hε W X]
  rw [Finset.mul_sum]
  unfold cfzpPrimeSideInteractionCutoffIncrement
  apply Finset.sum_congr rfl
  intro n hn
  ring

/-! ## B. Exact interaction successor law -/

theorem cfzpAggregateRayInteractionEnergy_succ
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W (X + 1) =
      pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W X +
        cfzpPrimeSideInteractionCutoffIncrement ε W (X + 1) := by
  rw [cfzpAggregateRayInteractionEnergy_eq_sum_cutoffIncrement hε W (X + 1),
    cfzpAggregateRayInteractionEnergy_eq_sum_cutoffIncrement hε W X]
  rw [show X + 1 + 1 = (X + 1) + 1 by omega, Finset.sum_range_succ]

theorem cfzpAggregateRayInteractionEnergy_succ_sub
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W (X + 1) -
        pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W X =
      cfzpPrimeSideInteractionCutoffIncrement ε W (X + 1) := by
  have h := cfzpAggregateRayInteractionEnergy_succ hε W X
  linarith

/-! ## C. Signed radial-budget residual -/

noncomputable def cfzpRadialBudgetResidual
    (ε : ℝ)
    (W : PascalCenteredXiResidueTransportWindow)
    (X : ℕ) : ℝ :=
  Real.pi * pascalCenteredXiFixedRadialSecondMomentFunctional W.R -
    (Real.pi * pascalCenteredXiPrimeSideIndependentCorrectionSourceReal ε W +
      pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W X)

theorem cfzpRadialBudgetResidual_eq_def
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    cfzpRadialBudgetResidual ε W X =
      Real.pi * pascalCenteredXiFixedRadialSecondMomentFunctional W.R -
        (Real.pi * pascalCenteredXiPrimeSideIndependentCorrectionSourceReal ε W +
          pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W X) := by
  rfl

theorem cfzpRadialBudgetResidual_eq_radialContactDeficit
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    cfzpRadialBudgetResidual ε W X =
      pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W X := by
  have hbase :=
    cfzpZeroCutoffRadialContactBaseline_eq_pi_mul_fixedMoment_sub_correctionSource
      hε W
  have hzero :=
    cfzpZeroCutoffRadialContactBaseline_eq_zeroCutoff_deficit
      (ε := ε) (W := W)
  have hdeficit :=
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit_eq_zeroCutoff_deficit_sub_interaction
      hε W X
  calc
    cfzpRadialBudgetResidual ε W X =
        Real.pi * pascalCenteredXiFixedRadialSecondMomentFunctional W.R -
          (Real.pi * pascalCenteredXiPrimeSideIndependentCorrectionSourceReal ε W +
            pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W X) := rfl
    _ = Real.pi *
          (pascalCenteredXiFixedRadialSecondMomentFunctional W.R -
            pascalCenteredXiPrimeSideIndependentCorrectionSourceReal ε W) -
          pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W X := by ring
    _ = cfzpZeroCutoffRadialContactBaseline ε W -
          pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W X := by rw [hbase]
    _ = pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W 0 -
          pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W X := by rw [hzero]
    _ = pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W X := hdeficit.symm

/-! ## D. Residual and radial-deficit successor laws -/

theorem cfzpRadialContactDeficit_succ
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W (X + 1) =
      pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W X -
        cfzpPrimeSideInteractionCutoffIncrement ε W (X + 1) := by
  have hnext :=
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit_eq_zeroCutoff_deficit_sub_interaction
      hε W (X + 1)
  have hcurrent :=
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit_eq_zeroCutoff_deficit_sub_interaction
      hε W X
  have hinter := cfzpAggregateRayInteractionEnergy_succ hε W X
  rw [hnext, hcurrent, hinter]
  ring

theorem cfzpRadialBudgetResidual_succ
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    cfzpRadialBudgetResidual ε W (X + 1) =
      cfzpRadialBudgetResidual ε W X -
        cfzpPrimeSideInteractionCutoffIncrement ε W (X + 1) := by
  have hnext := cfzpRadialBudgetResidual_eq_radialContactDeficit hε W (X + 1)
  have hcurrent := cfzpRadialBudgetResidual_eq_radialContactDeficit hε W X
  have hdeficit := cfzpRadialContactDeficit_succ hε W X
  rw [hnext, hcurrent, hdeficit]

/-! ## E. von Mangoldt-zero no-update API -/

theorem cfzpPrimeSideInteractionCutoffIncrement_eq_zero_of_vonMangoldt_eq_zero
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (n : ℕ)
    (hΛ : (ArithmeticFunction.vonMangoldt n : ℝ) = 0) :
    cfzpPrimeSideInteractionCutoffIncrement ε W n = 0 := by
  simp [cfzpPrimeSideInteractionCutoffIncrement, hΛ]

theorem cfzpAggregateRayInteractionEnergy_succ_eq_of_vonMangoldt_eq_zero
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ)
    (hΛ : (ArithmeticFunction.vonMangoldt (X + 1) : ℝ) = 0) :
    pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W (X + 1) =
      pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W X := by
  have h := cfzpAggregateRayInteractionEnergy_succ hε W X
  have hinc := cfzpPrimeSideInteractionCutoffIncrement_eq_zero_of_vonMangoldt_eq_zero
    ε W (X + 1) hΛ
  rw [hinc, add_zero] at h
  exact h

theorem cfzpRadialBudgetResidual_succ_eq_of_vonMangoldt_eq_zero
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ)
    (hΛ : (ArithmeticFunction.vonMangoldt (X + 1) : ℝ) = 0) :
    cfzpRadialBudgetResidual ε W (X + 1) =
      cfzpRadialBudgetResidual ε W X := by
  have h := cfzpRadialBudgetResidual_succ hε W X
  have hinc := cfzpPrimeSideInteractionCutoffIncrement_eq_zero_of_vonMangoldt_eq_zero
    ε W (X + 1) hΛ
  rw [hinc, sub_zero] at h
  exact h

theorem cfzpRadialContactDeficit_succ_eq_of_vonMangoldt_eq_zero
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ)
    (hΛ : (ArithmeticFunction.vonMangoldt (X + 1) : ℝ) = 0) :
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W (X + 1) =
      pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W X := by
  have h := cfzpRadialContactDeficit_succ hε W X
  have hinc := cfzpPrimeSideInteractionCutoffIncrement_eq_zero_of_vonMangoldt_eq_zero
    ε W (X + 1) hΛ
  rw [hinc, sub_zero] at h
  exact h

/-! ## F. Support containment and explicit frontiers -/

theorem cfzpPrimeSideInteractionCutoffIncrement_ne_zero_implies_vonMangoldt_ne_zero
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (n : ℕ)
    (hinc : cfzpPrimeSideInteractionCutoffIncrement ε W n ≠ 0) :
    (ArithmeticFunction.vonMangoldt n : ℝ) ≠ 0 := by
  intro hΛ
  exact hinc (cfzpPrimeSideInteractionCutoffIncrement_eq_zero_of_vonMangoldt_eq_zero
    ε W n hΛ)

theorem cfzpPrimeSideInteractionCutoffIncrement_ne_zero_implies_modeKernel_ne_zero
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (n : ℕ)
    (hinc : cfzpPrimeSideInteractionCutoffIncrement ε W n ≠ 0) :
    pascalCenteredXiPrimeSideFiniteModeKernel ε W n ≠ 0 := by
  intro hK
  apply hinc
  simp [cfzpPrimeSideInteractionCutoffIncrement, hK]

inductive CfzpInteractionCutoffIncrementSignGap : Prop
  | noIndependentFiniteModeKernelSignProvider

inductive CfzpInteractionCutoffReachDynamicsGap : Prop
  | noIndependentSuccessorDynamicsToBaselineReachProvider

inductive CfzpInteractionIncrementPrimePowerSupportBridgeGap : Prop
  | noPrimePowerSupportClassificationExposedHere

end DkMath.RH.CFBRCProjection
