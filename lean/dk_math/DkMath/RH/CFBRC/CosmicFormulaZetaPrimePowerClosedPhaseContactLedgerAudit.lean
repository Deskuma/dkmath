/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.CosmicFormulaZetaInteractionModeKernelPhaseBalanceAudit
import DkMath.RH.CFBRC.PascalCenteredXiPrimeSidePrimePowerRayAudit
import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideInteractionPhaseBoundaryAudit
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CosmicFormulaZetaPrimePowerClosedPhaseContactLedgerAudit"

/-!
# CFZP-006U: prime-power closed-phase contact ledger

The finite signed interaction is reindexed through the canonical
prime-power pair support and written with the already-verified closed phase
boundary form.  The resulting ledger is exact and finite.  No event sign,
monotonicity, baseline reach, convergence, zeta-zero, or RH conclusion is
provided here.
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

/-! ## A. One witnessed prime-power closed-phase event -/

noncomputable def cfzpPrimePowerClosedPhaseEvent
    (ε : ℝ)
    (W : PascalCenteredXiResidueTransportWindow)
    (p j : ℕ) : ℝ :=
  2 * Real.log (p : ℝ) *
    ((2 * ε)⁻¹ * cfzpModeCriticalScale (p ^ j) *
      (pascalCenteredXiPrimeSidePhasePrimitiveClosedForm
          (cfzpModePhaseAbscissa W)
          (ε - (j : ℝ) * Real.log (p : ℝ))
          W.rectangle.T -
        pascalCenteredXiPrimeSidePhasePrimitiveClosedForm
          (cfzpModePhaseAbscissa W)
          (-ε - (j : ℝ) * Real.log (p : ℝ))
          W.rectangle.T))

theorem cfzpPrimePowerClosedPhaseEvent_eq_interactionIncrement
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow)
    {p j : ℕ} (hp : Nat.Prime p) (hj : 0 < j) :
    cfzpPrimePowerClosedPhaseEvent ε W p j =
      cfzpPrimeSideInteractionCutoffIncrement ε W (p ^ j) := by
  rw [cfzpPrimePowerClosedPhaseEvent,
    cfzpPrimeSideInteractionCutoffIncrement_eq_two_log_mul_modeKernel_of_eq_prime_pow
      ε W hp hj rfl]
  rw [cfzpPrimeSideFiniteModeKernel_eq_scaled_primePowerPhasePrimitiveDifference
    hε W hp hj]
  rw [pascalCenteredXiPrimeSidePhasePrimitive_eq_closedForm,
    pascalCenteredXiPrimeSidePhasePrimitive_eq_closedForm]

theorem cfzpPrimePowerClosedPhaseEvent_eq_two_log_mul_modeKernel
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow)
    {p j : ℕ} (hp : Nat.Prime p) (hj : 0 < j) :
    cfzpPrimePowerClosedPhaseEvent ε W p j =
      2 * Real.log (p : ℝ) *
        pascalCenteredXiPrimeSideFiniteModeKernel ε W (p ^ j) := by
  rw [cfzpPrimePowerClosedPhaseEvent_eq_interactionIncrement hε W hp hj,
    cfzpPrimeSideInteractionCutoffIncrement_eq_two_log_mul_modeKernel_of_eq_prime_pow
      ε W hp hj rfl]

/-! ## B. Pair-support cumulative signed ledger -/

noncomputable def cfzpPrimePowerClosedPhaseLedger
    (ε : ℝ)
    (W : PascalCenteredXiResidueTransportWindow)
    (X : ℕ) : ℝ :=
  ∑ pk ∈ pascalPrimePowerPairSupportUpTo X,
    cfzpPrimePowerClosedPhaseEvent ε W pk.1 (pk.2 + 1)

/-! ## C. Aggregate interaction as the closed-phase ledger -/

theorem cfzpAggregateRayInteractionEnergy_eq_primePowerClosedPhaseLedger
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W X =
      cfzpPrimePowerClosedPhaseLedger ε W X := by
  rw [pascalCenteredXiPrimeSideAggregateRayInteractionEnergy_eq_two_modeSum hε W X,
    pascalCenteredXiPrimeSideFiniteModeSum_eq_canonicalPrimePowerSupport hε W X,
    pascalCenteredXiPrimeSideCanonicalModeSum_eq_pairSupport hε W X]
  unfold cfzpPrimePowerClosedPhaseLedger
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro pk hpk
  have hsupport := mem_pascalPrimePowerPairSupportUpTo_iff.mp hpk
  have hp := (mem_pascalPrimeCoordinateSupportUpTo_iff.mp hsupport.1).1
  have hj : 0 < pk.2 + 1 := by omega
  have hevent := cfzpPrimePowerClosedPhaseEvent_eq_two_log_mul_modeKernel
    hε W hp hj
  simpa [mul_assoc] using hevent.symm

/-! ## D. Residual and radial-deficit ledger identities -/

theorem cfzpRadialBudgetResidual_eq_zeroCutoffBaseline_sub_primePowerClosedPhaseLedger
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    cfzpRadialBudgetResidual ε W X =
      cfzpZeroCutoffRadialContactBaseline ε W -
        cfzpPrimePowerClosedPhaseLedger ε W X := by
  have hbase :=
    cfzpZeroCutoffRadialContactBaseline_eq_pi_mul_fixedMoment_sub_correctionSource
      hε W
  have hledger :=
    cfzpAggregateRayInteractionEnergy_eq_primePowerClosedPhaseLedger hε W X
  calc
    cfzpRadialBudgetResidual ε W X =
        Real.pi * pascalCenteredXiFixedRadialSecondMomentFunctional W.R -
          (Real.pi * pascalCenteredXiPrimeSideIndependentCorrectionSourceReal ε W +
            pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W X) := rfl
    _ = cfzpZeroCutoffRadialContactBaseline ε W -
          pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W X := by
      rw [hbase]
      ring
    _ = cfzpZeroCutoffRadialContactBaseline ε W -
          cfzpPrimePowerClosedPhaseLedger ε W X := by rw [hledger]

theorem cfzpRadialContactDeficit_eq_zeroCutoffBaseline_sub_primePowerClosedPhaseLedger
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W X =
      cfzpZeroCutoffRadialContactBaseline ε W -
        cfzpPrimePowerClosedPhaseLedger ε W X := by
  calc
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W X =
        cfzpRadialBudgetResidual ε W X :=
      (cfzpRadialBudgetResidual_eq_radialContactDeficit hε W X).symm
    _ = cfzpZeroCutoffRadialContactBaseline ε W -
          cfzpPrimePowerClosedPhaseLedger ε W X :=
      cfzpRadialBudgetResidual_eq_zeroCutoffBaseline_sub_primePowerClosedPhaseLedger
        hε W X

/-! ## E. Finite contact and order classification -/

theorem cfzpRadialBudgetResidual_eq_zero_iff_primePowerClosedPhaseLedger_reaches_baseline
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    cfzpRadialBudgetResidual ε W X = 0 ↔
      cfzpPrimePowerClosedPhaseLedger ε W X =
        cfzpZeroCutoffRadialContactBaseline ε W := by
  rw [cfzpRadialBudgetResidual_eq_zeroCutoffBaseline_sub_primePowerClosedPhaseLedger
    hε W X]
  constructor <;> intro h <;> linarith

theorem cfzpRadialContactDeficit_eq_zero_iff_primePowerClosedPhaseLedger_reaches_baseline
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W X = 0 ↔
      cfzpPrimePowerClosedPhaseLedger ε W X =
        cfzpZeroCutoffRadialContactBaseline ε W := by
  rw [cfzpRadialContactDeficit_eq_zeroCutoffBaseline_sub_primePowerClosedPhaseLedger
    hε W X]
  constructor <;> intro h <;> linarith

theorem cfzpRadialBudgetResidual_nonneg_iff_primePowerClosedPhaseLedger_le_baseline
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    0 ≤ cfzpRadialBudgetResidual ε W X ↔
      cfzpPrimePowerClosedPhaseLedger ε W X ≤
        cfzpZeroCutoffRadialContactBaseline ε W := by
  rw [cfzpRadialBudgetResidual_eq_zeroCutoffBaseline_sub_primePowerClosedPhaseLedger
    hε W X]
  constructor <;> intro h <;> linarith

theorem cfzpRadialBudgetResidual_nonpos_iff_baseline_le_primePowerClosedPhaseLedger
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    cfzpRadialBudgetResidual ε W X ≤ 0 ↔
      cfzpZeroCutoffRadialContactBaseline ε W ≤
        cfzpPrimePowerClosedPhaseLedger ε W X := by
  rw [cfzpRadialBudgetResidual_eq_zeroCutoffBaseline_sub_primePowerClosedPhaseLedger
    hε W X]
  constructor <;> intro h <;> linarith

theorem cfzpRadialContactDeficit_nonneg_iff_primePowerClosedPhaseLedger_le_baseline
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    0 ≤ pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W X ↔
      cfzpPrimePowerClosedPhaseLedger ε W X ≤
        cfzpZeroCutoffRadialContactBaseline ε W := by
  rw [cfzpRadialContactDeficit_eq_zeroCutoffBaseline_sub_primePowerClosedPhaseLedger
    hε W X]
  constructor <;> intro h <;> linarith

theorem cfzpRadialContactDeficit_nonpos_iff_baseline_le_primePowerClosedPhaseLedger
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W X ≤ 0 ↔
      cfzpZeroCutoffRadialContactBaseline ε W ≤
        cfzpPrimePowerClosedPhaseLedger ε W X := by
  rw [cfzpRadialContactDeficit_eq_zeroCutoffBaseline_sub_primePowerClosedPhaseLedger
    hε W X]
  constructor <;> intro h <;> linarith

inductive CfzpPrimePowerClosedPhaseBaselineReachGap : Prop
  | noIndependentFiniteOrCofinalClosedPhaseLedgerReachProvider

end DkMath.RH.CFBRCProjection
