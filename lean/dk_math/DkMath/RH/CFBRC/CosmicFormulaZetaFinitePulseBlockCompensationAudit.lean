/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.RH.CFBRC.CosmicFormulaZetaVonMangoldtPulseCompressionAudit
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CosmicFormulaZetaFinitePulseBlockCompensationAudit"

/-!
# CFZP-022: finite pulse-block compensation

This module lifts the CFZP-021 one-mode pulse recurrence to a finite
right-closed block `(A, B]`.  The resulting identities are finite
telescopes: no infinite sum, limit exchange, sign provider, or RH statement
is introduced.  In the safe-frequency regime the same block is expressed as
the positive-mass block minus the negative-debt block from CFZP-019/020.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.Analysis
open DkMath.NumberTheory
open DkMath.NumberTheory.PrimitiveSet

/-! ## Gate A: finite pulse blocks -/

/-- The signed von-Mangoldt pulse accumulated over the finite interval `(A, B]`. -/
noncomputable def cfzp022VonMangoldtPulseBlock
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (A B : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ioc A B, cfzp021VonMangoldtPulse ε W n

/-- A block with equal endpoints is empty. -/
theorem cfzp022VonMangoldtPulseBlock_self
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (A : ℕ) :
    cfzp022VonMangoldtPulseBlock ε W A A = 0 := by
  simp [cfzp022VonMangoldtPulseBlock]

/-- Extending a nonempty right-closed block by one endpoint adds one pulse. -/
theorem cfzp022VonMangoldtPulseBlock_succ_top
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    {A B : ℕ} (hAB : A ≤ B) :
    cfzp022VonMangoldtPulseBlock ε W A (B + 1) =
      cfzp022VonMangoldtPulseBlock ε W A B +
        cfzp021VonMangoldtPulse ε W (B + 1) := by
  unfold cfzp022VonMangoldtPulseBlock
  rw [Finset.sum_Ioc_succ_top hAB]

/-! ## Gate B: finite telescopes -/

/-- The aggregate interaction telescope is the sum of the pulses in a block. -/
theorem cfzp022AggregateRayInteractionEnergy_block_sub_eq_pulseBlock
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) {A B : ℕ} (hAB : A ≤ B) :
    pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W B -
        pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W A =
      cfzp022VonMangoldtPulseBlock ε W A B := by
  induction B, hAB using Nat.le_induction with
  | base =>
      simp [cfzp022VonMangoldtPulseBlock]
  | succ B hAB ih =>
      rw [cfzp021AggregateRayInteractionEnergy_succ_eq_add_pulse hε W B,
        cfzp022VonMangoldtPulseBlock_succ_top ε W hAB]
      linarith

/-- The branch-free ledger telescope has the same pulse block. -/
theorem cfzp022BranchFreeTrigLedger_block_sub_eq_pulseBlock
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow) {A B : ℕ} (hAB : A ≤ B) :
    cfzpPrimePowerBranchFreeTrigLedger ε W B -
        cfzpPrimePowerBranchFreeTrigLedger ε W A =
      cfzp022VonMangoldtPulseBlock ε W A B := by
  induction B, hAB using Nat.le_induction with
  | base =>
      simp [cfzp022VonMangoldtPulseBlock]
  | succ B hAB ih =>
      rw [cfzp021BranchFreeTrigLedger_succ_eq_add_pulse hε hε2 W B,
        cfzp022VonMangoldtPulseBlock_succ_top ε W hAB]
      linarith

/-- The radial contact deficit changes by the negative of the block pulse. -/
theorem cfzp022RadialContactDeficit_block_eq_sub_pulseBlock
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow) {A B : ℕ} (hAB : A ≤ B) :
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W B =
      pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W A -
        cfzp022VonMangoldtPulseBlock ε W A B := by
  induction B, hAB using Nat.le_induction with
  | base =>
      simp [cfzp022VonMangoldtPulseBlock]
  | succ B hAB ih =>
      rw [cfzp021RadialContactDeficit_succ_eq_sub_pulse hε hε2 W B,
        cfzp022VonMangoldtPulseBlock_succ_top ε W hAB]
      rw [ih]
      ring

/-! ## Gate C: signed mass blocks -/

/-- The positive signed-mass increment between two cutoffs. -/
noncomputable def cfzp022BranchFreePositiveEventMassBlock
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (A B : ℕ) : ℝ :=
  cfzp019BranchFreePositiveEventMass ε W B -
    cfzp019BranchFreePositiveEventMass ε W A

/-- The negative-debt increment between two cutoffs. -/
noncomputable def cfzp022BranchFreeNegativeEventDebtBlock
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (A B : ℕ) : ℝ :=
  cfzp019BranchFreeNegativeEventDebt ε W B -
    cfzp019BranchFreeNegativeEventDebt ε W A

theorem cfzp022BranchFreePositiveEventMassBlock_nonneg
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    {A B : ℕ} (hAB : A ≤ B) :
    0 ≤ cfzp022BranchFreePositiveEventMassBlock ε W A B := by
  unfold cfzp022BranchFreePositiveEventMassBlock
  exact sub_nonneg.mpr (cfzp020PositiveEventMass_mono ε W hAB)

theorem cfzp022BranchFreeNegativeEventDebtBlock_nonneg
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    {A B : ℕ} (hAB : A ≤ B) :
    0 ≤ cfzp022BranchFreeNegativeEventDebtBlock ε W A B := by
  unfold cfzp022BranchFreeNegativeEventDebtBlock
  exact sub_nonneg.mpr (cfzp020NegativeEventDebt_mono ε W hAB)

/-- The pulse block is positive mass minus negative debt. -/
theorem cfzp022VonMangoldtPulseBlock_eq_positiveMassBlock_sub_negativeDebtBlock
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow) {A B : ℕ} (hAB : A ≤ B) :
    cfzp022VonMangoldtPulseBlock ε W A B =
      cfzp022BranchFreePositiveEventMassBlock ε W A B -
        cfzp022BranchFreeNegativeEventDebtBlock ε W A B := by
  have hledger := cfzp022BranchFreeTrigLedger_block_sub_eq_pulseBlock
    hε hε2 W hAB
  rw [cfzp019BranchFreeTrigLedger_eq_positiveMass_sub_negativeDebt,
    cfzp019BranchFreeTrigLedger_eq_positiveMass_sub_negativeDebt] at hledger
  rw [← hledger]
  unfold cfzp022BranchFreePositiveEventMassBlock
    cfzp022BranchFreeNegativeEventDebtBlock
  ring

/-- The radial block recurrence in signed-mass coordinates. -/
theorem cfzp022RadialContactDeficit_block_eq_add_debt_sub_positiveMass
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow) {A B : ℕ} (hAB : A ≤ B) :
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W B =
      pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W A +
        cfzp022BranchFreeNegativeEventDebtBlock ε W A B -
        cfzp022BranchFreePositiveEventMassBlock ε W A B := by
  rw [cfzp022RadialContactDeficit_block_eq_sub_pulseBlock hε hε2 W hAB,
    cfzp022VonMangoldtPulseBlock_eq_positiveMassBlock_sub_negativeDebtBlock
      hε hε2 W hAB]
  ring

/-! ## Gate D: finite compensation inequality -/

/-- A terminal radial slack is exactly a finite signed block budget. -/
theorem cfzp022RadialContactDeficit_le_iff_finitePulseBlockCompensation
    {ε η : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow) {A B : ℕ} (hAB : A ≤ B) :
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W B ≤ η ↔
      pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W A +
          cfzp022BranchFreeNegativeEventDebtBlock ε W A B ≤
        cfzp022BranchFreePositiveEventMassBlock ε W A B + η := by
  rw [cfzp022RadialContactDeficit_block_eq_add_debt_sub_positiveMass
    hε hε2 W hAB]
  constructor <;> intro h <;> linarith

/-- The fixed-epsilon finite pulse-block compensation contract. -/
def Cfzp022FinitePulseBlockCompensationAt
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) : Prop :=
  ∀ η : ℝ, 0 < η → ∀ A : ℕ, ∃ B : ℕ, A ≤ B ∧
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W A +
        cfzp022BranchFreeNegativeEventDebtBlock ε W A B ≤
      cfzp022BranchFreePositiveEventMassBlock ε W A B + η

/-- Finite pulse-block compensation is the existing cofinal contact contract. -/
theorem cfzp022FinitePulseBlockCompensationAt_iff_contactZero
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow) :
    Cfzp022FinitePulseBlockCompensationAt ε W ↔
      PascalCenteredXiPrimeSideCofinalRadialContactZeroAt ε W := by
  unfold Cfzp022FinitePulseBlockCompensationAt
    PascalCenteredXiPrimeSideCofinalRadialContactZeroAt
    PascalCenteredXiPrimeSideCofinalRadialContactAt
  constructor
  · intro h η hη N
    rcases h η hη N with ⟨B, hNB, hbudget⟩
    refine ⟨B, hNB, ?_⟩
    simpa using (cfzp022RadialContactDeficit_le_iff_finitePulseBlockCompensation
      (η := η) hε hε2 W hNB).mpr hbudget
  · intro h η hη A
    rcases h η hη A with ⟨B, hAB, hcontact⟩
    refine ⟨B, hAB, ?_⟩
    apply (cfzp022RadialContactDeficit_le_iff_finitePulseBlockCompensation
      (η := η) hε hε2 W hAB).mp
    simpa using hcontact

/-! ## Gate E: finite quiescence and provider firewall -/

/-- A block containing no prime-power mode has zero pulse compensation. -/
theorem cfzp022VonMangoldtPulseBlock_eq_zero_of_forall_not_isPrimePow
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) {A B : ℕ}
    (hzero : ∀ n ∈ Finset.Ioc A B, ¬ IsPrimePow n) :
    cfzp022VonMangoldtPulseBlock ε W A B = 0 := by
  unfold cfzp022VonMangoldtPulseBlock
  apply Finset.sum_eq_zero
  intro n hn
  exact cfzp021VonMangoldtPulse_eq_zero_of_not_isPrimePow ε W n (hzero n hn)

/-- The missing cofinal block provider is recorded explicitly. -/
inductive Cfzp022FinitePulseBlockCompensationGap : Prop
  | noIndependentCofinalSignedPulseBlockBudgetProvider

end DkMath.RH.CFBRCProjection
