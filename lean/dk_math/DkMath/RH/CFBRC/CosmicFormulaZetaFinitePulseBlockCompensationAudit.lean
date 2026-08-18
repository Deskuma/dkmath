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

/-- The one-step block is exactly the next pulse. -/
theorem cfzp022VonMangoldtPulseBlock_succ_eq_pulse
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    cfzp022VonMangoldtPulseBlock ε W X (X + 1) =
      cfzp021VonMangoldtPulse ε W (X + 1) := by
  simp [cfzp022VonMangoldtPulseBlock]

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

/-- Additive form of the aggregate block telescope. -/
theorem cfzp022AggregateRayInteractionEnergy_eq_add_pulseBlock
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) {A B : ℕ} (hAB : A ≤ B) :
    pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W B =
      pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W A +
        cfzp022VonMangoldtPulseBlock ε W A B := by
  linarith [cfzp022AggregateRayInteractionEnergy_block_sub_eq_pulseBlock
    hε W hAB]

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

/-- Additive form of the safe-frequency ledger block telescope. -/
theorem cfzp022BranchFreeTrigLedger_eq_add_pulseBlock
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow) {A B : ℕ} (hAB : A ≤ B) :
    cfzpPrimePowerBranchFreeTrigLedger ε W B =
      cfzpPrimePowerBranchFreeTrigLedger ε W A +
        cfzp022VonMangoldtPulseBlock ε W A B := by
  linarith [cfzp022BranchFreeTrigLedger_block_sub_eq_pulseBlock
    hε hε2 W hAB]

/-- The radial contact deficit changes by the negative of the block pulse. -/
theorem cfzp022RadialContactDeficit_block_eq_sub_pulseBlock
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) {A B : ℕ} (hAB : A ≤ B) :
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W B =
      pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W A -
        cfzp022VonMangoldtPulseBlock ε W A B := by
  induction B, hAB using Nat.le_induction with
  | base =>
      simp [cfzp022VonMangoldtPulseBlock]
  | succ B hAB ih =>
      have hstep := cfzpRadialContactDeficit_succ hε W B
      rw [← cfzp021VonMangoldtPulse_eq_interactionCutoffIncrement
        ε W (B + 1)] at hstep
      rw [hstep, cfzp022VonMangoldtPulseBlock_succ_top ε W hAB]
      rw [ih]
      ring

/-! ## Gate E: pulse payment and block concatenation -/

/-- The endpoint slack is equivalent to payment by the signed pulse block. -/
theorem cfzp022RadialContactDeficit_le_iff_pulseBlock_pays
    {ε η : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) {A B : ℕ} (hAB : A ≤ B) :
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W B ≤ η ↔
      pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W A ≤
        cfzp022VonMangoldtPulseBlock ε W A B + η := by
  rw [cfzp022RadialContactDeficit_block_eq_sub_pulseBlock hε W hAB]
  constructor <;> intro h <;> linarith

/-- A pulse block is additive under a finite partition of its interval. -/
theorem cfzp022VonMangoldtPulseBlock_add
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    {A B C : ℕ} (hAB : A ≤ B) (hBC : B ≤ C) :
    cfzp022VonMangoldtPulseBlock ε W A C =
      cfzp022VonMangoldtPulseBlock ε W A B +
        cfzp022VonMangoldtPulseBlock ε W B C := by
  unfold cfzp022VonMangoldtPulseBlock
  rw [← Finset.Ioc_union_Ioc_eq_Ioc hAB hBC,
    Finset.sum_union (Finset.Ioc_disjoint_Ioc_of_le le_rfl)]

/-! ## Gate G: signed mass blocks -/

/-- The positive event mass accumulated on the finite block `(A, B]`. -/
noncomputable def cfzp022BlockPositiveEventMass
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (A B : ℕ) : ℝ :=
  cfzp019BranchFreePositiveEventMass ε W B -
    cfzp019BranchFreePositiveEventMass ε W A

/-- The negative event debt accumulated on the finite block `(A, B]`. -/
noncomputable def cfzp022BlockNegativeEventDebt
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (A B : ℕ) : ℝ :=
  cfzp019BranchFreeNegativeEventDebt ε W B -
    cfzp019BranchFreeNegativeEventDebt ε W A

/-- Compatibility name for the positive block increment. -/
noncomputable def cfzp022BranchFreePositiveEventMassBlock
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (A B : ℕ) : ℝ :=
  cfzp022BlockPositiveEventMass ε W A B

/-- Compatibility name for the negative-debt block increment. -/
noncomputable def cfzp022BranchFreeNegativeEventDebtBlock
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (A B : ℕ) : ℝ :=
  cfzp022BlockNegativeEventDebt ε W A B

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

/-- Nonnegativity of the positive block mass for ordered cutoffs. -/
theorem cfzp022BlockPositiveEventMass_nonneg
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    {A B : ℕ} (hAB : A ≤ B) :
    0 ≤ cfzp022BlockPositiveEventMass ε W A B := by
  simpa [cfzp022BranchFreePositiveEventMassBlock] using
    cfzp022BranchFreePositiveEventMassBlock_nonneg ε W hAB

/-- Nonnegativity of the negative block debt for ordered cutoffs. -/
theorem cfzp022BlockNegativeEventDebt_nonneg
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    {A B : ℕ} (hAB : A ≤ B) :
    0 ≤ cfzp022BlockNegativeEventDebt ε W A B := by
  simpa [cfzp022BranchFreeNegativeEventDebtBlock] using
    cfzp022BranchFreeNegativeEventDebtBlock_nonneg ε W hAB

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
    cfzp022BlockPositiveEventMass cfzp022BlockNegativeEventDebt
  ring

/-- The pulse block is positive block mass minus negative block debt. -/
theorem cfzp022VonMangoldtPulseBlock_eq_blockPositiveMass_sub_blockNegativeDebt
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow) {A B : ℕ} (hAB : A ≤ B) :
    cfzp022VonMangoldtPulseBlock ε W A B =
      cfzp022BlockPositiveEventMass ε W A B -
        cfzp022BlockNegativeEventDebt ε W A B := by
  simpa [cfzp022BranchFreePositiveEventMassBlock,
    cfzp022BranchFreeNegativeEventDebtBlock] using
    (cfzp022VonMangoldtPulseBlock_eq_positiveMassBlock_sub_negativeDebtBlock
      hε hε2 W hAB)

/-- The radial block recurrence in signed-mass coordinates. -/
theorem cfzp022RadialContactDeficit_block_eq_add_debt_sub_positiveMass
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow) {A B : ℕ} (hAB : A ≤ B) :
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W B =
      pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W A +
        cfzp022BranchFreeNegativeEventDebtBlock ε W A B -
        cfzp022BranchFreePositiveEventMassBlock ε W A B := by
  rw [cfzp022RadialContactDeficit_block_eq_sub_pulseBlock hε W hAB,
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

/-- The local signed block budget in the preferred CFZP-022 coordinates. -/
theorem cfzp022RadialContactDeficit_le_iff_signedBlockBudget
    {ε η : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow) {A B : ℕ} (hAB : A ≤ B) :
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W B ≤ η ↔
      pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W A +
          cfzp022BlockNegativeEventDebt ε W A B ≤
        cfzp022BlockPositiveEventMass ε W A B + η := by
  simpa [cfzp022BranchFreePositiveEventMassBlock,
    cfzp022BranchFreeNegativeEventDebtBlock] using
    (cfzp022RadialContactDeficit_le_iff_finitePulseBlockCompensation
      hε hε2 W hAB)

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

/-! ## Gate I/J: cofinal block contracts -/

/-- Every starting cutoff admits a finite pulse block paying its current
deficit up to any positive slack. -/
def Cfzp022CofinalFinitePulseBlockCompensationAt
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) : Prop :=
  ∀ η : ℝ, 0 < η → ∀ A : ℕ, ∃ B : ℕ, A ≤ B ∧
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W A ≤
      cfzp022VonMangoldtPulseBlock ε W A B + η

/-- The finite pulse-block compensation contract is a coordinate change of
the CS22 cofinal radial-contact contract. -/
theorem cfzp022CofinalFinitePulseBlockCompensationAt_iff_contactZero
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) :
    Cfzp022CofinalFinitePulseBlockCompensationAt ε W ↔
      PascalCenteredXiPrimeSideCofinalRadialContactZeroAt ε W := by
  unfold Cfzp022CofinalFinitePulseBlockCompensationAt
    PascalCenteredXiPrimeSideCofinalRadialContactZeroAt
    PascalCenteredXiPrimeSideCofinalRadialContactAt
  constructor
  · intro h η hη N
    rcases h η hη N with ⟨B, hNB, hpay⟩
    refine ⟨B, hNB, ?_⟩
    have hB := (cfzp022RadialContactDeficit_le_iff_pulseBlock_pays
      (η := η) hε W hNB).mpr hpay
    simpa using hB
  · intro h η hη A
    rcases h η hη A with ⟨B, hAB, hcontact⟩
    refine ⟨B, hAB, ?_⟩
    apply (cfzp022RadialContactDeficit_le_iff_pulseBlock_pays
      (η := η) hε W hAB).mp
    simpa using hcontact

/-- The cofinal signed block budget contract. -/
def Cfzp022CofinalSignedPulseBlockBudgetAt
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) : Prop :=
  ∀ η : ℝ, 0 < η → ∀ A : ℕ, ∃ B : ℕ, A ≤ B ∧
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W A +
        cfzp022BlockNegativeEventDebt ε W A B ≤
      cfzp022BlockPositiveEventMass ε W A B + η

/-- Safe-frequency signed block budget is equivalent to raw block payment. -/
theorem cfzp022CofinalSignedPulseBlockBudgetAt_iff_finiteCompensation
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow) :
    Cfzp022CofinalSignedPulseBlockBudgetAt ε W ↔
      Cfzp022CofinalFinitePulseBlockCompensationAt ε W := by
  unfold Cfzp022CofinalSignedPulseBlockBudgetAt
    Cfzp022CofinalFinitePulseBlockCompensationAt
  constructor
  · intro h η hη A
    rcases h η hη A with ⟨B, hAB, hbudget⟩
    refine ⟨B, hAB, ?_⟩
    exact (cfzp022RadialContactDeficit_le_iff_pulseBlock_pays
      (η := η) hε W hAB).mp
      ((cfzp022RadialContactDeficit_le_iff_signedBlockBudget
        (η := η) hε hε2 W hAB).mpr hbudget)
  · intro h η hη A
    rcases h η hη A with ⟨B, hAB, hpay⟩
    refine ⟨B, hAB, ?_⟩
    exact (cfzp022RadialContactDeficit_le_iff_signedBlockBudget
      (η := η) hε hε2 W hAB).mp
      ((cfzp022RadialContactDeficit_le_iff_pulseBlock_pays
        (η := η) hε W hAB).mpr hpay)

/-- The cofinal signed block budget is exactly the existing CS22 contract. -/
theorem cfzp022CofinalSignedPulseBlockBudgetAt_iff_contactZero
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow) :
    Cfzp022CofinalSignedPulseBlockBudgetAt ε W ↔
      PascalCenteredXiPrimeSideCofinalRadialContactZeroAt ε W :=
  (cfzp022CofinalSignedPulseBlockBudgetAt_iff_finiteCompensation hε hε2 W).trans
    (cfzp022CofinalFinitePulseBlockCompensationAt_iff_contactZero hε W)

/-- The signed block budget is equivalent to the CFZP-019 budget interface. -/
theorem cfzp022CofinalSignedPulseBlockBudgetAt_iff_cfzp019
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow) :
    Cfzp022CofinalSignedPulseBlockBudgetAt ε W ↔
      Cfzp019CofinalBranchFreeSignedMassBudgetAt ε W :=
  (cfzp022CofinalSignedPulseBlockBudgetAt_iff_contactZero hε hε2 W).trans
    (cfzp019CofinalBranchFreeSignedMassBudgetAt_iff_contactZero hε hε2 W).symm

/-- The signed block budget is also equivalent to CFZP-018 approximate reach. -/
theorem cfzp022CofinalSignedPulseBlockBudgetAt_iff_cfzp018
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow) :
    Cfzp022CofinalSignedPulseBlockBudgetAt ε W ↔
      Cfzp018CofinalPrimeThresholdApproximateReachAt ε W :=
  (cfzp022CofinalSignedPulseBlockBudgetAt_iff_contactZero hε hε2 W).trans
    (cfzp018CofinalPrimeThresholdApproximateReachAt_iff_csf hε W).symm

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
