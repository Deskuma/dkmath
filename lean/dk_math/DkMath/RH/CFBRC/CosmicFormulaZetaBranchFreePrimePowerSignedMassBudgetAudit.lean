/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.RH.CFBRC.CosmicFormulaZetaPrimeThresholdApproximateReachFrontierAudit
import DkMath.RH.CFBRC.CosmicFormulaZetaSafeFrequencyTrigonometricPhaseBoundaryAudit
import DkMath.RH.CFBRC.CosmicFormulaZetaPrimePowerCenteredPhaseCellCoverageAudit
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CosmicFormulaZetaBranchFreePrimePowerSignedMassBudgetAudit"

/-!
# CFZP-019: branch-free prime-power signed-mass budget

This module splits each existing branch-free prime-power event into its
canonical positive mass and negative debt.  The same finite pair-support
ledger is then rewritten as `positive mass - negative debt`, and the safe
frequency radial deficit is rewritten as a baseline plus debt minus mass.

The resulting cofinal budget is exactly the existing CS22/CFZP-018
arbitrary-slack contract.  Local phase-cell signs are transported only to
local mass/debt eliminations; no independent budget provider, phase
coverage theorem, joint limit, or RH statement is introduced.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open Set
open scoped Topology

/-! ## Gate A: one-event signed decomposition -/

/-- The canonical positive part of an existing branch-free prime-power event. -/
noncomputable def cfzp019PrimePowerEventPositiveMass
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (p j : ℕ) : ℝ :=
  max (cfzpPrimePowerBranchFreeTrigEvent ε W p j) 0

/-- The canonical negative debt carried by an existing branch-free event. -/
noncomputable def cfzp019PrimePowerEventNegativeDebt
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (p j : ℕ) : ℝ :=
  max (-cfzpPrimePowerBranchFreeTrigEvent ε W p j) 0

theorem cfzp019PrimePowerEventPositiveMass_nonneg
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (p j : ℕ) :
    0 ≤ cfzp019PrimePowerEventPositiveMass ε W p j := by
  exact le_max_right _ _

theorem cfzp019PrimePowerEventNegativeDebt_nonneg
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (p j : ℕ) :
    0 ≤ cfzp019PrimePowerEventNegativeDebt ε W p j := by
  exact le_max_right _ _

/-- Every real event is the difference of its positive mass and negative debt. -/
theorem cfzp019PrimePowerEvent_eq_positiveMass_sub_negativeDebt
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (p j : ℕ) :
    cfzpPrimePowerBranchFreeTrigEvent ε W p j =
      cfzp019PrimePowerEventPositiveMass ε W p j -
        cfzp019PrimePowerEventNegativeDebt ε W p j := by
  by_cases h : 0 ≤ cfzpPrimePowerBranchFreeTrigEvent ε W p j
  · rw [cfzp019PrimePowerEventPositiveMass, max_eq_left h,
      cfzp019PrimePowerEventNegativeDebt,
      max_eq_right (neg_nonpos.mpr h)]
    ring
  · have hn : cfzpPrimePowerBranchFreeTrigEvent ε W p j ≤ 0 :=
      le_of_not_ge h
    rw [cfzp019PrimePowerEventPositiveMass, max_eq_right hn,
      cfzp019PrimePowerEventNegativeDebt,
      max_eq_left (neg_nonneg.mpr hn)]
    ring

/-! ## Gate B: local sign adapters -/

theorem cfzp019PrimePowerEventPositiveMass_eq_of_nonneg
    {ε : ℝ} (W : PascalCenteredXiResidueTransportWindow) (p j : ℕ)
    (he : 0 ≤ cfzpPrimePowerBranchFreeTrigEvent ε W p j) :
    cfzp019PrimePowerEventPositiveMass ε W p j =
      cfzpPrimePowerBranchFreeTrigEvent ε W p j := by
  simp [cfzp019PrimePowerEventPositiveMass, max_eq_left he]

theorem cfzp019PrimePowerEventNegativeDebt_eq_zero_of_nonneg
    {ε : ℝ} (W : PascalCenteredXiResidueTransportWindow) (p j : ℕ)
    (he : 0 ≤ cfzpPrimePowerBranchFreeTrigEvent ε W p j) :
    cfzp019PrimePowerEventNegativeDebt ε W p j = 0 := by
  simp [cfzp019PrimePowerEventNegativeDebt, max_eq_right (neg_nonpos.mpr he)]

theorem cfzp019PrimePowerEventPositiveMass_eq_zero_of_nonpos
    {ε : ℝ} (W : PascalCenteredXiResidueTransportWindow) (p j : ℕ)
    (he : cfzpPrimePowerBranchFreeTrigEvent ε W p j ≤ 0) :
    cfzp019PrimePowerEventPositiveMass ε W p j = 0 := by
  simp [cfzp019PrimePowerEventPositiveMass, max_eq_right he]

theorem cfzp019PrimePowerEventNegativeDebt_eq_neg_of_nonpos
    {ε : ℝ} (W : PascalCenteredXiResidueTransportWindow) (p j : ℕ)
    (he : cfzpPrimePowerBranchFreeTrigEvent ε W p j ≤ 0) :
    cfzp019PrimePowerEventNegativeDebt ε W p j =
      -cfzpPrimePowerBranchFreeTrigEvent ε W p j := by
  simp [cfzp019PrimePowerEventNegativeDebt,
    max_eq_left (neg_nonneg.mpr he)]

theorem cfzp019PrimePowerEventNegativeDebt_eq_zero_of_nonposPhaseCellCoverage
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {p j : ℕ} (hp : Nat.Prime p) (hj : 0 < j)
    (hA : ∀ θ ∈ Set.Ioo
        (cfzpPrimePowerPhaseAngleLeft ε W p j)
        (cfzpPrimePowerPhaseAngleRight ε W p j),
      0 ≤ cfzpPhaseDerivativeSinCoeff (cfzpModePhaseAspectRatio W) θ)
    (hcoverage : ∀ θ ∈ Set.Ioo
        (cfzpPrimePowerPhaseAngleLeft ε W p j)
        (cfzpPrimePowerPhaseAngleRight ε W p j),
      cfzpPhaseCellSinNonposCosNonpos θ) :
    cfzp019PrimePowerEventNegativeDebt ε W p j = 0 := by
  apply cfzp019PrimePowerEventNegativeDebt_eq_zero_of_nonneg W p j
  exact cfzpPrimePowerBranchFreeTrigEvent_nonneg_of_nonposPhaseCellCoverage
    hε hε2 W hp hj hA hcoverage

theorem cfzp019PrimePowerEventPositiveMass_eq_of_nonposPhaseCellCoverage
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {p j : ℕ} (hp : Nat.Prime p) (hj : 0 < j)
    (hA : ∀ θ ∈ Set.Ioo
        (cfzpPrimePowerPhaseAngleLeft ε W p j)
        (cfzpPrimePowerPhaseAngleRight ε W p j),
      0 ≤ cfzpPhaseDerivativeSinCoeff (cfzpModePhaseAspectRatio W) θ)
    (hcoverage : ∀ θ ∈ Set.Ioo
        (cfzpPrimePowerPhaseAngleLeft ε W p j)
        (cfzpPrimePowerPhaseAngleRight ε W p j),
      cfzpPhaseCellSinNonposCosNonpos θ) :
    cfzp019PrimePowerEventPositiveMass ε W p j =
      cfzpPrimePowerBranchFreeTrigEvent ε W p j := by
  apply cfzp019PrimePowerEventPositiveMass_eq_of_nonneg W p j
  exact cfzpPrimePowerBranchFreeTrigEvent_nonneg_of_nonposPhaseCellCoverage
    hε hε2 W hp hj hA hcoverage

theorem cfzp019PrimePowerEventPositiveMass_eq_zero_of_nonnegPhaseCellCoverage
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {p j : ℕ} (hp : Nat.Prime p) (hj : 0 < j)
    (hA : ∀ θ ∈ Set.Ioo
        (cfzpPrimePowerPhaseAngleLeft ε W p j)
        (cfzpPrimePowerPhaseAngleRight ε W p j),
      cfzpPhaseDerivativeSinCoeff (cfzpModePhaseAspectRatio W) θ ≤ 0)
    (hcoverage : ∀ θ ∈ Set.Ioo
        (cfzpPrimePowerPhaseAngleLeft ε W p j)
        (cfzpPrimePowerPhaseAngleRight ε W p j),
      cfzpPhaseCellSinNonposCosNonneg θ) :
    cfzp019PrimePowerEventPositiveMass ε W p j = 0 := by
  apply cfzp019PrimePowerEventPositiveMass_eq_zero_of_nonpos W p j
  exact cfzpPrimePowerBranchFreeTrigEvent_nonpos_of_nonnegPhaseCellCoverage
    hε hε2 W hp hj hA hcoverage

theorem cfzp019PrimePowerEventNegativeDebt_eq_neg_of_nonnegPhaseCellCoverage
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {p j : ℕ} (hp : Nat.Prime p) (hj : 0 < j)
    (hA : ∀ θ ∈ Set.Ioo
        (cfzpPrimePowerPhaseAngleLeft ε W p j)
        (cfzpPrimePowerPhaseAngleRight ε W p j),
      cfzpPhaseDerivativeSinCoeff (cfzpModePhaseAspectRatio W) θ ≤ 0)
    (hcoverage : ∀ θ ∈ Set.Ioo
        (cfzpPrimePowerPhaseAngleLeft ε W p j)
        (cfzpPrimePowerPhaseAngleRight ε W p j),
      cfzpPhaseCellSinNonposCosNonneg θ) :
    cfzp019PrimePowerEventNegativeDebt ε W p j =
      -cfzpPrimePowerBranchFreeTrigEvent ε W p j := by
  apply cfzp019PrimePowerEventNegativeDebt_eq_neg_of_nonpos W p j
  exact cfzpPrimePowerBranchFreeTrigEvent_nonpos_of_nonnegPhaseCellCoverage
    hε hε2 W hp hj hA hcoverage

/-! ## Gate C: finite signed ledgers -/

/-- The finite positive event mass over the existing canonical support. -/
noncomputable def cfzp019BranchFreePositiveEventMass
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) : ℝ :=
  ∑ pk ∈ pascalPrimePowerPairSupportUpTo X,
    cfzp019PrimePowerEventPositiveMass ε W pk.1 (pk.2 + 1)

/-- The finite negative event debt over the existing canonical support. -/
noncomputable def cfzp019BranchFreeNegativeEventDebt
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) : ℝ :=
  ∑ pk ∈ pascalPrimePowerPairSupportUpTo X,
    cfzp019PrimePowerEventNegativeDebt ε W pk.1 (pk.2 + 1)

theorem cfzp019BranchFreePositiveEventMass_nonneg
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    0 ≤ cfzp019BranchFreePositiveEventMass ε W X := by
  unfold cfzp019BranchFreePositiveEventMass
  exact Finset.sum_nonneg fun pk hpk =>
    cfzp019PrimePowerEventPositiveMass_nonneg ε W pk.1 (pk.2 + 1)

theorem cfzp019BranchFreeNegativeEventDebt_nonneg
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    0 ≤ cfzp019BranchFreeNegativeEventDebt ε W X := by
  unfold cfzp019BranchFreeNegativeEventDebt
  exact Finset.sum_nonneg fun pk hpk =>
    cfzp019PrimePowerEventNegativeDebt_nonneg ε W pk.1 (pk.2 + 1)

theorem cfzp019BranchFreeTrigLedger_eq_positiveMass_sub_negativeDebt
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    cfzpPrimePowerBranchFreeTrigLedger ε W X =
      cfzp019BranchFreePositiveEventMass ε W X -
        cfzp019BranchFreeNegativeEventDebt ε W X := by
  unfold cfzpPrimePowerBranchFreeTrigLedger
    cfzp019BranchFreePositiveEventMass cfzp019BranchFreeNegativeEventDebt
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro pk hpk
  exact cfzp019PrimePowerEvent_eq_positiveMass_sub_negativeDebt
    ε W pk.1 (pk.2 + 1)

/-! ## Gate D/E: radial balance and finite slack -/

/-- In the safe-frequency regime, the radial deficit is baseline plus debt
minus positive event mass. -/
theorem cfzp019RadialContactDeficit_eq_baseline_add_debt_sub_positiveMass
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W X =
      cfzpZeroCutoffRadialContactBaseline ε W +
        cfzp019BranchFreeNegativeEventDebt ε W X -
        cfzp019BranchFreePositiveEventMass ε W X := by
  rw [cfzpRadialContactDeficit_eq_zeroCutoffBaseline_sub_branchFreeTrigLedger
    hε hε2 W X, cfzp019BranchFreeTrigLedger_eq_positiveMass_sub_negativeDebt]
  ring

/-- Finite radial contact up to geometric slack is exactly the signed-mass
budget inequality. -/
theorem cfzp019RadialContactDeficit_le_iff_signedMassBudget
    {ε η : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W X ≤ η ↔
      cfzpZeroCutoffRadialContactBaseline ε W +
          cfzp019BranchFreeNegativeEventDebt ε W X ≤
        cfzp019BranchFreePositiveEventMass ε W X + η := by
  rw [cfzp019RadialContactDeficit_eq_baseline_add_debt_sub_positiveMass
    hε hε2 W X]
  constructor <;> intro h <;> linarith

/-! ## Gate F/G: fixed-epsilon cofinal budget -/

/-- The signed-mass budget at fixed epsilon, with geometric slack `η`. -/
def Cfzp019CofinalBranchFreeSignedMassBudgetAt
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) : Prop :=
  ∀ η : ℝ, 0 < η → ∀ N : ℕ, ∃ X : ℕ, N ≤ X ∧
    cfzpZeroCutoffRadialContactBaseline ε W +
        cfzp019BranchFreeNegativeEventDebt ε W X ≤
      cfzp019BranchFreePositiveEventMass ε W X + η

theorem cfzp019CofinalBranchFreeSignedMassBudgetAt_iff_contactZero
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow) :
    Cfzp019CofinalBranchFreeSignedMassBudgetAt ε W ↔
      PascalCenteredXiPrimeSideCofinalRadialContactZeroAt ε W := by
  unfold Cfzp019CofinalBranchFreeSignedMassBudgetAt
    PascalCenteredXiPrimeSideCofinalRadialContactZeroAt
    PascalCenteredXiPrimeSideCofinalRadialContactAt
  constructor
  · intro h η hη N
    rcases h η hη N with ⟨X, hNX, hbudget⟩
    refine ⟨X, hNX, ?_⟩
    have hdef := cfzp019RadialContactDeficit_le_iff_signedMassBudget
      (η := η) hε hε2 W X
    simpa using hdef.mpr hbudget
  · intro h η hη N
    rcases h η hη N with ⟨X, hNX, hcontact⟩
    refine ⟨X, hNX, ?_⟩
    apply (cfzp019RadialContactDeficit_le_iff_signedMassBudget
      hε hε2 W X).mp
    simpa using hcontact

theorem cfzp019CofinalBranchFreeSignedMassBudgetAt_iff_cfzp018
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow) :
    Cfzp019CofinalBranchFreeSignedMassBudgetAt ε W ↔
      Cfzp018CofinalPrimeThresholdApproximateReachAt ε W := by
  rw [cfzp019CofinalBranchFreeSignedMassBudgetAt_iff_contactZero hε hε2 W,
    cfzp018CofinalPrimeThresholdApproximateReachAt_iff_csf hε W]

/-! ## Gate H: aggregate sign firewall -/

/-- If every witnessed finite event is nonnegative, no negative debt remains.
This is only a finite sign adapter and does not provide magnitude reach. -/
theorem cfzp019NegativeEventDebt_eq_zero_of_all_events_nonneg
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ)
    (hall : ∀ pk ∈ pascalPrimePowerPairSupportUpTo X,
      0 ≤ cfzpPrimePowerBranchFreeTrigEvent ε W pk.1 (pk.2 + 1)) :
    cfzp019BranchFreeNegativeEventDebt ε W X = 0 := by
  unfold cfzp019BranchFreeNegativeEventDebt
  apply Finset.sum_eq_zero
  intro pk hpk
  simp [cfzp019PrimePowerEventNegativeDebt,
    max_eq_right (neg_nonpos.mpr (hall pk hpk))]

theorem cfzp019PositiveEventMass_eq_ledger_of_all_events_nonneg
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ)
    (hall : ∀ pk ∈ pascalPrimePowerPairSupportUpTo X,
      0 ≤ cfzpPrimePowerBranchFreeTrigEvent ε W pk.1 (pk.2 + 1)) :
    cfzp019BranchFreePositiveEventMass ε W X =
      cfzpPrimePowerBranchFreeTrigLedger ε W X := by
  rw [cfzp019BranchFreeTrigLedger_eq_positiveMass_sub_negativeDebt,
    cfzp019NegativeEventDebt_eq_zero_of_all_events_nonneg ε W X hall]
  ring

/-- A nonnegative mass alone does not pay an arbitrary fixed baseline.  This
is a real-number firewall, not a counterexample to the zeta event ledger. -/
theorem cfzp019NonnegMass_does_not_imply_baselineBudget :
    ∃ baseline mass η : ℝ, 0 ≤ mass ∧ 0 < η ∧ ¬ baseline ≤ mass + η := by
  refine ⟨2, 0, 1, by norm_num, by norm_num, ?_⟩
  norm_num

/-! ## Gate I/J: safe outer frequency and doubly-cofinal budget -/

theorem eventually_epsilon_lt_log_two :
    ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < Real.log 2 := by
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog_nhds : ∀ᶠ ε : ℝ in 𝓝 (0 : ℝ), ε < Real.log 2 :=
    Iio_mem_nhds hlog
  exact hlog_nhds.filter_mono nhdsWithin_le_nhds

/-- The safe-frequency restriction is eventually true at the outer positive
epsilon boundary. -/
def Cfzp019DoublyCofinalSafeBranchFreeSignedMassBudget
    (W : PascalCenteredXiResidueTransportWindow) : Prop :=
  ∃ᶠ ε : ℝ in 𝓝[>] 0,
    0 < ε ∧ ε < Real.log 2 ∧
      Cfzp019CofinalBranchFreeSignedMassBudgetAt ε W

theorem cfzp019DoublyCofinalSafeBranchFreeSignedMassBudget_iff_cfzp018
    (W : PascalCenteredXiResidueTransportWindow) :
    Cfzp019DoublyCofinalSafeBranchFreeSignedMassBudget W ↔
      Cfzp018DoublyCofinalPrimeThresholdApproximateReach W := by
  constructor
  · intro h
    exact h.mono fun ε hε =>
      ⟨hε.1, (cfzp019CofinalBranchFreeSignedMassBudgetAt_iff_cfzp018
        hε.1 hε.2.1 W).mp hε.2.2⟩
  · intro h
    exact (h.and_eventually eventually_epsilon_lt_log_two).mono fun ε hε =>
      ⟨hε.1.1, hε.2,
        (cfzp019CofinalBranchFreeSignedMassBudgetAt_iff_cfzp018
          hε.1.1 hε.2 W).mpr hε.1.2⟩

/-- The signed-mass budget is a conditional adapter to the existing finite
window criticality theorem. -/
theorem cfzp019FiniteWindowZeros_critical_of_doublyCofinalSafeSignedMassBudget
    (W : PascalCenteredXiResidueTransportWindow)
    (hbudget : Cfzp019DoublyCofinalSafeBranchFreeSignedMassBudget W) :
    ∀ ρ ∈ pascalCriticalMirrorZeroWindowFinset W.R,
      ρ.re = (1 : ℝ) / 2 := by
  apply cfzp018FiniteWindowZeros_critical_of_doublyCofinalPrimeThresholdApproximateReach
    W
  exact (cfzp019DoublyCofinalSafeBranchFreeSignedMassBudget_iff_cfzp018 W).mp
    hbudget

/-! ## Gate L: explicit unresolved provider -/

/-- An independent doubly-cofinal signed-mass budget provider remains open. -/
inductive Cfzp019BranchFreeSignedMassBudgetGap : Prop
  | noIndependentDoublyCofinalSignedMassBudgetProvider

end DkMath.RH.CFBRCProjection
