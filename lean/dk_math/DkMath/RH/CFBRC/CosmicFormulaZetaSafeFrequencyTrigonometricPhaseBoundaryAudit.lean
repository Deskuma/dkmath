/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.CosmicFormulaZetaPrimePowerClosedPhaseContactLedgerAudit
import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideInteractionPhaseBoundaryAudit
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CosmicFormulaZetaSafeFrequencyTrigonometricPhaseBoundaryAudit"

/-!
# CFZP-006V: safe-frequency branch-free trigonometric phase boundary

On the finite safe-frequency regime `0 < ε < log 2`, every witnessed
prime-power event has two nonzero real phase frequencies.  The closed phase
ledger can therefore be written with a branch-free real `exp/cos/sin`
boundary value.  No sign, ordering, monotonicity, reach, convergence,
zeta-zero, or RH conclusion is supplied here.
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

/-! ## A. Branch-free nonzero-frequency primitive boundary -/

noncomputable def cfzpPhasePrimitiveNonzeroBoundary
    (a r T : ℝ) : ℝ :=
  Real.exp (a * r) *
    (T * Real.cos (r * T) / r +
      (a * r - 1) * Real.sin (r * T) / r ^ 2)

theorem cfzpPhasePrimitive_eq_nonzeroBoundary
    {a r T : ℝ} (hr : r ≠ 0) :
    pascalCenteredXiPrimeSidePhasePrimitive a r T =
      cfzpPhasePrimitiveNonzeroBoundary a r T := by
  simpa [cfzpPhasePrimitiveNonzeroBoundary] using
    (pascalCenteredXiPrimeSidePhasePrimitive_nonzero_frequency hr)

/-! ## B. Prime-power safe-frequency certificate -/

theorem cfzpPrimePowerPhaseFrequencies_nonzero_of_epsilon_lt_log_two
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    {p j : ℕ} (hp : Nat.Prime p) (hj : 0 < j) :
    cfzpModePhaseFrequencyPlus ε (p ^ j) ≠ 0 ∧
      cfzpModePhaseFrequencyMinus ε (p ^ j) ≠ 0 := by
  have hp2 : 2 ≤ p := hp.two_le
  have hp_pow : p ≤ p ^ j := Nat.le_pow (Nat.pos_of_ne_zero hj.ne')
  have hpow : 2 ≤ p ^ j := le_trans hp2 hp_pow
  have hsafe := pascalCenteredXiPrimeSide_phase_frequencies_safe_cutoff
    hε hε2 hpow
  simpa [cfzpModePhaseFrequencyPlus, cfzpModePhaseFrequencyMinus,
    pascalCenteredXiPrimeSidePhaseFrequencyPlus,
    pascalCenteredXiPrimeSidePhaseFrequencyMinus] using hsafe.2

theorem cfzpPrimePowerPhaseFrequencies_negative_of_epsilon_lt_log_two
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    {p j : ℕ} (hp : Nat.Prime p) (hj : 0 < j) :
    cfzpModePhaseFrequencyPlus ε (p ^ j) < 0 ∧
      cfzpModePhaseFrequencyMinus ε (p ^ j) < 0 := by
  have hp2 : 2 ≤ p := hp.two_le
  have hp_pow : p ≤ p ^ j := Nat.le_pow (Nat.pos_of_ne_zero hj.ne')
  have hpow : 2 ≤ p ^ j := le_trans hp2 hp_pow
  have hsafe := pascalCenteredXiPrimeSide_phase_frequencies_safe_cutoff
    hε hε2 hpow
  have hpowlog : ε < (j : ℝ) * Real.log (p : ℝ) := by
    simpa [Nat.cast_pow, Real.log_pow] using hsafe.1
  have hplus := cfzpModePhaseFrequencyPlus_eq_of_eq_prime_pow
    (ε := ε) hp hj
  have hminus := cfzpModePhaseFrequencyMinus_eq_of_eq_prime_pow
    (ε := ε) hp hj
  constructor
  · rw [hplus]
    linarith
  · rw [hminus]
    linarith

/-! ## C. One-event branch-free trigonometric formula -/

noncomputable def cfzpPrimePowerBranchFreeTrigEvent
    (ε : ℝ)
    (W : PascalCenteredXiResidueTransportWindow)
    (p j : ℕ) : ℝ :=
  2 * Real.log (p : ℝ) *
    ((2 * ε)⁻¹ * cfzpModeCriticalScale (p ^ j) *
      (cfzpPhasePrimitiveNonzeroBoundary
        (cfzpModePhaseAbscissa W)
        (ε - (j : ℝ) * Real.log (p : ℝ))
        W.rectangle.T -
       cfzpPhasePrimitiveNonzeroBoundary
        (cfzpModePhaseAbscissa W)
        (-ε - (j : ℝ) * Real.log (p : ℝ))
        W.rectangle.T))

theorem cfzpPrimePowerClosedPhaseEvent_eq_branchFreeTrigBoundaryDifference
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {p j : ℕ} (hp : Nat.Prime p) (hj : 0 < j) :
    cfzpPrimePowerClosedPhaseEvent ε W p j =
      cfzpPrimePowerBranchFreeTrigEvent ε W p j := by
  have hfreq := cfzpPrimePowerPhaseFrequencies_nonzero_of_epsilon_lt_log_two
    hε hε2 hp hj
  have hplus := cfzpModePhaseFrequencyPlus_eq_of_eq_prime_pow
    (ε := ε) hp hj
  have hminus := cfzpModePhaseFrequencyMinus_eq_of_eq_prime_pow
    (ε := ε) hp hj
  have hplus' : ε - (j : ℝ) * Real.log (p : ℝ) ≠ 0 := by
    rw [← hplus]
    exact hfreq.1
  have hminus' : -ε - (j : ℝ) * Real.log (p : ℝ) ≠ 0 := by
    rw [← hminus]
    exact hfreq.2
  unfold cfzpPrimePowerClosedPhaseEvent cfzpPrimePowerBranchFreeTrigEvent
  simp [pascalCenteredXiPrimeSidePhasePrimitiveClosedForm,
    cfzpPhasePrimitiveNonzeroBoundary,
    hplus', hminus']

/-! ## D. Pair-support branch-free ledger -/

noncomputable def cfzpPrimePowerBranchFreeTrigLedger
    (ε : ℝ)
    (W : PascalCenteredXiResidueTransportWindow)
    (X : ℕ) : ℝ :=
  ∑ pk ∈ pascalPrimePowerPairSupportUpTo X,
    cfzpPrimePowerBranchFreeTrigEvent ε W pk.1 (pk.2 + 1)

theorem cfzpPrimePowerClosedPhaseLedger_eq_branchFreeTrigLedger
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    cfzpPrimePowerClosedPhaseLedger ε W X =
      cfzpPrimePowerBranchFreeTrigLedger ε W X := by
  unfold cfzpPrimePowerClosedPhaseLedger cfzpPrimePowerBranchFreeTrigLedger
  apply Finset.sum_congr rfl
  intro pk hpk
  have hsupport := mem_pascalPrimePowerPairSupportUpTo_iff.mp hpk
  have hp := (mem_pascalPrimeCoordinateSupportUpTo_iff.mp hsupport.1).1
  have hj : 0 < pk.2 + 1 := by omega
  exact cfzpPrimePowerClosedPhaseEvent_eq_branchFreeTrigBoundaryDifference
    hε hε2 W hp hj

/-! ## E. Aggregate, residual, and deficit branch-free identities -/

theorem cfzpAggregateRayInteractionEnergy_eq_branchFreeTrigLedger
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W X =
      cfzpPrimePowerBranchFreeTrigLedger ε W X := by
  calc
    pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W X =
        cfzpPrimePowerClosedPhaseLedger ε W X :=
      cfzpAggregateRayInteractionEnergy_eq_primePowerClosedPhaseLedger hε W X
    _ = cfzpPrimePowerBranchFreeTrigLedger ε W X :=
      cfzpPrimePowerClosedPhaseLedger_eq_branchFreeTrigLedger hε hε2 W X

theorem cfzpRadialBudgetResidual_eq_zeroCutoffBaseline_sub_branchFreeTrigLedger
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    cfzpRadialBudgetResidual ε W X =
      cfzpZeroCutoffRadialContactBaseline ε W -
        cfzpPrimePowerBranchFreeTrigLedger ε W X := by
  have hres :=
    cfzpRadialBudgetResidual_eq_zeroCutoffBaseline_sub_primePowerClosedPhaseLedger
      hε W X
  rw [hres, cfzpPrimePowerClosedPhaseLedger_eq_branchFreeTrigLedger hε hε2 W X]

theorem cfzpRadialContactDeficit_eq_zeroCutoffBaseline_sub_branchFreeTrigLedger
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W X =
      cfzpZeroCutoffRadialContactBaseline ε W -
        cfzpPrimePowerBranchFreeTrigLedger ε W X := by
  have hdef :=
    cfzpRadialContactDeficit_eq_zeroCutoffBaseline_sub_primePowerClosedPhaseLedger
      hε W X
  rw [hdef, cfzpPrimePowerClosedPhaseLedger_eq_branchFreeTrigLedger hε hε2 W X]

/-! ## F. Explicit branch-free balance and order classification -/

theorem cfzpRadialBudgetResidual_eq_zero_iff_branchFreeTrigLedger_reaches_baseline
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    cfzpRadialBudgetResidual ε W X = 0 ↔
      cfzpPrimePowerBranchFreeTrigLedger ε W X =
        cfzpZeroCutoffRadialContactBaseline ε W := by
  rw [cfzpRadialBudgetResidual_eq_zeroCutoffBaseline_sub_branchFreeTrigLedger
    hε hε2 W X]
  constructor <;> intro h <;> linarith

theorem cfzpRadialContactDeficit_eq_zero_iff_branchFreeTrigLedger_reaches_baseline
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W X = 0 ↔
      cfzpPrimePowerBranchFreeTrigLedger ε W X =
        cfzpZeroCutoffRadialContactBaseline ε W := by
  rw [cfzpRadialContactDeficit_eq_zeroCutoffBaseline_sub_branchFreeTrigLedger
    hε hε2 W X]
  constructor <;> intro h <;> linarith

theorem cfzpRadialBudgetResidual_nonneg_iff_branchFreeTrigLedger_le_baseline
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    0 ≤ cfzpRadialBudgetResidual ε W X ↔
      cfzpPrimePowerBranchFreeTrigLedger ε W X ≤
        cfzpZeroCutoffRadialContactBaseline ε W := by
  rw [cfzpRadialBudgetResidual_eq_zeroCutoffBaseline_sub_branchFreeTrigLedger
    hε hε2 W X]
  constructor <;> intro h <;> linarith

theorem cfzpRadialBudgetResidual_nonpos_iff_baseline_le_branchFreeTrigLedger
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    cfzpRadialBudgetResidual ε W X ≤ 0 ↔
      cfzpZeroCutoffRadialContactBaseline ε W ≤
        cfzpPrimePowerBranchFreeTrigLedger ε W X := by
  rw [cfzpRadialBudgetResidual_eq_zeroCutoffBaseline_sub_branchFreeTrigLedger
    hε hε2 W X]
  constructor <;> intro h <;> linarith

inductive CfzpBranchFreeTrigBoundaryOrderingGap : Prop
  | noIndependentPrimePowerBranchFreeBoundaryOrderingProvider

end DkMath.RH.CFBRCProjection
