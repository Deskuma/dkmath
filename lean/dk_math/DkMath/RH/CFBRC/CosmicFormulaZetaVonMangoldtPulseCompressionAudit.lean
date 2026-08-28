/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.RH.CFBRC.CosmicFormulaZetaSignedMassCutoffFrontierIncrementAudit
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CosmicFormulaZetaVonMangoldtPulseCompressionAudit"

/-!
# CFZP-021: von Mangoldt pulse compression

The existing finite interaction cutoff increment is named here as a
von-Mangoldt-weighted mode pulse.  This compresses the CFZP-020 pair-support
frontier increment to the single natural-number mode `X + 1`.  The pulse is
signed: its von Mangoldt coefficient is nonnegative, but the finite mode
kernel is not assigned a sign.

The module proves finite successor identities, non-prime-power quiescence,
prime-power event identification, and conditional phase-cell sign adapters.
It introduces no sign provider, block-dominance provider, infinite sum, or RH
statement.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.Analysis
open DkMath.NumberTheory
open DkMath.NumberTheory.PrimitiveSet
open Set

/-! ## Gate A/B: one-mode pulse and aggregate successor law -/

/-- The signed von-Mangoldt pulse carried by one natural-number mode. -/
noncomputable def cfzp021VonMangoldtPulse
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (n : ℕ) : ℝ :=
  2 * (ArithmeticFunction.vonMangoldt n : ℝ) *
    pascalCenteredXiPrimeSideFiniteModeKernel ε W n

theorem cfzp021VonMangoldtPulse_eq_interactionCutoffIncrement
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (n : ℕ) :
    cfzp021VonMangoldtPulse ε W n =
      cfzpPrimeSideInteractionCutoffIncrement ε W n := by
  rfl

/-- The aggregate interaction changes by exactly one von-Mangoldt pulse. -/
theorem cfzp021AggregateRayInteractionEnergy_succ_eq_add_pulse
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W (X + 1) =
      pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W X +
        cfzp021VonMangoldtPulse ε W (X + 1) := by
  rw [cfzp021VonMangoldtPulse_eq_interactionCutoffIncrement]
  exact cfzpAggregateRayInteractionEnergy_succ hε W X

/-! ## Gate C: branch-free ledger and frontier compression -/

/-- In the safe-frequency regime, the branch-free ledger increment is the
same single pulse as the aggregate interaction increment. -/
theorem cfzp021BranchFreeTrigLedger_succ_eq_add_pulse
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    cfzpPrimePowerBranchFreeTrigLedger ε W (X + 1) =
      cfzpPrimePowerBranchFreeTrigLedger ε W X +
        cfzp021VonMangoldtPulse ε W (X + 1) := by
  have hnext := cfzpAggregateRayInteractionEnergy_eq_branchFreeTrigLedger
    hε hε2 W (X + 1)
  have hcurrent := cfzpAggregateRayInteractionEnergy_eq_branchFreeTrigLedger
    hε hε2 W X
  have hagg := cfzp021AggregateRayInteractionEnergy_succ_eq_add_pulse hε W X
  rw [← hnext, ← hcurrent, hagg]

theorem cfzp021BranchFreeTrigLedger_sub_eq_pulse
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    cfzpPrimePowerBranchFreeTrigLedger ε W (X + 1) -
        cfzpPrimePowerBranchFreeTrigLedger ε W X =
      cfzp021VonMangoldtPulse ε W (X + 1) := by
  have h := cfzp021BranchFreeTrigLedger_succ_eq_add_pulse hε hε2 W X
  linarith

/-- The CFZP-020 frontier net flow is the same natural-number pulse. -/
theorem cfzp021FrontierPositiveMass_sub_frontierNegativeDebt_eq_pulse
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    cfzp020FrontierPositiveEventMass ε W X -
        cfzp020FrontierNegativeEventDebt ε W X =
      cfzp021VonMangoldtPulse ε W (X + 1) := by
  have hfront := cfzp020BranchFreeTrigLedger_sub_eq_frontierMass_sub_frontierDebt
    ε W X
  have hpulse := cfzp021BranchFreeTrigLedger_sub_eq_pulse hε hε2 W X
  linarith

/-! ## Gate D/E: radial pulse recurrence and sign adapters -/

/-- The safe-frequency radial contact deficit is decreased by a positive
pulse and increased by a negative pulse. -/
theorem cfzp021RadialContactDeficit_succ_eq_sub_pulse
    {ε : ℝ} (hε : 0 < ε) (_hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W (X + 1) =
      pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W X -
        cfzp021VonMangoldtPulse ε W (X + 1) := by
  rw [cfzp021VonMangoldtPulse_eq_interactionCutoffIncrement]
  exact cfzpRadialContactDeficit_succ hε W X

theorem cfzp021RadialContactDeficit_succ_le_of_pulse_nonneg
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ)
    (hpulse : 0 ≤ cfzp021VonMangoldtPulse ε W (X + 1)) :
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W (X + 1) ≤
      pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W X := by
  rw [cfzp021RadialContactDeficit_succ_eq_sub_pulse hε hε2 W X]
  linarith

theorem cfzp021RadialContactDeficit_le_succ_of_pulse_nonpos
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ)
    (hpulse : cfzp021VonMangoldtPulse ε W (X + 1) ≤ 0) :
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W X ≤
      pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W (X + 1) := by
  rw [cfzp021RadialContactDeficit_succ_eq_sub_pulse hε hε2 W X]
  linarith

theorem cfzp021RadialContactDeficit_succ_eq_of_pulse_zero
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ)
    (hpulse : cfzp021VonMangoldtPulse ε W (X + 1) = 0) :
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W (X + 1) =
      pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W X := by
  rw [cfzp021RadialContactDeficit_succ_eq_sub_pulse hε hε2 W X,
    hpulse, sub_zero]

/-! ## Gate F: non-prime-power quiescence -/

theorem cfzp021VonMangoldtPulse_eq_zero_of_not_isPrimePow
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (n : ℕ)
    (hNP : ¬ IsPrimePow n) :
    cfzp021VonMangoldtPulse ε W n = 0 := by
  apply cfzpPrimeSideInteractionCutoffIncrement_eq_zero_of_vonMangoldt_eq_zero
    ε W n
  exact ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hNP

theorem cfzp021AggregateRayInteractionEnergy_succ_eq_of_not_isPrimePow
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ)
    (hNP : ¬ IsPrimePow (X + 1)) :
    pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W (X + 1) =
      pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W X := by
  have h := cfzp021AggregateRayInteractionEnergy_succ_eq_add_pulse hε W X
  have hpulse := cfzp021VonMangoldtPulse_eq_zero_of_not_isPrimePow
    ε W (X + 1) hNP
  rw [hpulse, add_zero] at h
  exact h

theorem cfzp021BranchFreeTrigLedger_succ_eq_of_not_isPrimePow
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ)
    (hNP : ¬ IsPrimePow (X + 1)) :
    cfzpPrimePowerBranchFreeTrigLedger ε W (X + 1) =
      cfzpPrimePowerBranchFreeTrigLedger ε W X := by
  have h := cfzp021BranchFreeTrigLedger_succ_eq_add_pulse hε hε2 W X
  have hpulse := cfzp021VonMangoldtPulse_eq_zero_of_not_isPrimePow
    ε W (X + 1) hNP
  rw [hpulse, add_zero] at h
  exact h

theorem cfzp021RadialContactDeficit_succ_eq_of_not_isPrimePow
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ)
    (hNP : ¬ IsPrimePow (X + 1)) :
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W (X + 1) =
      pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W X := by
  have h := cfzpRadialContactDeficit_succ hε W X
  have hpulse := cfzp021VonMangoldtPulse_eq_zero_of_not_isPrimePow
    ε W (X + 1) hNP
  rw [cfzp021VonMangoldtPulse_eq_interactionCutoffIncrement] at hpulse
  rw [hpulse, sub_zero] at h
  exact h

/-! ## Gate G: prime-power event identification -/

theorem cfzp021VonMangoldtPulse_eq_two_log_mul_modeKernel_of_eq_prime_pow
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    {p j n : ℕ} (hp : Nat.Prime p) (hj : 0 < j) (hn : n = p ^ j) :
    cfzp021VonMangoldtPulse ε W n =
      2 * Real.log (p : ℝ) *
        pascalCenteredXiPrimeSideFiniteModeKernel ε W n := by
  rw [cfzp021VonMangoldtPulse_eq_interactionCutoffIncrement]
  exact cfzpPrimeSideInteractionCutoffIncrement_eq_two_log_mul_modeKernel_of_eq_prime_pow
    ε W hp hj hn

theorem cfzp021VonMangoldtPulse_eq_branchFreeTrigEvent_of_eq_prime_pow
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {p j n : ℕ} (hp : Nat.Prime p) (hj : 0 < j) (hn : n = p ^ j) :
    cfzp021VonMangoldtPulse ε W n =
      cfzpPrimePowerBranchFreeTrigEvent ε W p j := by
  rw [hn, cfzp021VonMangoldtPulse_eq_interactionCutoffIncrement,
    ← cfzpPrimePowerClosedPhaseEvent_eq_interactionIncrement hε W hp hj,
    cfzpPrimePowerClosedPhaseEvent_eq_branchFreeTrigBoundaryDifference
      hε hε2 W hp hj]

/-! ## Gate H: exact frontier labels -/

/-- Every pair in the cutoff frontier represents exactly the newly reached
natural-number label `X + 1`. -/
theorem cfzp020PrimePowerCutoffFrontier_label_eq_succ
    {X : ℕ} {pk : ℕ × ℕ}
    (hpk : pk ∈ cfzp020PrimePowerCutoffFrontier X) :
    primePowerPairLabel pk = X + 1 := by
  have hsucc := cfzp020PrimePowerCutoffFrontier_subset_succ X hpk
  have hsucc' := mem_pascalPrimePowerPairSupportUpTo_iff.mp hsucc
  have hp := (mem_pascalPrimeCoordinateSupportUpTo_iff.mp hsucc'.1).1
  have hlabel_pp : IsPrimePowerLabel (primePowerPairLabel pk) :=
    ⟨pk.1, pk.2 + 1, hp, by omega, rfl⟩
  have hle : primePowerPairLabel pk ≤ X + 1 := hsucc'.2.2
  have hnot : pk ∉ pascalPrimePowerPairSupportUpTo X := by
    exact (Finset.mem_sdiff.mp hpk).2
  by_contra hneq
  have hleX : primePowerPairLabel pk ≤ X := by omega
  have hcanon : primePowerPairLabel pk ∈ canonicalPrimePowerSupportUpTo X :=
    mem_canonicalPrimePowerSupportUpTo_iff.mpr ⟨hleX, hlabel_pp⟩
  have hcanon_image : primePowerPairLabel pk ∈
      (pascalPrimePowerPairSupportUpTo X).image primePowerPairLabel := by
    rw [image_primePowerPairLabel_support_eq_canonicalSupport X]
    exact hcanon
  rcases Finset.mem_image.mp hcanon_image with ⟨q, hq, hlabel⟩
  have hqsucc : q ∈ pascalPrimePowerPairSupportUpTo (X + 1) :=
    cfzp020PrimePowerPairSupportUpTo_mono (Nat.le_add_right X 1) hq
  have heq : primePowerPairLabel pk = primePowerPairLabel q := hlabel.symm
  have : pk = q := primePowerPairLabel_injOn (X + 1) hsucc hqsucc heq
  exact hnot (this ▸ hq)

/-! ## Gate I: phase-cell signs compressed to pulse signs -/

theorem cfzp021VonMangoldtPulse_nonneg_of_nonposPhaseCellCoverage
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {X p j : ℕ} (hp : Nat.Prime p) (hj : 0 < j)
    (hstep : X + 1 = p ^ j)
    (hA : ∀ θ ∈ Set.Ioo
        (cfzpPrimePowerPhaseAngleLeft ε W p j)
        (cfzpPrimePowerPhaseAngleRight ε W p j),
      0 ≤ cfzpPhaseDerivativeSinCoeff (cfzpModePhaseAspectRatio W) θ)
    (hcoverage : ∀ θ ∈ Set.Ioo
        (cfzpPrimePowerPhaseAngleLeft ε W p j)
        (cfzpPrimePowerPhaseAngleRight ε W p j),
      cfzpPhaseCellSinNonposCosNonpos θ) :
    0 ≤ cfzp021VonMangoldtPulse ε W (X + 1) := by
  rw [hstep, cfzp021VonMangoldtPulse_eq_branchFreeTrigEvent_of_eq_prime_pow
    hε hε2 W hp hj rfl]
  exact cfzpPrimePowerBranchFreeTrigEvent_nonneg_of_nonposPhaseCellCoverage
    hε hε2 W hp hj hA hcoverage

theorem cfzp021VonMangoldtPulse_nonpos_of_nonnegPhaseCellCoverage
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {X p j : ℕ} (hp : Nat.Prime p) (hj : 0 < j)
    (hstep : X + 1 = p ^ j)
    (hA : ∀ θ ∈ Set.Ioo
        (cfzpPrimePowerPhaseAngleLeft ε W p j)
        (cfzpPrimePowerPhaseAngleRight ε W p j),
      cfzpPhaseDerivativeSinCoeff (cfzpModePhaseAspectRatio W) θ ≤ 0)
    (hcoverage : ∀ θ ∈ Set.Ioo
        (cfzpPrimePowerPhaseAngleLeft ε W p j)
        (cfzpPrimePowerPhaseAngleRight ε W p j),
      cfzpPhaseCellSinNonposCosNonneg θ) :
    cfzp021VonMangoldtPulse ε W (X + 1) ≤ 0 := by
  rw [hstep, cfzp021VonMangoldtPulse_eq_branchFreeTrigEvent_of_eq_prime_pow
    hε hε2 W hp hj rfl]
  exact cfzpPrimePowerBranchFreeTrigEvent_nonpos_of_nonnegPhaseCellCoverage
    hε hε2 W hp hj hA hcoverage

theorem cfzp021RadialContactDeficit_succ_le_of_nonposPhaseCellCoverage
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {X p j : ℕ} (hp : Nat.Prime p) (hj : 0 < j)
    (hstep : X + 1 = p ^ j)
    (hA : ∀ θ ∈ Set.Ioo
        (cfzpPrimePowerPhaseAngleLeft ε W p j)
        (cfzpPrimePowerPhaseAngleRight ε W p j),
      0 ≤ cfzpPhaseDerivativeSinCoeff (cfzpModePhaseAspectRatio W) θ)
    (hcoverage : ∀ θ ∈ Set.Ioo
        (cfzpPrimePowerPhaseAngleLeft ε W p j)
        (cfzpPrimePowerPhaseAngleRight ε W p j),
      cfzpPhaseCellSinNonposCosNonpos θ) :
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W (X + 1) ≤
      pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W X := by
  apply cfzp021RadialContactDeficit_succ_le_of_pulse_nonneg hε hε2 W X
  exact cfzp021VonMangoldtPulse_nonneg_of_nonposPhaseCellCoverage
    hε hε2 W hp hj hstep hA hcoverage

theorem cfzp021RadialContactDeficit_le_succ_of_nonnegPhaseCellCoverage
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {X p j : ℕ} (hp : Nat.Prime p) (hj : 0 < j)
    (hstep : X + 1 = p ^ j)
    (hA : ∀ θ ∈ Set.Ioo
        (cfzpPrimePowerPhaseAngleLeft ε W p j)
        (cfzpPrimePowerPhaseAngleRight ε W p j),
      cfzpPhaseDerivativeSinCoeff (cfzpModePhaseAspectRatio W) θ ≤ 0)
    (hcoverage : ∀ θ ∈ Set.Ioo
        (cfzpPrimePowerPhaseAngleLeft ε W p j)
        (cfzpPrimePowerPhaseAngleRight ε W p j),
      cfzpPhaseCellSinNonposCosNonneg θ) :
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W X ≤
      pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W (X + 1) := by
  apply cfzp021RadialContactDeficit_le_succ_of_pulse_nonpos hε hε2 W X
  exact cfzp021VonMangoldtPulse_nonpos_of_nonnegPhaseCellCoverage
    hε hε2 W hp hj hstep hA hcoverage

/-! ## Gate J: explicit remaining provider gap -/

/-- A cofinal net-positive pulse-block provider remains an independent open
input after the finite compression identities. -/
inductive Cfzp021VonMangoldtPulseCompressionGap : Prop
  | noIndependentCofinalNetPositivePulseBlockProvider

end DkMath.RH.CFBRCProjection
