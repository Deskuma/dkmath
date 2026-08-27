/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.RH.CFBRC.CosmicFormulaZetaBranchFreePrimePowerSignedMassBudgetAudit
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CosmicFormulaZetaSignedMassCutoffFrontierIncrementAudit"

/-!
# CFZP-020: signed-mass cutoff frontier increments

This module makes the one-step evolution of the existing canonical
prime-power support explicit.  The positive event mass and negative event
debt from CFZP-019 are split over the new support appearing at `X + 1`.
Their exact recurrences give the signed-ledger and radial-deficit increments.

The mass and debt are individually monotone, but their difference is not
declared monotone.  Frontier sign hypotheses only produce conditional
one-step deficit directions; no cofinal provider, asymptotic coverage, joint
limit, or RH statement is introduced.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.NumberTheory

/-! ## Gate A/B: support inclusion and one-step frontier -/

/-- The canonical prime-power pair support is monotone in its natural cutoff. -/
theorem cfzp020PrimePowerPairSupportUpTo_mono
    {X Y : ℕ} (hXY : X ≤ Y) :
    pascalPrimePowerPairSupportUpTo X ⊆
      pascalPrimePowerPairSupportUpTo Y := by
  intro pk hpk
  rw [mem_pascalPrimePowerPairSupportUpTo_iff]
  have hs := mem_pascalPrimePowerPairSupportUpTo_iff.mp hpk
  have hp := mem_pascalPrimeCoordinateSupportUpTo_iff.mp hs.1
  exact ⟨mem_pascalPrimeCoordinateSupportUpTo_iff.mpr
      ⟨hp.1, hp.2.trans hXY⟩,
    hs.2.1.trans_le hXY,
    hs.2.2.trans hXY⟩

/-- The new support frontier between `X` and `X + 1`. -/
def cfzp020PrimePowerCutoffFrontier (X : ℕ) : Finset (ℕ × ℕ) :=
  pascalPrimePowerPairSupportUpTo (X + 1) \
    pascalPrimePowerPairSupportUpTo X

theorem cfzp020PrimePowerCutoffFrontier_subset_succ (X : ℕ) :
    cfzp020PrimePowerCutoffFrontier X ⊆
      pascalPrimePowerPairSupportUpTo (X + 1) := by
  exact Finset.sdiff_subset

theorem cfzp020PrimePowerCutoffFrontier_disjoint_prev (X : ℕ) :
    Disjoint (pascalPrimePowerPairSupportUpTo X)
      (cfzp020PrimePowerCutoffFrontier X) := by
  exact Finset.disjoint_sdiff

/-- The successor support is the disjoint union of the old support and its
frontier. -/
theorem cfzp020PrimePowerPairSupportUpTo_succ_eq_union (X : ℕ) :
    pascalPrimePowerPairSupportUpTo (X + 1) =
      pascalPrimePowerPairSupportUpTo X ∪
        cfzp020PrimePowerCutoffFrontier X := by
  symm
  exact Finset.union_sdiff_of_subset
    (cfzp020PrimePowerPairSupportUpTo_mono (Nat.le_add_right X 1))

/-! ## Gate C: frontier mass and debt -/

/-- Positive event mass contributed by the new pair support at `X + 1`. -/
noncomputable def cfzp020FrontierPositiveEventMass
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) : ℝ :=
  ∑ pk ∈ cfzp020PrimePowerCutoffFrontier X,
    cfzp019PrimePowerEventPositiveMass ε W pk.1 (pk.2 + 1)

/-- Negative event debt contributed by the new pair support at `X + 1`. -/
noncomputable def cfzp020FrontierNegativeEventDebt
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) : ℝ :=
  ∑ pk ∈ cfzp020PrimePowerCutoffFrontier X,
    cfzp019PrimePowerEventNegativeDebt ε W pk.1 (pk.2 + 1)

theorem cfzp020FrontierPositiveEventMass_nonneg
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    0 ≤ cfzp020FrontierPositiveEventMass ε W X := by
  unfold cfzp020FrontierPositiveEventMass
  exact Finset.sum_nonneg fun pk hpk =>
    cfzp019PrimePowerEventPositiveMass_nonneg ε W pk.1 (pk.2 + 1)

theorem cfzp020FrontierNegativeEventDebt_nonneg
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    0 ≤ cfzp020FrontierNegativeEventDebt ε W X := by
  unfold cfzp020FrontierNegativeEventDebt
  exact Finset.sum_nonneg fun pk hpk =>
    cfzp019PrimePowerEventNegativeDebt_nonneg ε W pk.1 (pk.2 + 1)

/-! ## Gate D: cumulative one-step recurrences -/

theorem cfzp020PositiveEventMass_succ_eq_add_frontier
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    cfzp019BranchFreePositiveEventMass ε W (X + 1) =
      cfzp019BranchFreePositiveEventMass ε W X +
        cfzp020FrontierPositiveEventMass ε W X := by
  unfold cfzp019BranchFreePositiveEventMass
    cfzp020FrontierPositiveEventMass
  rw [cfzp020PrimePowerPairSupportUpTo_succ_eq_union]
  rw [Finset.sum_union (cfzp020PrimePowerCutoffFrontier_disjoint_prev X)]

theorem cfzp020NegativeEventDebt_succ_eq_add_frontier
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    cfzp019BranchFreeNegativeEventDebt ε W (X + 1) =
      cfzp019BranchFreeNegativeEventDebt ε W X +
        cfzp020FrontierNegativeEventDebt ε W X := by
  unfold cfzp019BranchFreeNegativeEventDebt
    cfzp020FrontierNegativeEventDebt
  rw [cfzp020PrimePowerPairSupportUpTo_succ_eq_union]
  rw [Finset.sum_union (cfzp020PrimePowerCutoffFrontier_disjoint_prev X)]

/-! ## Gate E: mass/debt monotonicity -/

theorem cfzp020PositiveEventMass_le_succ
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    cfzp019BranchFreePositiveEventMass ε W X ≤
      cfzp019BranchFreePositiveEventMass ε W (X + 1) := by
  rw [cfzp020PositiveEventMass_succ_eq_add_frontier]
  exact le_add_of_nonneg_right (cfzp020FrontierPositiveEventMass_nonneg ε W X)

theorem cfzp020NegativeEventDebt_le_succ
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    cfzp019BranchFreeNegativeEventDebt ε W X ≤
      cfzp019BranchFreeNegativeEventDebt ε W (X + 1) := by
  rw [cfzp020NegativeEventDebt_succ_eq_add_frontier]
  exact le_add_of_nonneg_right (cfzp020FrontierNegativeEventDebt_nonneg ε W X)

theorem cfzp020PositiveEventMass_mono
    {X Y : ℕ} (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (hXY : X ≤ Y) :
    cfzp019BranchFreePositiveEventMass ε W X ≤
      cfzp019BranchFreePositiveEventMass ε W Y := by
  unfold cfzp019BranchFreePositiveEventMass
  apply Finset.sum_le_sum_of_subset_of_nonneg
    (cfzp020PrimePowerPairSupportUpTo_mono hXY)
  intro pk hpk hnot
  exact cfzp019PrimePowerEventPositiveMass_nonneg ε W pk.1 (pk.2 + 1)

theorem cfzp020NegativeEventDebt_mono
    {X Y : ℕ} (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (hXY : X ≤ Y) :
    cfzp019BranchFreeNegativeEventDebt ε W X ≤
      cfzp019BranchFreeNegativeEventDebt ε W Y := by
  unfold cfzp019BranchFreeNegativeEventDebt
  apply Finset.sum_le_sum_of_subset_of_nonneg
    (cfzp020PrimePowerPairSupportUpTo_mono hXY)
  intro pk hpk hnot
  exact cfzp019PrimePowerEventNegativeDebt_nonneg ε W pk.1 (pk.2 + 1)

/-! ## Gate F/G: ledger and radial-deficit increments -/

/-- The signed branch-free ledger changes by frontier mass minus frontier debt. -/
theorem cfzp020BranchFreeTrigLedger_sub_eq_frontierMass_sub_frontierDebt
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    cfzpPrimePowerBranchFreeTrigLedger ε W (X + 1) -
        cfzpPrimePowerBranchFreeTrigLedger ε W X =
      cfzp020FrontierPositiveEventMass ε W X -
        cfzp020FrontierNegativeEventDebt ε W X := by
  calc
    cfzpPrimePowerBranchFreeTrigLedger ε W (X + 1) -
          cfzpPrimePowerBranchFreeTrigLedger ε W X =
        (cfzp019BranchFreePositiveEventMass ε W (X + 1) -
            cfzp019BranchFreeNegativeEventDebt ε W (X + 1)) -
          (cfzp019BranchFreePositiveEventMass ε W X -
            cfzp019BranchFreeNegativeEventDebt ε W X) := by
      rw [cfzp019BranchFreeTrigLedger_eq_positiveMass_sub_negativeDebt,
        cfzp019BranchFreeTrigLedger_eq_positiveMass_sub_negativeDebt]
    _ = cfzp020FrontierPositiveEventMass ε W X -
          cfzp020FrontierNegativeEventDebt ε W X := by
      rw [cfzp020PositiveEventMass_succ_eq_add_frontier,
        cfzp020NegativeEventDebt_succ_eq_add_frontier]
      ring

/-- Additive form of the signed ledger frontier increment. -/
theorem cfzp020BranchFreeTrigLedger_succ_eq_add_frontierMass_sub_frontierDebt
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    cfzpPrimePowerBranchFreeTrigLedger ε W (X + 1) =
      cfzpPrimePowerBranchFreeTrigLedger ε W X +
        cfzp020FrontierPositiveEventMass ε W X -
        cfzp020FrontierNegativeEventDebt ε W X := by
  have h := cfzp020BranchFreeTrigLedger_sub_eq_frontierMass_sub_frontierDebt ε W X
  linarith

/-- In the safe-frequency regime, frontier debt increases the radial deficit
and frontier positive mass decreases it. -/
theorem cfzp020RadialContactDeficit_succ_eq_add_frontierDebt_sub_frontierMass
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W (X + 1) =
      pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W X +
        cfzp020FrontierNegativeEventDebt ε W X -
        cfzp020FrontierPositiveEventMass ε W X := by
  rw [cfzp019RadialContactDeficit_eq_baseline_add_debt_sub_positiveMass
      hε hε2 W (X + 1),
    cfzp019RadialContactDeficit_eq_baseline_add_debt_sub_positiveMass
      hε hε2 W X,
    cfzp020PositiveEventMass_succ_eq_add_frontier,
    cfzp020NegativeEventDebt_succ_eq_add_frontier]
  ring

/-! ## Gate H: frontier sign adapters -/

theorem cfzp020FrontierNegativeEventDebt_eq_zero_of_all_events_nonneg
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ)
    (hall : ∀ pk ∈ cfzp020PrimePowerCutoffFrontier X,
      0 ≤ cfzpPrimePowerBranchFreeTrigEvent ε W pk.1 (pk.2 + 1)) :
    cfzp020FrontierNegativeEventDebt ε W X = 0 := by
  unfold cfzp020FrontierNegativeEventDebt
  apply Finset.sum_eq_zero
  intro pk hpk
  simp [cfzp019PrimePowerEventNegativeDebt,
    max_eq_right (neg_nonpos.mpr (hall pk hpk))]

theorem cfzp020FrontierPositiveEventMass_eq_zero_of_all_events_nonpos
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ)
    (hall : ∀ pk ∈ cfzp020PrimePowerCutoffFrontier X,
      cfzpPrimePowerBranchFreeTrigEvent ε W pk.1 (pk.2 + 1) ≤ 0) :
    cfzp020FrontierPositiveEventMass ε W X = 0 := by
  unfold cfzp020FrontierPositiveEventMass
  apply Finset.sum_eq_zero
  intro pk hpk
  simp [cfzp019PrimePowerEventPositiveMass, max_eq_right (hall pk hpk)]

theorem cfzp020RadialContactDeficit_succ_le_of_all_frontier_events_nonneg
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ)
    (hall : ∀ pk ∈ cfzp020PrimePowerCutoffFrontier X,
      0 ≤ cfzpPrimePowerBranchFreeTrigEvent ε W pk.1 (pk.2 + 1)) :
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W (X + 1) ≤
      pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W X := by
  rw [cfzp020RadialContactDeficit_succ_eq_add_frontierDebt_sub_frontierMass
    hε hε2 W X,
    cfzp020FrontierNegativeEventDebt_eq_zero_of_all_events_nonneg ε W X hall]
  linarith [cfzp020FrontierPositiveEventMass_nonneg ε W X]

theorem cfzp020RadialContactDeficit_le_succ_of_all_frontier_events_nonpos
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ)
    (hall : ∀ pk ∈ cfzp020PrimePowerCutoffFrontier X,
      cfzpPrimePowerBranchFreeTrigEvent ε W pk.1 (pk.2 + 1) ≤ 0) :
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W X ≤
      pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W (X + 1) := by
  rw [cfzp020RadialContactDeficit_succ_eq_add_frontierDebt_sub_frontierMass
    hε hε2 W X,
    cfzp020FrontierPositiveEventMass_eq_zero_of_all_events_nonpos ε W X hall]
  linarith [cfzp020FrontierNegativeEventDebt_nonneg ε W X]

/-! ## Gate I: empty-frontier constancy -/

theorem cfzp020PositiveEventMass_succ_eq_of_frontier_empty
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ)
    (hempty : cfzp020PrimePowerCutoffFrontier X = ∅) :
    cfzp019BranchFreePositiveEventMass ε W (X + 1) =
      cfzp019BranchFreePositiveEventMass ε W X := by
  have hfront : cfzp020FrontierPositiveEventMass ε W X = 0 := by
    simp [cfzp020FrontierPositiveEventMass, hempty]
  rw [cfzp020PositiveEventMass_succ_eq_add_frontier, hfront, add_zero]

theorem cfzp020NegativeEventDebt_succ_eq_of_frontier_empty
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ)
    (hempty : cfzp020PrimePowerCutoffFrontier X = ∅) :
    cfzp019BranchFreeNegativeEventDebt ε W (X + 1) =
      cfzp019BranchFreeNegativeEventDebt ε W X := by
  have hfront : cfzp020FrontierNegativeEventDebt ε W X = 0 := by
    simp [cfzp020FrontierNegativeEventDebt, hempty]
  rw [cfzp020NegativeEventDebt_succ_eq_add_frontier, hfront, add_zero]

theorem cfzp020BranchFreeTrigLedger_succ_eq_of_frontier_empty
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ)
    (hempty : cfzp020PrimePowerCutoffFrontier X = ∅) :
    cfzpPrimePowerBranchFreeTrigLedger ε W (X + 1) =
      cfzpPrimePowerBranchFreeTrigLedger ε W X := by
  have hpos : cfzp020FrontierPositiveEventMass ε W X = 0 := by
    simp [cfzp020FrontierPositiveEventMass, hempty]
  have hdebt : cfzp020FrontierNegativeEventDebt ε W X = 0 := by
    simp [cfzp020FrontierNegativeEventDebt, hempty]
  rw [cfzp020BranchFreeTrigLedger_succ_eq_add_frontierMass_sub_frontierDebt,
    hpos, hdebt, sub_zero, add_zero]

theorem cfzp020RadialContactDeficit_succ_eq_of_frontier_empty
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ)
    (hempty : cfzp020PrimePowerCutoffFrontier X = ∅) :
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W (X + 1) =
      pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W X := by
  have hpos : cfzp020FrontierPositiveEventMass ε W X = 0 := by
    simp [cfzp020FrontierPositiveEventMass, hempty]
  have hdebt : cfzp020FrontierNegativeEventDebt ε W X = 0 := by
    simp [cfzp020FrontierNegativeEventDebt, hempty]
  rw [cfzp020RadialContactDeficit_succ_eq_add_frontierDebt_sub_frontierMass
    hε hε2 W X, hdebt, hpos, sub_zero, add_zero]

/-! ## Gate J/G: explicit frontier -/

/-- A cofinal net-positive frontier provider remains an open arithmetic input.
The finite increment identities above do not supply it. -/
inductive Cfzp020SignedMassCutoffIncrementGap : Prop
  | noIndependentCofinalFrontierNetPositiveMassProvider

end DkMath.RH.CFBRCProjection
