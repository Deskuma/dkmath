/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.RH.CFBRC.CosmicFormulaZetaPrimeAxisCombinedDiscrepancySensitivityEnvelopeAudit
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CosmicFormulaZetaPrimeCountingPNTToRelativeDiscrepancyAudit"

/-!
# CFZP-051: PNT ratio to relative finite-cell discrepancy

This module fixes the standard real/floor prime-counting ratio as the only
arithmetic asymptotic input.  Everything below it is a finite transport from
that provider to the existing CFZP-049/050 cell APIs.  In particular, this
file does not prove the prime number theorem, add an external dependency, or
assert a limit exchange or a global RH statement.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.NumberTheory
open MeasureTheory
open Set

/-! ## Gates A-B: the canonical PNT ratio and its relative discrepancy -/

/-- The real/floor prime-counting ratio used as the standard PNT provider. -/
noncomputable def cfzp051PrimeCountingPNTRatio (x : ℝ) : ℝ :=
  (Nat.primeCounting ⌊x⌋₊ : ℝ) /
    cfzp040PrimeCountingSmoothModel x

/-- The sole arithmetic asymptotic provider admitted by CFZP-051. -/
def Cfzp051PrimeCountingPNTRatioAtTop : Prop :=
  Filter.Tendsto cfzp051PrimeCountingPNTRatio
    Filter.atTop (nhds 1)

/-- The discrepancy normalized by the exact finite smooth model. -/
noncomputable def cfzp051PrimeCountingRelativeDiscrepancyRatio (x : ℝ) : ℝ :=
  cfzp040PrimeCountingDiscrepancy x /
    cfzp040PrimeCountingSmoothModel x

private theorem cfzp051_smoothModel_pos_of_one_lt
    {x : ℝ} (hx : 1 < x) :
    0 < cfzp040PrimeCountingSmoothModel x := by
  unfold cfzp040PrimeCountingSmoothModel
  exact div_pos (by linarith) (Real.log_pos hx)

private theorem cfzp051_relativeRatio_eq_pntRatio_sub_one_of_one_lt
    {x : ℝ} (hx : 1 < x) :
    cfzp051PrimeCountingRelativeDiscrepancyRatio x =
      cfzp051PrimeCountingPNTRatio x - 1 := by
  unfold cfzp051PrimeCountingRelativeDiscrepancyRatio
    cfzp051PrimeCountingPNTRatio cfzp040PrimeCountingDiscrepancy
    cfzp040PrimeCountingSmoothModel
  have hpos : 0 < cfzp040PrimeCountingSmoothModel x :=
    cfzp051_smoothModel_pos_of_one_lt hx
  have hlog : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
  field_simp [hlog, ne_of_gt hpos]

/-- A PNT ratio provider makes the normalized discrepancy tend to zero. -/
theorem cfzp051_pntRatio_implies_relativeDiscrepancyRatio_tendsto_zero
    (hPNT : Cfzp051PrimeCountingPNTRatioAtTop) :
    Filter.Tendsto cfzp051PrimeCountingRelativeDiscrepancyRatio
      Filter.atTop (nhds 0) := by
  have hsub : Filter.Tendsto
      (fun x : ℝ => cfzp051PrimeCountingPNTRatio x - 1)
      Filter.atTop (nhds (1 - 1)) := hPNT.sub_const 1
  have hsub0 : Filter.Tendsto
      (fun x : ℝ => cfzp051PrimeCountingPNTRatio x - 1)
      Filter.atTop (nhds 0) := by simpa using hsub
  apply hsub0.congr'
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx
  exact (cfzp051_relativeRatio_eq_pntRatio_sub_one_of_one_lt hx).symm

/-- The exact eventual relative pointwise discrepancy predicate. -/
def Cfzp051EventuallyRelativePrimeCountingDiscrepancy
    (delta : ℝ) : Prop :=
  ∀ᶠ x : ℝ in Filter.atTop,
    |cfzp040PrimeCountingDiscrepancy x| ≤
      delta * cfzp040PrimeCountingSmoothModel x

/-- Every positive tolerance is eventually supplied by the PNT ratio. -/
theorem cfzp051_pntRatio_implies_eventually_relativeDiscrepancy
    (hPNT : Cfzp051PrimeCountingPNTRatioAtTop)
    {delta : ℝ} (hdelta : 0 < delta) :
    Cfzp051EventuallyRelativePrimeCountingDiscrepancy delta := by
  have hratio :=
    cfzp051_pntRatio_implies_relativeDiscrepancyRatio_tendsto_zero hPNT
  have habs : ∀ᶠ x : ℝ in Filter.atTop,
      |cfzp051PrimeCountingRelativeDiscrepancyRatio x| < delta := by
    rw [Metric.tendsto_atTop] at hratio
    obtain ⟨N, hN⟩ := hratio delta hdelta
    filter_upwards [Filter.eventually_ge_atTop N] with x hx
    simpa [Real.dist_eq] using hN x hx
  filter_upwards [habs, Filter.eventually_gt_atTop (1 : ℝ)] with x hx hx1
  have hs : 0 < cfzp040PrimeCountingSmoothModel x :=
    cfzp051_smoothModel_pos_of_one_lt hx1
  have hratio_abs :
      |cfzp040PrimeCountingDiscrepancy x| /
          cfzp040PrimeCountingSmoothModel x < delta := by
    simpa [cfzp051PrimeCountingRelativeDiscrepancyRatio, abs_div,
      abs_of_pos hs] using hx
  exact le_of_lt ((div_lt_iff₀ hs).1 hratio_abs)

/-! ## Gates C-D: exponential cell cofinality and cell transport -/

/-- The exponential left endpoints of the carrier cells are cofinal. -/
theorem cfzp051CarrierCellExpLeft_tendsto_atTop
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) :
    Filter.Tendsto
      (fun n : ℕ => cfzp040CarrierCellExpLeft W c n)
      Filter.atTop Filter.atTop := by
  convert Real.tendsto_exp_atTop.comp
    (cfzp047CarrierCellLeft_tendsto_atTop W c) using 1
  ext n
  rfl

/-- An eventual real pointwise bound restricts to every sufficiently late cell. -/
theorem cfzp051_pntRatio_implies_eventually_cellRelativeDiscrepancy
    (hPNT : Cfzp051PrimeCountingPNTRatioAtTop)
    {delta : ℝ} (hdelta : 0 < delta)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      Cfzp049PrimeCountingRelativeDiscrepancyBoundAt W c n delta := by
  have hpoint :=
    cfzp051_pntRatio_implies_eventually_relativeDiscrepancy hPNT hdelta
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.1 hpoint
  have hcell :=
    (cfzp051CarrierCellExpLeft_tendsto_atTop W c).eventually
      (Filter.eventually_ge_atTop X)
  filter_upwards [hcell] with n hn
  intro x hx
  exact hX x (le_trans hn hx.1)

/-! ## Gates E-F: explicit eighth-margin coefficient closure -/

/-- A strictly safe relative discrepancy tolerance for one eighth of the margin. -/
noncomputable def cfzp051EighthMarginRelativeTolerance
    (epsilon : ℝ)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) : ℝ :=
  cfzp039ExponentialCarrierPeriodTransform epsilon W c /
    (32 * Real.exp (cfzp036PrimeAxisCarrierPeriod W) *
      (cfzp050CombinedSensitivityConstant epsilon W + 1))

theorem cfzp051EighthMarginRelativeTolerance_pos
    {epsilon : ℝ} (hε : 0 < epsilon)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ)
    (hM : 0 < cfzp039ExponentialCarrierPeriodTransform epsilon W c) :
    0 < cfzp051EighthMarginRelativeTolerance epsilon W c := by
  unfold cfzp051EighthMarginRelativeTolerance
  apply div_pos hM
  have hC := cfzp050CombinedSensitivityConstant_nonneg hε W
  have hExp : 0 < Real.exp (cfzp036PrimeAxisCarrierPeriod W) :=
    Real.exp_pos _
  have hC1 : 0 < cfzp050CombinedSensitivityConstant epsilon W + 1 := by
    linarith
  exact mul_pos (mul_pos (by norm_num) hExp) hC1

theorem cfzp051EighthMarginRelativeTolerance_condition
    {epsilon : ℝ} (hε : 0 < epsilon)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ)
    (hM : 0 < cfzp039ExponentialCarrierPeriodTransform epsilon W c) :
    Cfzp050RelativeDiscrepancyEighthMarginCondition
      epsilon (cfzp051EighthMarginRelativeTolerance epsilon W c) W c := by
  unfold Cfzp050RelativeDiscrepancyEighthMarginCondition
    cfzp051EighthMarginRelativeTolerance
  have hC := cfzp050CombinedSensitivityConstant_nonneg hε W
  have hExp : 0 < Real.exp (cfzp036PrimeAxisCarrierPeriod W) :=
    Real.exp_pos _
  have hden : 0 < 32 * Real.exp (cfzp036PrimeAxisCarrierPeriod W) *
      (cfzp050CombinedSensitivityConstant epsilon W + 1) := by
    exact mul_pos (mul_pos (by norm_num) hExp) (by linarith)
  have hC1 : 0 < cfzp050CombinedSensitivityConstant epsilon W + 1 := by
    linarith
  have hMC :
      cfzp039ExponentialCarrierPeriodTransform epsilon W c *
          cfzp050CombinedSensitivityConstant epsilon W ≤
        cfzp039ExponentialCarrierPeriodTransform epsilon W c *
          (cfzp050CombinedSensitivityConstant epsilon W + 1) := by
    apply mul_le_mul_of_nonneg_left _ hM.le
    linarith
  calc
    32 * (cfzp039ExponentialCarrierPeriodTransform epsilon W c /
        (32 * Real.exp (cfzp036PrimeAxisCarrierPeriod W) *
          (cfzp050CombinedSensitivityConstant epsilon W + 1))) *
        Real.exp (cfzp036PrimeAxisCarrierPeriod W) *
        cfzp050CombinedSensitivityConstant epsilon W =
      (cfzp039ExponentialCarrierPeriodTransform epsilon W c *
        cfzp050CombinedSensitivityConstant epsilon W) /
        (cfzp050CombinedSensitivityConstant epsilon W + 1) := by
          field_simp [ne_of_gt hden, ne_of_gt hExp, ne_of_gt hC1]
    _ ≤ cfzp039ExponentialCarrierPeriodTransform epsilon W c := by
      exact (div_le_iff₀ hC1).2 (by simpa [mul_comm] using hMC)

/-- The eighth coefficient condition is the general margin-share condition. -/
theorem cfzp051EighthCondition_implies_marginShare
    {epsilon delta : ℝ}
    (W : PascalCenteredXiResidueTransportWindow) (c : ℝ)
    (hCondition : Cfzp050RelativeDiscrepancyEighthMarginCondition
      epsilon delta W c) :
    Cfzp050RelativeDiscrepancyMarginShareCondition
      epsilon delta (1 / 8 : ℝ) W c := by
  dsimp [Cfzp050RelativeDiscrepancyEighthMarginCondition,
    Cfzp050RelativeDiscrepancyMarginShareCondition] at *
  linarith

/-- A finite combined debt satisfying the eighth condition costs one eighth. -/
theorem cfzp051CombinedDebt_le_eighth_explicitSmoothMargin
    {epsilon delta : ℝ} (hε : 0 < epsilon) (hdelta : 0 ≤ delta)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hM : 0 < cfzp039ExponentialCarrierPeriodTransform epsilon W c)
    (hU : 1 ≤ cfzp039CarrierCellLeft W c n)
    (hCondition : Cfzp050RelativeDiscrepancyEighthMarginCondition
      epsilon delta W c)
    (hDebt : cfzp049CombinedPrimeCountingDiscrepancyCellDebt epsilon W c n ≤
      cfzp050RelativeCombinedDiscrepancyExplicitEnvelope epsilon delta W c n) :
    cfzp049CombinedPrimeCountingDiscrepancyCellDebt epsilon W c n ≤
      cfzp044ExplicitSmoothMargin epsilon W c n / 8 := by
  have hShare := cfzp051EighthCondition_implies_marginShare W c hCondition
  have henv := cfzp050RelativeEnvelope_le_marginShare
    hε hdelta (by norm_num : (0 : ℝ) ≤ 1 / 8) W c n hM hU hShare
  linarith

/-! ## Gate G: PNT to the eventual eighth-margin debt -/

/-- The finite analytic certificates still required by the debt bridge. -/
def Cfzp051FiniteDiscrepancyAnalyticReadyAt
    (epsilon : ℝ)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) : Prop :=
  IntegrableOn
      (fun x => |deriv (cfzp040PrimeAxisCarrierTestFunction epsilon W) x|)
      (Set.Ioc (cfzp040CarrierCellExpLeft W c n)
        (cfzp040CarrierCellExpRight W c n)) ∧
    IntegrableOn
      (fun x => deriv (cfzp040PrimeAxisCarrierTestFunction epsilon W) x *
        cfzp040PrimeCountingDiscrepancy x)
      (Set.Ioc (cfzp040CarrierCellExpLeft W c n)
        (cfzp040CarrierCellExpRight W c n)) ∧
    IntegrableOn
      (fun x => |deriv (cfzp048PrimeAxisRemainderTestFunction W) x|)
      (Set.Ioc (cfzp040CarrierCellExpLeft W c n)
        (cfzp040CarrierCellExpRight W c n)) ∧
    IntegrableOn
      (fun x => deriv (cfzp048PrimeAxisRemainderTestFunction W) x *
        cfzp040PrimeCountingDiscrepancy x)
      (Set.Ioc (cfzp040CarrierCellExpLeft W c n)
        (cfzp040CarrierCellExpRight W c n))

theorem cfzp051_pntRatio_eventually_combinedDebt_le_eighthMargin
    {epsilon : ℝ} (hε : 0 < epsilon)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ)
    (hM : 0 < cfzp039ExponentialCarrierPeriodTransform epsilon W c)
    (hPNT : Cfzp051PrimeCountingPNTRatioAtTop)
    (hReady : ∀ᶠ n : ℕ in Filter.atTop,
      Cfzp051FiniteDiscrepancyAnalyticReadyAt epsilon W c n) :
    ∀ᶠ n : ℕ in Filter.atTop,
      cfzp049CombinedPrimeCountingDiscrepancyCellDebt epsilon W c n ≤
        cfzp044ExplicitSmoothMargin epsilon W c n / 8 := by
  let delta := cfzp051EighthMarginRelativeTolerance epsilon W c
  have hdelta : 0 < delta :=
    cfzp051EighthMarginRelativeTolerance_pos hε W c hM
  have hcell := cfzp051_pntRatio_implies_eventually_cellRelativeDiscrepancy
    hPNT hdelta W c
  have hU : ∀ᶠ n : ℕ in Filter.atTop,
      1 ≤ cfzp039CarrierCellLeft W c n :=
    (cfzp047CarrierCellLeft_tendsto_atTop W c).eventually
      (Filter.eventually_ge_atTop (1 : ℝ))
  have hcondition := cfzp051EighthMarginRelativeTolerance_condition hε W c hM
  filter_upwards [hcell, hU, hReady] with n hn hUn hRn
  rcases hRn with ⟨hCA, hCD, hRA, hRD⟩
  have hDebt := cfzp050CombinedDebt_le_explicitRelativeEnvelope_auto
    hε hdelta.le W c n hUn hn hCA hCD hRA hRD
  exact cfzp051CombinedDebt_le_eighth_explicitSmoothMargin
    hε hdelta.le W c n hM hUn hcondition hDebt

/-! ## Gate H: the other eighth remains a separate radial provider -/

/-- The left radial eighth-credit condition, without claiming it automatically. -/
def Cfzp051LeftRadialEighthCreditBudgetAt
    (epsilon eta : ℝ)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) : Prop :=
  pascalCenteredXiPrimeSideFiniteRadialContactDeficit epsilon W
      (cfzp040CarrierCellNaturalLeft W c n) ≤
    cfzp044ExplicitSmoothMargin epsilon W c n / 8 + eta

theorem cfzp051_eighthDiscrepancy_and_leftEighthCredit_implies_combinedBudget
    {epsilon eta : ℝ}
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hDisc : cfzp049CombinedPrimeCountingDiscrepancyCellDebt epsilon W c n ≤
      cfzp044ExplicitSmoothMargin epsilon W c n / 8)
    (hLeft : Cfzp051LeftRadialEighthCreditBudgetAt epsilon eta W c n) :
    Cfzp049CombinedRemainingQuarterBudgetAt epsilon eta W c n := by
  unfold Cfzp051LeftRadialEighthCreditBudgetAt at hLeft
  unfold Cfzp049CombinedRemainingQuarterBudgetAt
  linarith

/-! ## Explicit firewall -/

/-- Unresolved arithmetic and analytic providers retained after CFZP-051. -/
inductive Cfzp051PrimeCountingPNTToRelativeDiscrepancyGap : Prop
  | noPrimeCountingPNTRatioProvider
  | noAutomaticFiniteDiscrepancyAnalyticReadinessProvider
  | noAutomaticInteriorStripWindowProvider
  | noAutomaticLeadingSmoothAbelLogCellReadinessProvider
  | noAutomaticLeftRadialEighthCreditBudgetProvider
  | noCofinalFinalRadialBudgetProvider

end DkMath.RH.CFBRCProjection
