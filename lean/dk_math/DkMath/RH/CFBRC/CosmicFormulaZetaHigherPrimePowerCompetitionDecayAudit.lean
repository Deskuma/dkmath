/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.RH.CFBRC.CosmicFormulaZetaHigherPrimePowerCellCountingEnvelopeAudit
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CosmicFormulaZetaHigherPrimePowerCompetitionDecayAudit"

/-!
# CFZP-047: decay of the higher-prime-power competition kernel

CFZP-046 reduced the higher-power debt versus the smooth margin to a quadratic
polynomial in the cell-left coordinate times `exp (-U / 2)`.  This module
proves that this profile tends to zero by the standard exponential limit in
Mathlib.  The argument is finite real analysis: it uses neither prime density
nor an infinite prime sum.  The discrepancy, prime-axis remainder, and
analytic-readiness providers remain explicit gaps.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.NumberTheory
open Filter
open MeasureTheory
open Set

/-! ## Gates A-C: profile and exponential decay -/

/-- The cell-free form of the higher-power competition kernel.

The parameter `U` is the left coordinate of a carrier cell.  The profile
records the `U² * exp (-U / 2)` and `U * exp (-U / 2)` scales that remain after
the rectangle sigma exponent cancels against the smooth margin.
-/
noncomputable def cfzp047HigherPowerCompetitionProfile
    (ε : ℝ)
    (W : PascalCenteredXiResidueTransportWindow)
    (U : ℝ) : ℝ :=
  8 * U * cfzp045HigherPowerReferenceMassConstant ε W *
    Real.exp (cfzp036PrimeAxisCarrierPeriod W / 2) *
    ((U + cfzp036PrimeAxisCarrierPeriod W) / Real.log 2 + 1) *
    Real.exp (-U / 2)

/-- The quadratic coefficient in the profile expansion. -/
noncomputable def cfzp047CompetitionQuadraticCoeff
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) : ℝ :=
  8 * cfzp045HigherPowerReferenceMassConstant ε W *
    Real.exp (cfzp036PrimeAxisCarrierPeriod W / 2) / Real.log 2

/-- The linear coefficient in the profile expansion. -/
noncomputable def cfzp047CompetitionLinearCoeff
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) : ℝ :=
  8 * cfzp045HigherPowerReferenceMassConstant ε W *
    Real.exp (cfzp036PrimeAxisCarrierPeriod W / 2) *
    (cfzp036PrimeAxisCarrierPeriod W / Real.log 2 + 1)

/-- The 046 kernel is exactly the cell-free profile at the cell-left point. -/
theorem cfzp047HigherPowerMarginCompetitionKernel_eq_profile
    (ε : ℝ)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) :
    cfzp046HigherPowerMarginCompetitionKernel ε W c n =
      cfzp047HigherPowerCompetitionProfile ε W
        (cfzp039CarrierCellLeft W c n) := by
  unfold cfzp046HigherPowerMarginCompetitionKernel
    cfzp047HigherPowerCompetitionProfile
  rw [cfzp046CarrierCellRight_eq_left_add_period]

/-- The profile is a quadratic-plus-linear exponential expression. -/
theorem cfzp047HigherPowerCompetitionProfile_eq_quadratic_linear
    (ε : ℝ)
    (W : PascalCenteredXiResidueTransportWindow)
    (U : ℝ) :
    cfzp047HigherPowerCompetitionProfile ε W U =
      cfzp047CompetitionQuadraticCoeff ε W *
          (U ^ 2 * Real.exp (-U / 2)) +
        cfzp047CompetitionLinearCoeff ε W *
          (U * Real.exp (-U / 2)) := by
  unfold cfzp047HigherPowerCompetitionProfile
    cfzp047CompetitionQuadraticCoeff cfzp047CompetitionLinearCoeff
  ring

/-- The half-rate linear exponential term tends to zero. -/
theorem cfzp047_tendsto_mul_exp_neg_half :
    Filter.Tendsto
      (fun U : ℝ => U * Real.exp (-U / 2))
      Filter.atTop (nhds 0) := by
  have hscale : Filter.Tendsto (fun U : ℝ => U / 2)
      Filter.atTop Filter.atTop :=
    tendsto_id.atTop_div_const (by norm_num)
  have hbase := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hscale
  have hmul :=
    (tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ => (2 : ℝ))
      Filter.atTop (nhds 2)).mul hbase
  convert hmul using 1
  · simp [pow_one]
    ring_nf
  · simp

/-- The half-rate quadratic exponential term tends to zero. -/
theorem cfzp047_tendsto_sq_mul_exp_neg_half :
    Filter.Tendsto
      (fun U : ℝ => U ^ 2 * Real.exp (-U / 2))
      Filter.atTop (nhds 0) := by
  have hscale : Filter.Tendsto (fun U : ℝ => U / 2)
      Filter.atTop Filter.atTop :=
    tendsto_id.atTop_div_const (by norm_num)
  have hbase := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp hscale
  have hmul :=
    (tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ => (4 : ℝ))
      Filter.atTop (nhds 4)).mul hbase
  convert hmul using 1
  · simp [pow_two]
    ring_nf
  · simp

/-- The cell-free higher-power competition profile tends to zero. -/
theorem cfzp047HigherPowerCompetitionProfile_tendsto_zero
    (ε : ℝ)
    (W : PascalCenteredXiResidueTransportWindow) :
    Filter.Tendsto
      (cfzp047HigherPowerCompetitionProfile ε W)
      Filter.atTop (nhds 0) := by
  have hquad := cfzp047_tendsto_sq_mul_exp_neg_half
  have hlin := cfzp047_tendsto_mul_exp_neg_half
  have hquad' :=
    (tendsto_const_nhds : Filter.Tendsto
      (fun _ : ℝ => cfzp047CompetitionQuadraticCoeff ε W)
      Filter.atTop (nhds (cfzp047CompetitionQuadraticCoeff ε W))).mul hquad
  have hlin' :=
    (tendsto_const_nhds : Filter.Tendsto
      (fun _ : ℝ => cfzp047CompetitionLinearCoeff ε W)
      Filter.atTop (nhds (cfzp047CompetitionLinearCoeff ε W))).mul hlin
  have hadd := hquad'.add hlin'
  have hfun : cfzp047HigherPowerCompetitionProfile ε W =
      (fun U =>
        cfzp047CompetitionQuadraticCoeff ε W *
            (U ^ 2 * Real.exp (-U / 2)) +
          cfzp047CompetitionLinearCoeff ε W *
            (U * Real.exp (-U / 2))) := by
    funext U
    exact cfzp047HigherPowerCompetitionProfile_eq_quadratic_linear ε W U
  rw [hfun]
  simpa using hadd

/-! ## Gates D-E: cofinal cell coordinates and the actual kernel -/

/-- The left coordinates of the carrier cells tend to `+∞`. -/
theorem cfzp047CarrierCellLeft_tendsto_atTop
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) :
    Filter.Tendsto
      (fun n : ℕ => cfzp039CarrierCellLeft W c n)
      Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop_atTop.2 ?_
  intro K
  obtain ⟨N, hN⟩ := cfzp043_carrierCellLeft_eventually_ge W c K
  exact ⟨N, hN⟩

/-- The actual 046 competition kernel tends to zero along carrier cells. -/
theorem cfzp047HigherPowerMarginCompetitionKernel_tendsto_zero
    (ε : ℝ)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) :
    Filter.Tendsto
      (fun n : ℕ =>
        cfzp046HigherPowerMarginCompetitionKernel ε W c n)
      Filter.atTop (nhds 0) := by
  have hprofile := cfzp047HigherPowerCompetitionProfile_tendsto_zero ε W
  have hleft := cfzp047CarrierCellLeft_tendsto_atTop W c
  have hcomp := hprofile.comp hleft
  have hfun :
      (fun n : ℕ => cfzp046HigherPowerMarginCompetitionKernel ε W c n) =
        cfzp047HigherPowerCompetitionProfile ε W ∘
          (fun n : ℕ => cfzp039CarrierCellLeft W c n) := by
    funext n
    exact cfzp047HigherPowerMarginCompetitionKernel_eq_profile ε W c n
  rw [hfun]
  exact hcomp

/-- A positive target is eventually above the competition kernel. -/
theorem cfzp047HigherPowerMarginCompetitionKernel_eventually_le
    {ε δ : ℝ}
    (hδ : 0 < δ)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      cfzp046HigherPowerMarginCompetitionKernel ε W c n ≤ δ := by
  have hkernel := cfzp047HigherPowerMarginCompetitionKernel_tendsto_zero ε W c
  have hev : ∀ᶠ n : ℕ in Filter.atTop,
      cfzp046HigherPowerMarginCompetitionKernel ε W c n < δ :=
    hkernel.eventually (Iio_mem_nhds hδ)
  obtain ⟨N, hN⟩ := (eventually_atTop.1 hev)
  refine ⟨N, ?_⟩
  intro n hn
  exact (hN n hn).le

/-- Radial lateness and a kernel bound can be chosen with one threshold. -/
theorem cfzp047_eventually_radialLate_and_kernel_le
    {ε δ : ℝ}
    (hδ : 0 < δ)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      cfzp044RadialLateThreshold ε W c ≤
          cfzp039CarrierCellLeft W c n ∧
      cfzp046HigherPowerMarginCompetitionKernel ε W c n ≤ δ := by
  obtain ⟨Nlate, hlate⟩ := cfzp043_carrierCellLeft_eventually_ge W c
    (cfzp044RadialLateThreshold ε W c)
  obtain ⟨Nkernel, hkernel⟩ :=
    cfzp047HigherPowerMarginCompetitionKernel_eventually_le hδ W c
  refine ⟨max Nlate Nkernel, ?_⟩
  intro n hn
  exact ⟨hlate n (le_trans (Nat.le_max_left _ _) hn),
    hkernel n (le_trans (Nat.le_max_right _ _) hn)⟩

/-! ## Gates F-I: eventual margin domination -/

/-- A positive transform eventually dominates the higher-power kernel. -/
theorem cfzp047_eventually_kernel_le_positiveTransform
    {ε : ℝ}
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ)
    (hM : 0 < cfzp039ExponentialCarrierPeriodTransform ε W c) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      cfzp044RadialLateThreshold ε W c ≤
          cfzp039CarrierCellLeft W c n ∧
      cfzp046HigherPowerMarginCompetitionKernel ε W c n ≤
          cfzp039ExponentialCarrierPeriodTransform ε W c := by
  exact cfzp047_eventually_radialLate_and_kernel_le hM W c

/-- The higher-power exponential envelope eventually costs half the margin. -/
theorem cfzp047HigherPowerEnvelope_eventually_le_half_explicitSmoothMargin
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ)
    (hM : 0 < cfzp039ExponentialCarrierPeriodTransform ε W c) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      cfzp044RadialLateThreshold ε W c ≤
          cfzp039CarrierCellLeft W c n ∧
      cfzp045HigherPowerReferenceMassConstant ε W *
          cfzp046HigherPowerSigmaTailExponentialEnvelope W c n ≤
        cfzp044ExplicitSmoothMargin ε W c n / 2 := by
  obtain ⟨N, hN⟩ := cfzp047_eventually_kernel_le_positiveTransform W c hM
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨hLate, hkernel⟩ := hN n hn
  exact ⟨hLate,
    cfzp046HigherPowerEnvelope_le_half_explicitSmoothMargin_of_kernel
      hε W c n hM hLate hkernel⟩

/-- The raw higher-power reference mass is eventually at most half the margin.

This is the residual-elimination theorem for the higher-prime-power route. -/
theorem cfzp047HigherPowerReferenceMass_eventually_le_half_explicitSmoothMargin
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    (hsub : Cfzp027SubcriticalPhaseAspect W)
    (c : ℝ)
    (hM : 0 < cfzp039ExponentialCarrierPeriodTransform ε W c) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      cfzp044RadialLateThreshold ε W c ≤
          cfzp039CarrierCellLeft W c n ∧
      cfzp034HigherPowerReferenceMass ε W
          (cfzp040CarrierCellNaturalLeft W c n)
          (cfzp040CarrierCellNaturalRight W c n) ≤
        cfzp044ExplicitSmoothMargin ε W c n / 2 := by
  obtain ⟨N, hN⟩ :=
    cfzp047HigherPowerEnvelope_eventually_le_half_explicitSmoothMargin
      hε W c hM
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨hLate, henv⟩ := hN n hn
  have hraw := cfzp046CarrierCellHigherPowerReferenceMass_le_exponentialEnvelope
    hε hε2 W hsub c n hLate
  exact ⟨hLate, hraw.trans henv⟩

/-- A positive phase supplies cofinally many cells with higher-power domination. -/
theorem cfzp047_exists_positive_transform_cofinal_higherPower_domination
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    (hstrip : Cfzp039PrimeAxisInteriorStrip W)
    (hsub : Cfzp027SubcriticalPhaseAspect W) :
    ∃ (c : ℝ) (N : ℕ),
      0 < cfzp039ExponentialCarrierPeriodTransform ε W c ∧
      ∀ n : ℕ, N ≤ n →
        cfzp044RadialLateThreshold ε W c ≤
            cfzp039CarrierCellLeft W c n ∧
        cfzp034HigherPowerReferenceMass ε W
            (cfzp040CarrierCellNaturalLeft W c n)
            (cfzp040CarrierCellNaturalRight W c n) ≤
          cfzp044ExplicitSmoothMargin ε W c n / 2 := by
  obtain ⟨c, hc⟩ := cfzp039ExponentialCarrierPeriodTransform_exists_pos
    hε W hstrip
  obtain ⟨N, hN⟩ :=
    cfzp047HigherPowerReferenceMass_eventually_le_half_explicitSmoothMargin
      hε hε2 W hsub c hc
  exact ⟨c, N, hc, hN⟩

/-! ## Gate J: the remaining-half radial budget -/

/-- The budget left after the eventual higher-power half-margin payment. -/
def Cfzp047RemainingHalfExplicitSmoothMarginBudgetAt
    (ε η D : ℝ)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) : Prop :=
  pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W
      (cfzp040CarrierCellNaturalLeft W c n) +
    cfzp039PrimeAxisRemainderCellDebt ε W c n
      (cfzp040CarrierCellNaturalLeft W c n)
      (cfzp040CarrierCellNaturalRight W c n) + D ≤
    cfzp044ExplicitSmoothMargin ε W c n / 2 + η

/-- The remaining-half budget feeds the finite radial reservoir theorem. -/
theorem cfzp047RemainingHalfBudget_implies_radialContactDeficit_le
    {ε η D : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hM : 0 < cfzp039ExponentialCarrierPeriodTransform ε W c)
    (hLate : cfzp044RadialLateThreshold ε W c ≤
      cfzp039CarrierCellLeft W c n)
    (hHigher :
      cfzp034HigherPowerReferenceMass ε W
          (cfzp040CarrierCellNaturalLeft W c n)
          (cfzp040CarrierCellNaturalRight W c n) ≤
        cfzp044ExplicitSmoothMargin ε W c n / 2)
    (hSmoothLog :
      cfzp040SmoothAbelCarrierModel ε W
          (cfzp040CarrierCellExpLeft W c n)
          (cfzp040CarrierCellExpRight W c n) =
        cfzp042SmoothLogCellIntegral ε W c n)
    (hf_diff : ∀ t ∈ Set.Icc
        (cfzp040CarrierCellExpLeft W c n)
        (cfzp040CarrierCellExpRight W c n),
      DifferentiableAt ℝ (cfzp040PrimeAxisCarrierTestFunction ε W) t)
    (hf_int : IntegrableOn
      (deriv (cfzp040PrimeAxisCarrierTestFunction ε W)) (Set.Icc
        (cfzp040CarrierCellExpLeft W c n)
        (cfzp040CarrierCellExpRight W c n)))
    (hM_int : IntegrableOn
      (fun t => deriv (cfzp040PrimeAxisCarrierTestFunction ε W) t *
        cfzp040PrimeCountingSmoothModel t) (Set.Ioc
          (cfzp040CarrierCellExpLeft W c n)
          (cfzp040CarrierCellExpRight W c n)))
    (hD_int : IntegrableOn
      (fun t => deriv (cfzp040PrimeAxisCarrierTestFunction ε W) t *
        cfzp040PrimeCountingDiscrepancy t) (Set.Ioc
          (cfzp040CarrierCellExpLeft W c n)
          (cfzp040CarrierCellExpRight W c n)))
    (hD : Cfzp041PrimeCountingDiscrepancyFunctionalBoundAt
      ε W c n D)
    (hbudget : Cfzp047RemainingHalfExplicitSmoothMarginBudgetAt
      ε η D W c n) :
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W
      (cfzp040CarrierCellNaturalRight W c n) ≤ η := by
  have hbudget044 : Cfzp044ExplicitSmoothMarginBudgetAt ε η D W c n := by
    unfold Cfzp047RemainingHalfExplicitSmoothMarginBudgetAt at hbudget
    unfold Cfzp044ExplicitSmoothMarginBudgetAt
    linarith
  exact cfzp044ExplicitSmoothMarginBudget_implies_radialContactDeficit_le
    hε hε2 W c n hM hLate hSmoothLog hf_diff hf_int hM_int hD_int hD
    hbudget044

/-! ## Firewall -/

/-- Remaining providers that are intentionally outside CFZP-047. -/
inductive Cfzp047HigherPrimePowerCompetitionDecayGap : Prop
  | noAutomaticInteriorStripWindowProvider
  | noAutomaticSmoothAbelLogCellReadinessProvider
  | noPrimeCountingDiscrepancyFunctionalDecayProvider
  | noPointwiseDiscrepancyToFunctionalBound
  | noPrimeAxisRemainderCellDebtDecayProvider
  | noCofinalRemainingHalfBudgetProvider

end DkMath.RH.CFBRCProjection
