/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.RH.CFBRC.CosmicFormulaZetaPrimeAxisSmoothWeightVariationEventualPositivityAudit
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CosmicFormulaZetaPrimeAxisExplicitSmoothMarginRadialBudgetAudit"

/-!
# CFZP-044: explicit smooth margin and radial budget

This module connects the finite smooth margin from CFZP-043 to the finite
radial reservoir of CFZP-041.  Late prime-axis exceptional support is removed
by an exact finite cell argument; higher-power and discrepancy debts remain
explicit inputs.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.NumberTheory
open MeasureTheory
open Set

/-! ## Gate A: the combined radial-late threshold -/

/-- A single threshold carrying both the 043 positivity and 041 eligibility
    requirements. -/
noncomputable def cfzp044RadialLateThreshold
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) : ℝ :=
  max (cfzp043SmoothPositivityThreshold ε W c) (max (3 * ε) 1)

/-- The radial threshold implies the smooth positivity threshold. -/
theorem cfzp044_smoothThreshold_le_of_radialLate
    {ε : ℝ} {W : PascalCenteredXiResidueTransportWindow} {c U : ℝ}
    (hU : cfzp044RadialLateThreshold ε W c ≤ U) :
    cfzp043SmoothPositivityThreshold ε W c ≤ U := by
  exact le_trans (le_max_left _ _) hU

/-- The radial threshold implies the finite prime-axis eligibility threshold. -/
theorem cfzp044_eligibilityThreshold_le_of_radialLate
    {ε : ℝ} {W : PascalCenteredXiResidueTransportWindow} {c U : ℝ}
    (hU : cfzp044RadialLateThreshold ε W c ≤ U) :
    max (3 * ε) 1 ≤ U := by
  exact le_trans (le_max_right _ _) hU

/-- The combined threshold also puts the cell in the 043 late region. -/
theorem cfzp044_two_le_of_radialLate
    {ε : ℝ} {W : PascalCenteredXiResidueTransportWindow} {c U : ℝ}
    (hU : cfzp044RadialLateThreshold ε W c ≤ U) :
    2 ≤ U := by
  have hs := cfzp044_smoothThreshold_le_of_radialLate hU
  unfold cfzp043SmoothPositivityThreshold at hs
  exact le_trans (le_max_left _ _) hs

/-- Positive phase has cofinally many cells above the combined threshold. -/
theorem cfzp044_exists_positive_transform_cofinal_radialLate_cells
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow)
    (hstrip : Cfzp039PrimeAxisInteriorStrip W) :
    ∃ (c : ℝ) (N : ℕ),
      0 < cfzp039ExponentialCarrierPeriodTransform ε W c ∧
      ∀ n : ℕ, N ≤ n →
        cfzp044RadialLateThreshold ε W c ≤
          cfzp039CarrierCellLeft W c n := by
  obtain ⟨c, hc⟩ := cfzp039ExponentialCarrierPeriodTransform_exists_pos
    hε W hstrip
  obtain ⟨N, hN⟩ := cfzp043_carrierCellLeft_eventually_ge W c
    (cfzp044RadialLateThreshold ε W c)
  exact ⟨c, N, hc, hN⟩

/-! ## Gate B: exact elimination of late exceptional prime-axis support -/

/-- In a radial-late natural cell every prime-axis support point is eligible. -/
theorem cfzp044PrimeAxisBlockSupport_eq_eligible
    {ε : ℝ}
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hcell : max (3 * ε) 1 ≤ cfzp039CarrierCellLeft W c n) :
    cfzp034PrimeAxisPairBlockSupport
        (cfzp040CarrierCellNaturalLeft W c n)
        (cfzp040CarrierCellNaturalRight W c n) =
      cfzp034EligiblePrimeAxisPairBlockSupport ε
        (cfzp040CarrierCellNaturalLeft W c n)
        (cfzp040CarrierCellNaturalRight W c n) := by
  classical
  apply Finset.Subset.antisymm
  · intro pk hpk
    have hblock := (Finset.mem_filter.mp hpk).1
    have hzero := (Finset.mem_filter.mp hpk).2
    have hright : pk ∈ pascalPrimePowerPairSupportUpTo
        (cfzp040CarrierCellNaturalRight W c n) :=
      (Finset.mem_sdiff.mp hblock).1
    have hcoord := mem_pascalPrimeCoordinateSupportUpTo_iff.mp
      (mem_pascalPrimePowerPairSupportUpTo_iff.mp hright).1
    have hp : Nat.Prime pk.1 := hcoord.1
    have hleft : pk ∉ pascalPrimePowerPairSupportUpTo
        (cfzp040CarrierCellNaturalLeft W c n) :=
      (Finset.mem_sdiff.mp hblock).2
    have hpk_gt_left : cfzp040CarrierCellNaturalLeft W c n < pk.1 := by
      by_contra hnot
      have hpk_le_left : pk.1 ≤ cfzp040CarrierCellNaturalLeft W c n :=
        Nat.le_of_not_gt hnot
      have hleft_mem : pk ∈ pascalPrimePowerPairSupportUpTo
          (cfzp040CarrierCellNaturalLeft W c n) := by
        rw [mem_pascalPrimePowerPairSupportUpTo_iff]
        refine ⟨mem_pascalPrimeCoordinateSupportUpTo_iff.mpr
          ⟨hp, hpk_le_left⟩, ?_, ?_⟩
        · have hA2 : 2 ≤ cfzp040CarrierCellNaturalLeft W c n :=
            hp.two_le.trans hpk_le_left
          omega
        · simpa [hzero] using hpk_le_left
      exact hleft hleft_mem
    have hraw : pk.1 ∈ cfzp040RawPrimeCarrierCellSupport W c n := by
      change pk.1 ∈ (Finset.Ioc
        (cfzp040CarrierCellNaturalLeft W c n)
        (cfzp040CarrierCellNaturalRight W c n)).filter Nat.Prime
      exact Finset.mem_filter.mpr ⟨
        Finset.mem_Ioc.mpr ⟨hpk_gt_left, hcoord.2⟩, hp⟩
    have hlog := (cfzp040RawPrimeCarrierCellSupport_mem_iff hp).mp hraw
    have hlate : 3 * ε ≤ cfzp039CarrierCellLeft W c n ∧
        1 ≤ cfzp039CarrierCellLeft W c n := max_le_iff.mp hcell
    have heligible : Cfzp034PrimeAxisMassEligible ε pk.1 :=
      ⟨le_trans hlate.1 hlog.2.1.le,
        le_trans hlate.2 hlog.2.1.le⟩
    exact Finset.mem_filter.mpr ⟨hpk, heligible⟩
  · intro pk hpk
    exact (Finset.mem_filter.mp hpk).1

/-- The exceptional prime-axis support is empty in every radial-late cell. -/
theorem cfzp044ExceptionalPrimeAxisPairBlockSupport_eq_empty
    {ε : ℝ}
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hcell : max (3 * ε) 1 ≤ cfzp039CarrierCellLeft W c n) :
    cfzp034ExceptionalPrimeAxisPairBlockSupport ε
        (cfzp040CarrierCellNaturalLeft W c n)
        (cfzp040CarrierCellNaturalRight W c n) = ∅ := by
  classical
  have hEq := cfzp044PrimeAxisBlockSupport_eq_eligible W c n hcell
  apply Finset.eq_empty_of_forall_notMem
  intro pk hpk
  have hbad := (Finset.mem_filter.mp hpk).2
  have haxis := (Finset.mem_filter.mp hpk).1
  rw [hEq] at haxis
  exact hbad (Finset.mem_filter.mp haxis).2

/-- The corresponding exceptional reference mass is exactly zero. -/
theorem cfzp044ExceptionalPrimeAxisReferenceMass_eq_zero
    {ε : ℝ}
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hcell : max (3 * ε) 1 ≤ cfzp039CarrierCellLeft W c n) :
    cfzp034ExceptionalPrimeAxisReferenceMass ε W
        (cfzp040CarrierCellNaturalLeft W c n)
        (cfzp040CarrierCellNaturalRight W c n) = 0 := by
  unfold cfzp034ExceptionalPrimeAxisReferenceMass
  rw [cfzp044ExceptionalPrimeAxisPairBlockSupport_eq_empty W c n hcell]
  simp

/-! ## Gate C: finite one-period integrability compression -/

private theorem cfzp044Carrier_continuous
    {ε : ℝ} (hε : ε ≠ 0)
    (W : PascalCenteredXiResidueTransportWindow) (c : ℝ) :
    Continuous (fun t =>
      Real.exp (cfzp039PrimeAxisGrowthExponent W * t) *
        cfzp036PrimeAxisLeadingPeriodicCarrier ε W (c + t)) := by
  have hcarrier : Continuous
      (fun t => cfzp036PrimeAxisLeadingPeriodicCarrier ε W (c + t)) := by
    rw [show (fun t => cfzp036PrimeAxisLeadingPeriodicCarrier ε W (c + t)) =
        (fun t =>
          (cfzp036LeadingSinCoeffNumerator ε W *
              Real.sin (W.rectangle.T * (c + t)) +
            cfzp036LeadingCosCoeffNumerator ε W *
              Real.cos (W.rectangle.T * (c + t))) / ε) by
      funext t
      exact cfzp036PrimeAxisLeadingPeriodicCarrier_eq_sin_cos_pair
        (ε := ε) (u := c + t) hε W]
    fun_prop
  fun_prop

/-- The unperturbed carrier is integrable on one finite period. -/
theorem cfzp044ExponentialCarrier_intervalIntegrable
    {ε : ℝ} (hε : ε ≠ 0)
    (W : PascalCenteredXiResidueTransportWindow) (c : ℝ) :
    IntervalIntegrable
      (fun t => Real.exp (cfzp039PrimeAxisGrowthExponent W * t) *
        cfzp036PrimeAxisLeadingPeriodicCarrier ε W (c + t))
      volume 0 (cfzp036PrimeAxisCarrierPeriod W) := by
  exact (cfzp044Carrier_continuous hε W c).continuousOn.intervalIntegrable

private theorem cfzp044WeightVariationError_continuousOn
    {ε : ℝ} (hε : ε ≠ 0)
    (W : PascalCenteredXiResidueTransportWindow) (c : ℝ) (n : ℕ)
    (hU : 2 ≤ cfzp039CarrierCellLeft W c n) :
    ContinuousOn
      (fun t => Real.exp (cfzp039PrimeAxisGrowthExponent W * t) *
        cfzp036PrimeAxisLeadingPeriodicCarrier ε W (c + t) *
        (cfzp042LogDensityWeight
            (cfzp039CarrierCellLeft W c n + t) -
          cfzp042LogDensityWeight
            (cfzp039CarrierCellLeft W c n)))
      (Set.uIcc (0 : ℝ) (cfzp036PrimeAxisCarrierPeriod W)) := by
  let U := cfzp039CarrierCellLeft W c n
  let P := cfzp036PrimeAxisCarrierPeriod W
  let s : Set ℝ := Set.uIcc (0 : ℝ) P
  have hP : 0 ≤ P := (cfzp036PrimeAxisCarrierPeriod_pos W).le
  have hU0 : 0 < U := lt_of_lt_of_le (by norm_num) hU
  have hlin : ContinuousOn (fun t : ℝ => U + t) s :=
    continuousOn_const.add continuousOn_id
  have hlin_ne : ∀ t ∈ s, U + t ≠ 0 := by
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) P := by
      simpa [s, uIcc_of_le hP] using ht
    exact ne_of_gt (lt_of_lt_of_le hU0 (le_add_of_nonneg_right ht'.1))
  have hq : ContinuousOn (fun t : ℝ =>
      cfzp042LogDensityWeight (U + t)) s := by
    unfold cfzp042LogDensityWeight
    exact (continuousOn_const.div hlin hlin_ne).sub
      (continuousOn_const.div (hlin.pow 2)
        (fun t ht => pow_ne_zero 2 (hlin_ne t ht)))
  have hA : ContinuousOn
      (fun t => Real.exp (cfzp039PrimeAxisGrowthExponent W * t) *
        cfzp036PrimeAxisLeadingPeriodicCarrier ε W (c + t)) s :=
    (cfzp044Carrier_continuous hε W c).continuousOn
  have hdiff : ContinuousOn (fun t : ℝ =>
      cfzp042LogDensityWeight (U + t) -
        cfzp042LogDensityWeight U) s :=
    hq.sub continuousOn_const
  have herror : ContinuousOn (fun t : ℝ =>
      (Real.exp (cfzp039PrimeAxisGrowthExponent W * t) *
        cfzp036PrimeAxisLeadingPeriodicCarrier ε W (c + t)) *
        (cfzp042LogDensityWeight (U + t) -
          cfzp042LogDensityWeight U)) s := hA.mul hdiff
  simpa [U, P, s, mul_assoc] using herror

/-- The varying-weight error is also integrable on one finite period. -/
theorem cfzp044WeightVariationError_intervalIntegrable
    {ε : ℝ} (hε : ε ≠ 0)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hU : 2 ≤ cfzp039CarrierCellLeft W c n) :
    IntervalIntegrable
      (fun t => Real.exp (cfzp039PrimeAxisGrowthExponent W * t) *
        cfzp036PrimeAxisLeadingPeriodicCarrier ε W (c + t) *
        (cfzp042LogDensityWeight
            (cfzp039CarrierCellLeft W c n + t) -
          cfzp042LogDensityWeight
            (cfzp039CarrierCellLeft W c n)))
      volume 0 (cfzp036PrimeAxisCarrierPeriod W) := by
  exact (cfzp044WeightVariationError_continuousOn hε W c n hU).intervalIntegrable

/-! ## Gate D: explicit smooth margin -/

/-- The positive finite smooth margin supplied by CFZP-043. -/
noncomputable def cfzp044ExplicitSmoothMargin
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) : ℝ :=
  Real.exp (cfzp039PrimeAxisGrowthExponent W *
      cfzp039CarrierCellLeft W c n) *
    (cfzp039ExponentialCarrierPeriodTransform ε W c /
      (4 * cfzp039CarrierCellLeft W c n))

/-- A positive transform and a radial-late cell give a positive smooth margin. -/
theorem cfzp044ExplicitSmoothMargin_pos
    {ε : ℝ} (_hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hM : 0 < cfzp039ExponentialCarrierPeriodTransform ε W c)
    (hLate : cfzp044RadialLateThreshold ε W c ≤
      cfzp039CarrierCellLeft W c n) :
    0 < cfzp044ExplicitSmoothMargin ε W c n := by
  have hU := cfzp044_two_le_of_radialLate hLate
  have hU0 : 0 < cfzp039CarrierCellLeft W c n :=
    lt_of_lt_of_le (by norm_num) hU
  unfold cfzp044ExplicitSmoothMargin
  exact mul_pos (Real.exp_pos _) (div_pos hM
    (mul_pos (by norm_num) hU0))

/-- The explicit margin is bounded by the 042 smooth Abel cell.  Only the
    finite smooth/log-cell bridge remains an external premise. -/
theorem cfzp044_explicitSmoothMargin_le_smoothCell
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hM : 0 < cfzp039ExponentialCarrierPeriodTransform ε W c)
    (hLate : cfzp044RadialLateThreshold ε W c ≤
      cfzp039CarrierCellLeft W c n)
    (hSmoothLog :
      cfzp040SmoothAbelCarrierModel ε W
          (cfzp040CarrierCellExpLeft W c n)
          (cfzp040CarrierCellExpRight W c n) =
        cfzp042SmoothLogCellIntegral ε W c n) :
    cfzp044ExplicitSmoothMargin ε W c n ≤
      cfzp040SmoothAbelCarrierModel ε W
        (cfzp040CarrierCellExpLeft W c n)
        (cfzp040CarrierCellExpRight W c n) := by
  have hSmooth := cfzp044_smoothThreshold_le_of_radialLate hLate
  have hU := cfzp044_two_le_of_radialLate hLate
  have hA := cfzp044ExponentialCarrier_intervalIntegrable hε.ne' W c
  have hE := cfzp044WeightVariationError_intervalIntegrable
    hε.ne' W c n hU
  have hmargin := cfzp043_exp_transform_div_four_le_smoothCell
    hε W c n hM hSmooth hSmoothLog hA hE
  simpa [cfzp044ExplicitSmoothMargin] using hmargin

/-! ## Gate E: the finite explicit-margin budget -/

/-- The one-cell radial budget after the late exceptional axis has vanished. -/
def Cfzp044ExplicitSmoothMarginBudgetAt
    (ε η D : ℝ)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) : Prop :=
  pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W
      (cfzp040CarrierCellNaturalLeft W c n) +
    cfzp039PrimeAxisRemainderCellDebt ε W c n
      (cfzp040CarrierCellNaturalLeft W c n)
      (cfzp040CarrierCellNaturalRight W c n) +
    cfzp034HigherPowerReferenceMass ε W
      (cfzp040CarrierCellNaturalLeft W c n)
      (cfzp040CarrierCellNaturalRight W c n) + D ≤
    cfzp044ExplicitSmoothMargin ε W c n + η

/-! ## Gate F: explicit smooth margin to radial endpoint -/

/-- The explicit smooth-margin budget feeds the existing finite radial
    reservoir theorem.  Discrepancy regularity remains caller-supplied. -/
theorem cfzp044ExplicitSmoothMarginBudget_implies_radialContactDeficit_le
    {ε η D : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hM : 0 < cfzp039ExponentialCarrierPeriodTransform ε W c)
    (hLate : cfzp044RadialLateThreshold ε W c ≤
      cfzp039CarrierCellLeft W c n)
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
    (hbudget : Cfzp044ExplicitSmoothMarginBudgetAt ε η D W c n) :
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W
      (cfzp040CarrierCellNaturalRight W c n) ≤ η := by
  have hcell := cfzp044_eligibilityThreshold_le_of_radialLate hLate
  have hmargin := cfzp044_explicitSmoothMargin_le_smoothCell
    hε W c n hM hLate hSmoothLog
  have hexception := cfzp044ExceptionalPrimeAxisReferenceMass_eq_zero
    W c n hcell
  have hreservoir :
      pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W
          (cfzp040CarrierCellNaturalLeft W c n) +
        cfzp039PrimeAxisRemainderCellDebt ε W c n
          (cfzp040CarrierCellNaturalLeft W c n)
          (cfzp040CarrierCellNaturalRight W c n) +
        cfzp034ExceptionalPrimeAxisReferenceMass ε W
          (cfzp040CarrierCellNaturalLeft W c n)
          (cfzp040CarrierCellNaturalRight W c n) +
        cfzp034HigherPowerReferenceMass ε W
          (cfzp040CarrierCellNaturalLeft W c n)
          (cfzp040CarrierCellNaturalRight W c n) + D ≤
      cfzp040SmoothAbelCarrierModel ε W
          (cfzp040CarrierCellExpLeft W c n)
          (cfzp040CarrierCellExpRight W c n) + η := by
    unfold Cfzp044ExplicitSmoothMarginBudgetAt at hbudget
    rw [hexception]
    linarith
  exact cfzp041SmoothDiscrepancyCellReservoir_implies_radialContactDeficit_le
    hε hε2 W c n hcell hf_diff hf_int hM_int hD_int hD hreservoir

/-! ## Gate G: cofinal budget interface and explicit boundaries -/

/-- Interface for a supplied finite discrepancy/budget provider on a positive
    phase.  This predicate does not assert that such a provider exists. -/
def Cfzp044CofinalExplicitSmoothMarginBudget
    (ε η : ℝ)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) : Prop :=
  ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ∃ D : ℝ,
    Cfzp041PrimeCountingDiscrepancyFunctionalBoundAt ε W c n D ∧
    Cfzp044ExplicitSmoothMarginBudgetAt ε η D W c n

inductive Cfzp044PrimeAxisExplicitSmoothMarginRadialBudgetGap : Prop
  | noAutomaticInteriorStripWindowProvider
  | noAutomaticSmoothAbelLogCellReadinessProvider
  | noPrimeCountingDiscrepancyFunctionalDecayProvider
  | noPointwiseDiscrepancyToFunctionalBound
  | noHigherPrimePowerResidualDomination
  | noCofinalExplicitMarginBudgetProvider

end DkMath.RH.CFBRCProjection
