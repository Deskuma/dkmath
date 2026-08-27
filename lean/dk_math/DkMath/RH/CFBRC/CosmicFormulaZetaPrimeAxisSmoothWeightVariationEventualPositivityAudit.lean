/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.RH.CFBRC.CosmicFormulaZetaPrimeAxisSmoothDensityLogCoordinateTransformAudit
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CosmicFormulaZetaPrimeAxisSmoothWeightVariationEventualPositivityAudit"

/-!
# CFZP-043: smooth weight variation and eventual positivity

This module keeps the quantitative argument finite.  The discrepancy and
prime-power residuals remain named inputs from the preceding modules.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.NumberTheory
open MeasureTheory
open Set

/-! ## Gate A: late logarithmic density -/

/-- The smooth logarithmic density is positive beyond the first unit scale. -/
theorem cfzp043LogDensityWeight_pos
    {u : ℝ} (hu : 1 < u) :
    0 < cfzp042LogDensityWeight u := by
  rw [cfzp042LogDensityWeight]
  have hu0 : 0 < u := lt_trans (by norm_num) hu
  have hu_ne : u ≠ 0 := ne_of_gt hu0
  field_simp [hu_ne]
  nlinarith

/-- A convenient reciprocal lower bound for the density in the late region. -/
theorem cfzp043_half_inv_le_logDensityWeight
    {u : ℝ} (hu : 2 ≤ u) :
    1 / (2 * u) ≤ cfzp042LogDensityWeight u := by
  rw [cfzp042LogDensityWeight]
  have hu0 : 0 < u := lt_of_lt_of_le (by norm_num) hu
  have hu_ne : u ≠ 0 := ne_of_gt hu0
  field_simp [hu_ne]
  nlinarith

/-- Pointwise `U⁻²` control of the density variation on a forward interval. -/
theorem cfzp043_logDensityWeight_variation_le
    {U t : ℝ} (hU : 2 ≤ U) (ht : 0 ≤ t) :
    |cfzp042LogDensityWeight (U + t) -
        cfzp042LogDensityWeight U| ≤ t / U ^ 2 := by
  have hU0 : 0 < U := lt_of_lt_of_le (by norm_num) hU
  have hUt0 : 0 < U + t := lt_of_lt_of_le hU0 (le_add_of_nonneg_right ht)
  have hU_ne : U ≠ 0 := ne_of_gt hU0
  have hUt_ne : U + t ≠ 0 := ne_of_gt hUt0
  rw [abs_le]
  unfold cfzp042LogDensityWeight
  constructor <;>
    field_simp [hU_ne, hUt_ne] <;>
    ring_nf at * <;>
    nlinarith [sq_nonneg U, sq_nonneg (U + t),
      mul_nonneg ht (sub_nonneg.mpr hU)]

/-- The pointwise variation bound with the whole carrier period as budget. -/
theorem cfzp043_logDensityWeight_variation_le_period
    {U t P : ℝ} (hU : 2 ≤ U) (ht : 0 ≤ t) (htP : t ≤ P) :
    |cfzp042LogDensityWeight (U + t) -
        cfzp042LogDensityWeight U| ≤ P / U ^ 2 := by
  have hpoint := cfzp043_logDensityWeight_variation_le hU ht
  have hU0 : 0 < U := lt_of_lt_of_le (by norm_num) hU
  have hU2 : 0 ≤ U ^ 2 := sq_nonneg U
  have hU2ne : U ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hU0)
  calc
    |cfzp042LogDensityWeight (U + t) -
        cfzp042LogDensityWeight U| ≤ t / U ^ 2 := hpoint
    _ ≤ P / U ^ 2 := by
      exact (div_le_div_of_nonneg_right htP hU2)

/-! ## Gate B: finite absolute carrier moment -/

/-- The absolute exponential-carrier mass over one period. -/
noncomputable def cfzp043ExponentialCarrierAbsMoment
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..cfzp036PrimeAxisCarrierPeriod W,
    |Real.exp (cfzp039PrimeAxisGrowthExponent W * t) *
      cfzp036PrimeAxisLeadingPeriodicCarrier ε W (c + t)|

/-- The finite absolute moment is nonnegative. -/
theorem cfzp043ExponentialCarrierAbsMoment_nonneg
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (c : ℝ) :
    0 ≤ cfzp043ExponentialCarrierAbsMoment ε W c := by
  unfold cfzp043ExponentialCarrierAbsMoment
  apply intervalIntegral.integral_nonneg_of_ae
    (cfzp036PrimeAxisCarrierPeriod_pos W).le
  exact Filter.Eventually.of_forall (fun t => abs_nonneg _)

private theorem cfzp043Carrier_continuous
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

theorem cfzp043ExponentialCarrierAbsMoment_intervalIntegrable
    {ε : ℝ} (hε : ε ≠ 0)
    (W : PascalCenteredXiResidueTransportWindow) (c : ℝ) :
    IntervalIntegrable
      (fun t => |Real.exp (cfzp039PrimeAxisGrowthExponent W * t) *
        cfzp036PrimeAxisLeadingPeriodicCarrier ε W (c + t)|)
      volume 0 (cfzp036PrimeAxisCarrierPeriod W) := by
  exact (cfzp043Carrier_continuous hε W c).abs.continuousOn.intervalIntegrable

/-! ## Gate C: the finite `U⁻²` variation bound -/

/-- The finite coefficient multiplying the late-coordinate `U⁻²` error. -/
noncomputable def cfzp043SmoothWeightVariationConstant
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) : ℝ :=
  cfzp036PrimeAxisCarrierPeriod W *
    cfzp043ExponentialCarrierAbsMoment ε W c

private theorem cfzp043SmoothWeightVariationError_intervalIntegrable
    {ε : ℝ} (hε : ε ≠ 0)
    (W : PascalCenteredXiResidueTransportWindow) (c : ℝ) (n : ℕ)
    (hU : 2 ≤ cfzp039CarrierCellLeft W c n) :
    IntervalIntegrable
      (fun t => Real.exp (cfzp039PrimeAxisGrowthExponent W * t) *
        cfzp036PrimeAxisLeadingPeriodicCarrier ε W (c + t) *
        (cfzp042LogDensityWeight
            (cfzp039CarrierCellLeft W c n + t) -
          cfzp042LogDensityWeight
            (cfzp039CarrierCellLeft W c n)))
      volume 0 (cfzp036PrimeAxisCarrierPeriod W) := by
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
    (cfzp043Carrier_continuous hε W c).continuousOn
  have hdiff : ContinuousOn (fun t : ℝ =>
      cfzp042LogDensityWeight (U + t) -
        cfzp042LogDensityWeight U) s :=
    hq.sub continuousOn_const
  have herror : ContinuousOn (fun t : ℝ =>
      (Real.exp (cfzp039PrimeAxisGrowthExponent W * t) *
        cfzp036PrimeAxisLeadingPeriodicCarrier ε W (c + t)) *
        (cfzp042LogDensityWeight (U + t) -
          cfzp042LogDensityWeight U)) s := hA.mul hdiff
  simpa [U, P, s, mul_assoc] using herror.intervalIntegrable

/-- The 042 weight-variation error is bounded by the finite moment budget. -/
theorem cfzp043SmoothWeightVariationError_abs_le
    {ε : ℝ} (hε : ε ≠ 0)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hU : 2 ≤ cfzp039CarrierCellLeft W c n) :
    |cfzp042SmoothWeightVariationError ε W c n| ≤
      (cfzp036PrimeAxisCarrierPeriod W /
          (cfzp039CarrierCellLeft W c n) ^ 2) *
        cfzp043ExponentialCarrierAbsMoment ε W c := by
  let U := cfzp039CarrierCellLeft W c n
  let P := cfzp036PrimeAxisCarrierPeriod W
  let A : ℝ → ℝ := fun t =>
    Real.exp (cfzp039PrimeAxisGrowthExponent W * t) *
      cfzp036PrimeAxisLeadingPeriodicCarrier ε W (c + t)
  let qdiff : ℝ → ℝ := fun t =>
    cfzp042LogDensityWeight (U + t) - cfzp042LogDensityWeight U
  have hP : 0 ≤ P := (cfzp036PrimeAxisCarrierPeriod_pos W).le
  have hPpos : 0 ≤ (0 : ℝ) := by norm_num
  have hAabs_int : IntervalIntegrable (fun t => |A t|) volume 0 P := by
    simpa [A, P] using
      cfzp043ExponentialCarrierAbsMoment_intervalIntegrable hε W c
  have hErr_int : IntervalIntegrable (fun t => A t * qdiff t)
      volume 0 P := by
    simpa [A, qdiff, U, P, mul_assoc] using
      cfzp043SmoothWeightVariationError_intervalIntegrable hε W c n hU
  have hpoint : ∀ t ∈ Set.Icc (0 : ℝ) P,
      |A t * qdiff t| ≤ (P / U ^ 2) * |A t| := by
    intro t ht
    have hvar := cfzp043_logDensityWeight_variation_le_period
      hU ht.1 ht.2
    calc
      |A t * qdiff t| = |A t| * |qdiff t| := abs_mul _ _
      _ ≤ |A t| * (P / U ^ 2) :=
        mul_le_mul_of_nonneg_left hvar (abs_nonneg _)
      _ = (P / U ^ 2) * |A t| := by ring
  have hmono :
      (∫ t in (0 : ℝ)..P, |A t * qdiff t|) ≤
        ∫ t in (0 : ℝ)..P, (P / U ^ 2) * |A t| := by
    apply intervalIntegral.integral_mono_on hP
      hErr_int.abs (hAabs_int.const_mul (P / U ^ 2))
    exact hpoint
  have habs :
      |∫ t in (0 : ℝ)..P, A t * qdiff t| ≤
        ∫ t in (0 : ℝ)..P, |A t * qdiff t| :=
    intervalIntegral.abs_integral_le_integral_abs hP
  calc
    |cfzp042SmoothWeightVariationError ε W c n| =
        |∫ t in (0 : ℝ)..P, A t * qdiff t| := by
          rfl
    _ ≤ ∫ t in (0 : ℝ)..P, |A t * qdiff t| := habs
    _ ≤ ∫ t in (0 : ℝ)..P, (P / U ^ 2) * |A t| := hmono
    _ = (P / U ^ 2) *
        cfzp043ExponentialCarrierAbsMoment ε W c := by
      rw [intervalIntegral.integral_const_mul]
      rfl

/-! ## Gates D--E: an explicit smooth-cell margin -/

/-- The late-coordinate threshold at which the positive carrier dominates the
    finite weight-variation error.  It is only used when the transform in the
    denominator is known to be positive. -/
noncomputable def cfzp043SmoothPositivityThreshold
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) : ℝ :=
  max 2 (4 * cfzp043SmoothWeightVariationConstant ε W c /
    cfzp039ExponentialCarrierPeriodTransform ε W c)

/-- The exact finite 042 split gives the advertised `M/(4U)` lower margin.

    The hypotheses `hcell`, `hA_int`, and `hE_int` are intentionally retained:
    they are the local analytic readiness data needed by the preceding change
    of variables, and are not supplied automatically by this theorem. -/
theorem cfzp043_exp_transform_div_four_le_smoothCell
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hM : 0 < cfzp039ExponentialCarrierPeriodTransform ε W c)
    (hLate : cfzp043SmoothPositivityThreshold ε W c ≤
      cfzp039CarrierCellLeft W c n)
    (hcell :
      cfzp040SmoothAbelCarrierModel ε W
          (cfzp040CarrierCellExpLeft W c n)
          (cfzp040CarrierCellExpRight W c n) =
        cfzp042SmoothLogCellIntegral ε W c n)
    (hA_int : IntervalIntegrable
      (fun t => Real.exp (cfzp039PrimeAxisGrowthExponent W * t) *
        cfzp036PrimeAxisLeadingPeriodicCarrier ε W (c + t))
      volume 0 (cfzp036PrimeAxisCarrierPeriod W))
    (hE_int : IntervalIntegrable
      (fun t => Real.exp (cfzp039PrimeAxisGrowthExponent W * t) *
        cfzp036PrimeAxisLeadingPeriodicCarrier ε W (c + t) *
        (cfzp042LogDensityWeight
            (cfzp039CarrierCellLeft W c n + t) -
          cfzp042LogDensityWeight
            (cfzp039CarrierCellLeft W c n)))
      volume 0 (cfzp036PrimeAxisCarrierPeriod W)) :
    Real.exp (cfzp039PrimeAxisGrowthExponent W *
        cfzp039CarrierCellLeft W c n) *
      (cfzp039ExponentialCarrierPeriodTransform ε W c /
        (4 * cfzp039CarrierCellLeft W c n)) ≤
      cfzp040SmoothAbelCarrierModel ε W
        (cfzp040CarrierCellExpLeft W c n)
        (cfzp040CarrierCellExpRight W c n) := by
  let U := cfzp039CarrierCellLeft W c n
  let β := cfzp039PrimeAxisGrowthExponent W
  let M := cfzp039ExponentialCarrierPeriodTransform ε W c
  let C := cfzp043SmoothWeightVariationConstant ε W c
  have hLate' : max 2 (4 * C / M) ≤ U := by
    simpa [cfzp043SmoothPositivityThreshold, C, U, M] using hLate
  have hU : 2 ≤ U := by
    exact le_trans (le_max_left _ _) hLate'
  have hU0 : 0 < U := lt_of_lt_of_le (by norm_num) hU
  have hC : 0 ≤ C := by
    dsimp [C, cfzp043SmoothWeightVariationConstant]
    exact mul_nonneg (cfzp036PrimeAxisCarrierPeriod_pos W).le
      (cfzp043ExponentialCarrierAbsMoment_nonneg ε W c)
  have hthreshold : 4 * C / M ≤ U := by
    exact le_trans (le_max_right _ _) hLate'
  have hCM : 4 * C ≤ M * U := by
    simpa [mul_comm] using (div_le_iff₀ hM).mp hthreshold
  have hCMU : (4 * C) * U ≤ (M * U) * U :=
    mul_le_mul_of_nonneg_right hCM hU0.le
  have hCU : C / U ^ 2 ≤ M / (4 * U) := by
    field_simp [ne_of_gt hU0]
    nlinarith [hCMU]
  have herror := cfzp043SmoothWeightVariationError_abs_le
    hε.ne' W c n hU
  have herror' :
      |cfzp042SmoothWeightVariationError ε W c n| ≤ C / U ^ 2 := by
    simpa [C, U, cfzp043SmoothWeightVariationConstant, mul_comm,
      mul_left_comm, mul_assoc, div_eq_mul_inv] using herror
  have herror_lower :
      -(C / U ^ 2) ≤ cfzp042SmoothWeightVariationError ε W c n := by
    have hneg := neg_abs_le (cfzp042SmoothWeightVariationError ε W c n)
    exact le_trans (neg_le_neg herror') hneg
  have hq := cfzp043_half_inv_le_logDensityWeight hU
  have hqM : M / (2 * U) ≤
      cfzp042LogDensityWeight U * M := by
    have h := mul_le_mul_of_nonneg_right hq hM.le
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h
  have hinner : M / (4 * U) ≤
      cfzp042LogDensityWeight U * M +
        cfzp042SmoothWeightVariationError ε W c n := by
    have hdouble : M / (2 * U) = 2 * (M / (4 * U)) := by
      field_simp [ne_of_gt hU0]
      ring
    have hquarter : M / (4 * U) ≤ M / (2 * U) - C / U ^ 2 := by
      rw [hdouble]
      linarith [hCU]
    linarith [hquarter, hqM, herror_lower]
  have hsplit := cfzp042SmoothAbelCell_eq_transform_add_weightError
    hε.ne' W c n hcell hA_int hE_int
  have hsplit' :
      cfzp040SmoothAbelCarrierModel ε W
          (cfzp040CarrierCellExpLeft W c n)
          (cfzp040CarrierCellExpRight W c n) =
        Real.exp (β * U) *
          (cfzp042LogDensityWeight U * M +
            cfzp042SmoothWeightVariationError ε W c n) := by
    simpa [β, U, M] using hsplit
  calc
    Real.exp (β * U) * (M / (4 * U)) ≤
        Real.exp (β * U) *
          (cfzp042LogDensityWeight U * M +
            cfzp042SmoothWeightVariationError ε W c n) := by
      exact mul_le_mul_of_nonneg_left hinner (Real.exp_pos _).le
    _ = cfzp040SmoothAbelCarrierModel ε W
        (cfzp040CarrierCellExpLeft W c n)
        (cfzp040CarrierCellExpRight W c n) := hsplit'.symm

/-- Strict positivity follows from the same finite explicit margin. -/
theorem cfzp043_smoothCell_pos
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hM : 0 < cfzp039ExponentialCarrierPeriodTransform ε W c)
    (hLate : cfzp043SmoothPositivityThreshold ε W c ≤
      cfzp039CarrierCellLeft W c n)
    (hcell :
      cfzp040SmoothAbelCarrierModel ε W
          (cfzp040CarrierCellExpLeft W c n)
          (cfzp040CarrierCellExpRight W c n) =
        cfzp042SmoothLogCellIntegral ε W c n)
    (hA_int : IntervalIntegrable
      (fun t => Real.exp (cfzp039PrimeAxisGrowthExponent W * t) *
        cfzp036PrimeAxisLeadingPeriodicCarrier ε W (c + t))
      volume 0 (cfzp036PrimeAxisCarrierPeriod W))
    (hE_int : IntervalIntegrable
      (fun t => Real.exp (cfzp039PrimeAxisGrowthExponent W * t) *
        cfzp036PrimeAxisLeadingPeriodicCarrier ε W (c + t) *
        (cfzp042LogDensityWeight
            (cfzp039CarrierCellLeft W c n + t) -
          cfzp042LogDensityWeight
            (cfzp039CarrierCellLeft W c n)))
      volume 0 (cfzp036PrimeAxisCarrierPeriod W)) :
    0 < cfzp040SmoothAbelCarrierModel ε W
        (cfzp040CarrierCellExpLeft W c n)
        (cfzp040CarrierCellExpRight W c n) := by
  have hmargin := cfzp043_exp_transform_div_four_le_smoothCell
    hε W c n hM hLate hcell hA_int hE_int
  have hLate' : max 2 (4 *
      cfzp043SmoothWeightVariationConstant ε W c /
        cfzp039ExponentialCarrierPeriodTransform ε W c) ≤
      cfzp039CarrierCellLeft W c n := by
    simpa [cfzp043SmoothPositivityThreshold] using hLate
  have hU : 0 < cfzp039CarrierCellLeft W c n :=
    lt_of_lt_of_le (by norm_num)
      (le_trans (le_max_left _ _) hLate')
  have hpos : 0 <
      Real.exp (cfzp039PrimeAxisGrowthExponent W *
        cfzp039CarrierCellLeft W c n) *
        (cfzp039ExponentialCarrierPeriodTransform ε W c /
          (4 * cfzp039CarrierCellLeft W c n)) := by
    exact mul_pos (Real.exp_pos _) (div_pos hM
      (mul_pos (by norm_num) hU))
  exact lt_of_lt_of_le hpos hmargin

/-! ## Gate F: positive phase and cofinal late cells -/

/-- Every fixed real threshold is eventually below the translated carrier
    cell-left coordinates.  This is only the Archimedean property plus the
    positivity of the carrier period. -/
theorem cfzp043_carrierCellLeft_eventually_ge
    (W : PascalCenteredXiResidueTransportWindow)
    (c K : ℝ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      K ≤ cfzp039CarrierCellLeft W c n := by
  have hP : 0 < cfzp036PrimeAxisCarrierPeriod W :=
    cfzp036PrimeAxisCarrierPeriod_pos W
  obtain ⟨N, hN⟩ := exists_nat_gt ((K - c) /
    cfzp036PrimeAxisCarrierPeriod W)
  refine ⟨N, ?_⟩
  intro n hn
  have hnN : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hNP : K - c < (N : ℝ) *
      cfzp036PrimeAxisCarrierPeriod W := by
    have := (div_lt_iff₀ hP).mp hN
    simpa [mul_comm] using this
  have hmono : (N : ℝ) * cfzp036PrimeAxisCarrierPeriod W ≤
      (n : ℝ) * cfzp036PrimeAxisCarrierPeriod W :=
    mul_le_mul_of_nonneg_right hnN hP.le
  unfold cfzp039CarrierCellLeft
  linarith

/-- The positive transform phase supplied by CFZP-039 has cofinally many
    cells above its explicit smooth-positivity threshold. -/
theorem cfzp043_exists_positive_transform_cofinal_cells
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow)
    (hstrip : Cfzp039PrimeAxisInteriorStrip W) :
    ∃ (c : ℝ) (N : ℕ), 0 < cfzp039ExponentialCarrierPeriodTransform ε W c ∧
      ∀ n : ℕ, N ≤ n →
        cfzp043SmoothPositivityThreshold ε W c ≤
          cfzp039CarrierCellLeft W c n := by
  obtain ⟨c, hc⟩ := cfzp039ExponentialCarrierPeriodTransform_exists_pos
    hε W hstrip
  obtain ⟨N, hN⟩ := cfzp043_carrierCellLeft_eventually_ge W c
    (cfzp043SmoothPositivityThreshold ε W c)
  exact ⟨c, N, hc, hN⟩

/-! ## Explicit quantitative boundaries -/

inductive Cfzp043PrimeAxisSmoothWeightVariationEventualPositivityGap : Prop
  | noAutomaticInteriorStripWindowProvider
  | noAutomaticSmoothCellAnalyticReadinessProvider
  | noPrimeCountingDiscrepancyFunctionalDecayProvider
  | noPointwiseDiscrepancyToFunctionalBound
  | noExceptionalPrimeAxisResidualElimination
  | noHigherPrimePowerResidualElimination

end DkMath.RH.CFBRCProjection
