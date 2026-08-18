/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.RH.CFBRC.CosmicFormulaZetaPrimeAxisCombinedDiscrepancyEnvelopeAudit
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CosmicFormulaZetaPrimeAxisCombinedDiscrepancySensitivityEnvelopeAudit"

/-!
# CFZP-050: an explicit finite sensitivity envelope

This file makes the finite coefficient in the CFZP-049 discrepancy bound
explicit.  The hypotheses named `...Envelope` below are finite, cell-local
certificates.  They deliberately do not assert a prime-distribution
asymptotic, a limit exchange, or a global RH statement.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.NumberTheory
open MeasureTheory
open Set

/-! ## Gate A: finite carrier constants -/

/-- The triangle-inequality constant for the leading periodic carrier. -/
noncomputable def cfzp050LeadingCarrierAbsConstant
    (epsilon : ℝ) (W : PascalCenteredXiResidueTransportWindow) : ℝ :=
  (abs (cfzp036LeadingSinCoeffNumerator epsilon W) +
      abs (cfzp036LeadingCosCoeffNumerator epsilon W)) / epsilon

/-- The corresponding coordinate-derivative constant. -/
noncomputable def cfzp050LeadingCarrierDerivativeAbsConstant
    (epsilon : ℝ) (W : PascalCenteredXiResidueTransportWindow) : ℝ :=
  W.rectangle.T *
    (abs (cfzp036LeadingSinCoeffNumerator epsilon W) +
      abs (cfzp036LeadingCosCoeffNumerator epsilon W)) / epsilon

theorem cfzp050LeadingCarrierAbsConstant_nonneg
    {epsilon : ℝ} (hε : 0 < epsilon)
    (W : PascalCenteredXiResidueTransportWindow) :
    0 ≤ cfzp050LeadingCarrierAbsConstant epsilon W := by
  unfold cfzp050LeadingCarrierAbsConstant
  exact div_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) hε.le

theorem cfzp050LeadingCarrierDerivativeAbsConstant_nonneg
    {epsilon : ℝ} (hε : 0 < epsilon)
    (W : PascalCenteredXiResidueTransportWindow) :
    0 ≤ cfzp050LeadingCarrierDerivativeAbsConstant epsilon W := by
  unfold cfzp050LeadingCarrierDerivativeAbsConstant
  exact div_nonneg
    (mul_nonneg W.rectangle.hT.le
      (add_nonneg (abs_nonneg _) (abs_nonneg _))) hε.le

/-- The leading carrier is bounded uniformly in its phase coordinate. -/
theorem cfzp050LeadingPeriodicCarrier_abs_le
    {epsilon u : ℝ} (hε : 0 < epsilon)
    (W : PascalCenteredXiResidueTransportWindow) :
    abs (cfzp036PrimeAxisLeadingPeriodicCarrier epsilon W u) ≤
      cfzp050LeadingCarrierAbsConstant epsilon W := by
  rw [cfzp036PrimeAxisLeadingPeriodicCarrier_eq_sin_cos_pair hε.ne' W]
  unfold cfzp050LeadingCarrierAbsConstant
  have hs : abs (Real.sin (W.rectangle.T * u)) ≤ (1 : ℝ) :=
    Real.abs_sin_le_one _
  have hc : abs (Real.cos (W.rectangle.T * u)) ≤ (1 : ℝ) :=
    Real.abs_cos_le_one _
  have hnum :
      abs (cfzp036LeadingSinCoeffNumerator epsilon W *
          Real.sin (W.rectangle.T * u) +
        cfzp036LeadingCosCoeffNumerator epsilon W *
          Real.cos (W.rectangle.T * u)) ≤
      abs (cfzp036LeadingSinCoeffNumerator epsilon W) +
        abs (cfzp036LeadingCosCoeffNumerator epsilon W) := by
    calc
      _ ≤ abs (cfzp036LeadingSinCoeffNumerator epsilon W *
          Real.sin (W.rectangle.T * u)) +
          abs (cfzp036LeadingCosCoeffNumerator epsilon W *
            Real.cos (W.rectangle.T * u)) := abs_add_le _ _
      _ = abs (cfzp036LeadingSinCoeffNumerator epsilon W) *
          abs (Real.sin (W.rectangle.T * u)) +
          abs (cfzp036LeadingCosCoeffNumerator epsilon W) *
            abs (Real.cos (W.rectangle.T * u)) := by rw [abs_mul, abs_mul]
      _ ≤ _ := by
        exact add_le_add
          (by simpa using
            (mul_le_mul_of_nonneg_left hs
              (abs_nonneg (cfzp036LeadingSinCoeffNumerator epsilon W))))
          (by simpa using
            (mul_le_mul_of_nonneg_left hc
              (abs_nonneg (cfzp036LeadingCosCoeffNumerator epsilon W))))
  rw [abs_div, abs_of_pos hε]
  exact (div_le_div_of_nonneg_right hnum hε.le)

/-- The coordinate derivative has the analogous finite uniform bound. -/
theorem cfzp050LeadingCarrierDerivative_abs_le
    {epsilon u : ℝ} (hε : 0 < epsilon)
    (W : PascalCenteredXiResidueTransportWindow) :
    abs (cfzp040LeadingCarrierDerivative epsilon W u) ≤
      cfzp050LeadingCarrierDerivativeAbsConstant epsilon W := by
  unfold cfzp040LeadingCarrierDerivative
    cfzp050LeadingCarrierDerivativeAbsConstant
  rw [abs_mul, abs_div, abs_of_pos W.rectangle.hT, abs_of_pos hε]
  have hs : abs (Real.sin (W.rectangle.T * u)) ≤ (1 : ℝ) :=
    Real.abs_sin_le_one _
  have hc : abs (Real.cos (W.rectangle.T * u)) ≤ (1 : ℝ) :=
    Real.abs_cos_le_one _
  have hpair :
      abs (cfzp036LeadingSinCoeffNumerator epsilon W *
          Real.cos (W.rectangle.T * u) -
        cfzp036LeadingCosCoeffNumerator epsilon W *
          Real.sin (W.rectangle.T * u)) ≤
      abs (cfzp036LeadingSinCoeffNumerator epsilon W) +
        abs (cfzp036LeadingCosCoeffNumerator epsilon W) := by
    calc
      _ ≤ abs (cfzp036LeadingSinCoeffNumerator epsilon W *
          Real.cos (W.rectangle.T * u)) +
          abs (cfzp036LeadingCosCoeffNumerator epsilon W *
            Real.sin (W.rectangle.T * u)) := abs_sub _ _
      _ = abs (cfzp036LeadingSinCoeffNumerator epsilon W) *
          abs (Real.cos (W.rectangle.T * u)) +
          abs (cfzp036LeadingCosCoeffNumerator epsilon W) *
            abs (Real.sin (W.rectangle.T * u)) := by rw [abs_mul, abs_mul]
      _ ≤ _ := by
        exact add_le_add
          (by simpa using
            (mul_le_mul_of_nonneg_left hc
              (abs_nonneg (cfzp036LeadingSinCoeffNumerator epsilon W))))
          (by simpa using
            (mul_le_mul_of_nonneg_left hs
              (abs_nonneg (cfzp036LeadingCosCoeffNumerator epsilon W))))
  have hdiv := div_le_div_of_nonneg_right hpair hε.le
  calc
    W.rectangle.T / epsilon *
        abs (cfzp036LeadingSinCoeffNumerator epsilon W *
          Real.cos (W.rectangle.T * u) -
          cfzp036LeadingCosCoeffNumerator epsilon W *
            Real.sin (W.rectangle.T * u)) =
      W.rectangle.T *
        (abs (cfzp036LeadingSinCoeffNumerator epsilon W *
          Real.cos (W.rectangle.T * u) -
          cfzp036LeadingCosCoeffNumerator epsilon W *
            Real.sin (W.rectangle.T * u)) / epsilon) := by ring
    _ ≤ W.rectangle.T *
        ((abs (cfzp036LeadingSinCoeffNumerator epsilon W) +
          abs (cfzp036LeadingCosCoeffNumerator epsilon W)) / epsilon) :=
      mul_le_mul_of_nonneg_left hdiv W.rectangle.hT.le
    _ = W.rectangle.T *
        (abs (cfzp036LeadingSinCoeffNumerator epsilon W) +
          abs (cfzp036LeadingCosCoeffNumerator epsilon W)) / epsilon := by ring

/-! ## Gates B-E: finite sensitivity certificates -/

/-- A compact finite certificate for a sensitivity envelope.  The endpoint
and derivative bounds are intentionally explicit so that a later analytic
provider can be audited independently of the discrepancy API. -/
structure Cfzp050CellSensitivityEnvelope
    (f : ℝ → ℝ) (a b U sigma C : ℝ) : Prop where
  endpoint_left : |f a| ≤ C * Real.exp (-sigma * U)
  endpoint_right : |f b| ≤ C * Real.exp (-sigma * U)
  derivative_integral :
    ∫ x in Set.Ioc a b, |deriv f x| ≤
      C * Real.exp (-sigma * U) -
        (|f a| + |f b|)

theorem cfzp050FiniteAbelSensitivity_le_of_envelope
    {f : ℝ → ℝ} {a b U sigma C : ℝ}
    (hEnv : Cfzp050CellSensitivityEnvelope f a b U sigma C) :
    cfzp049FiniteAbelSensitivity f a b ≤ C * Real.exp (-sigma * U) := by
  unfold cfzp049FiniteAbelSensitivity
  linarith [hEnv.derivative_integral]

/-- The finite carrier coefficient used after the endpoint and derivative
envelopes have been integrated over one period. -/
noncomputable def cfzp050CarrierSensitivityConstant
    (epsilon : ℝ) (W : PascalCenteredXiResidueTransportWindow) : ℝ :=
  2 * cfzp050LeadingCarrierAbsConstant epsilon W +
    Real.exp (cfzp036PrimeAxisCarrierPeriod W) *
      (W.rectangle.σ * cfzp050LeadingCarrierAbsConstant epsilon W +
        cfzp050LeadingCarrierDerivativeAbsConstant epsilon W)

/-- The coarse finite coefficient for the `1 / log x` remainder. -/
noncomputable def cfzp050RemainderSensitivityConstant
    (W : PascalCenteredXiResidueTransportWindow) : ℝ :=
  2 + Real.exp (cfzp036PrimeAxisCarrierPeriod W) *
    (W.rectangle.σ + 1)

theorem cfzp050CarrierSensitivityConstant_nonneg
    {epsilon : ℝ} (hε : 0 < epsilon)
    (W : PascalCenteredXiResidueTransportWindow) :
    0 ≤ cfzp050CarrierSensitivityConstant epsilon W := by
  unfold cfzp050CarrierSensitivityConstant
  have hσ : 0 ≤ W.rectangle.σ := by
    linarith [cfzp034_rectangleSigma_gt_half W]
  have hC := cfzp050LeadingCarrierAbsConstant_nonneg hε W
  have hD := cfzp050LeadingCarrierDerivativeAbsConstant_nonneg hε W
  exact add_nonneg
    (mul_nonneg (by norm_num) hC)
    (mul_nonneg (Real.exp_pos _).le
      (add_nonneg (mul_nonneg hσ hC) hD))

theorem cfzp050RemainderSensitivityConstant_nonneg
    (W : PascalCenteredXiResidueTransportWindow) :
    0 ≤ cfzp050RemainderSensitivityConstant W := by
  unfold cfzp050RemainderSensitivityConstant
  have hσ : 0 ≤ W.rectangle.σ := by
    linarith [cfzp034_rectangleSigma_gt_half W]
  exact add_nonneg (by norm_num)
    (mul_nonneg (Real.exp_pos _).le (add_nonneg hσ (by norm_num)))

/-- A carrier sensitivity bound from a finite cell envelope certificate. -/
theorem cfzp050CarrierDiscrepancyCellSensitivity_le
    {epsilon : ℝ} (_hε : 0 < epsilon)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hEnv : Cfzp050CellSensitivityEnvelope
      (cfzp040PrimeAxisCarrierTestFunction epsilon W)
      (cfzp040CarrierCellExpLeft W c n)
      (cfzp040CarrierCellExpRight W c n)
      (cfzp039CarrierCellLeft W c n) W.rectangle.σ
      (cfzp050CarrierSensitivityConstant epsilon W)) :
    cfzp049CarrierDiscrepancyCellSensitivity epsilon W c n ≤
      cfzp050CarrierSensitivityConstant epsilon W *
        Real.exp (-W.rectangle.σ * cfzp039CarrierCellLeft W c n) := by
  exact cfzp050FiniteAbelSensitivity_le_of_envelope hEnv

/-- A remainder sensitivity bound from a finite cell envelope certificate. -/
theorem cfzp050RemainderDiscrepancyCellSensitivity_le
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hEnv : Cfzp050CellSensitivityEnvelope
      (cfzp048PrimeAxisRemainderTestFunction W)
      (cfzp040CarrierCellExpLeft W c n)
      (cfzp040CarrierCellExpRight W c n)
      (cfzp039CarrierCellLeft W c n) W.rectangle.σ
      (cfzp050RemainderSensitivityConstant W)) :
    cfzp049RemainderDiscrepancyCellSensitivity W c n ≤
      cfzp050RemainderSensitivityConstant W *
        Real.exp (-W.rectangle.σ * cfzp039CarrierCellLeft W c n) := by
  exact cfzp050FiniteAbelSensitivity_le_of_envelope hEnv

/-! ## Gate E: the combined finite coefficient -/

/-- The carrier coefficient plus the exact CFZP-036 remainder multiplier. -/
noncomputable def cfzp050CombinedSensitivityConstant
    (epsilon : ℝ) (W : PascalCenteredXiResidueTransportWindow) : ℝ :=
  cfzp050CarrierSensitivityConstant epsilon W +
    cfzp036PrimeAxisRemainderConstant epsilon W *
      cfzp050RemainderSensitivityConstant W

theorem cfzp050CombinedSensitivityConstant_nonneg
    {epsilon : ℝ} (hε : 0 < epsilon)
    (W : PascalCenteredXiResidueTransportWindow) :
    0 ≤ cfzp050CombinedSensitivityConstant epsilon W := by
  unfold cfzp050CombinedSensitivityConstant
  exact add_nonneg
    (cfzp050CarrierSensitivityConstant_nonneg hε W)
    (mul_nonneg
      (cfzp036PrimeAxisRemainderConstant_pos hε W).le
      (cfzp050RemainderSensitivityConstant_nonneg W))

/-- The two finite sensitivity bounds combine without changing the cell
scale `exp (-sigma U)`. -/
theorem cfzp050CombinedPrimeCountingDiscrepancySensitivity_le
    {epsilon : ℝ} (hε : 0 < epsilon)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hCarrier : Cfzp050CellSensitivityEnvelope
      (cfzp040PrimeAxisCarrierTestFunction epsilon W)
      (cfzp040CarrierCellExpLeft W c n)
      (cfzp040CarrierCellExpRight W c n)
      (cfzp039CarrierCellLeft W c n) W.rectangle.σ
      (cfzp050CarrierSensitivityConstant epsilon W))
    (hRemainder : Cfzp050CellSensitivityEnvelope
      (cfzp048PrimeAxisRemainderTestFunction W)
      (cfzp040CarrierCellExpLeft W c n)
      (cfzp040CarrierCellExpRight W c n)
      (cfzp039CarrierCellLeft W c n) W.rectangle.σ
      (cfzp050RemainderSensitivityConstant W)) :
    cfzp049CombinedPrimeCountingDiscrepancySensitivity epsilon W c n ≤
      cfzp050CombinedSensitivityConstant epsilon W *
        Real.exp (-W.rectangle.σ * cfzp039CarrierCellLeft W c n) := by
  have hc := cfzp050CarrierDiscrepancyCellSensitivity_le hε W c n hCarrier
  have hr := cfzp050RemainderDiscrepancyCellSensitivity_le W c n hRemainder
  have hK := (cfzp036PrimeAxisRemainderConstant_pos hε W).le
  unfold cfzp049CombinedPrimeCountingDiscrepancySensitivity
    cfzp050CombinedSensitivityConstant
  calc
    _ ≤ cfzp050CarrierSensitivityConstant epsilon W *
          Real.exp (-W.rectangle.σ * cfzp039CarrierCellLeft W c n) +
        cfzp036PrimeAxisRemainderConstant epsilon W *
          (cfzp050RemainderSensitivityConstant W *
            Real.exp (-W.rectangle.σ * cfzp039CarrierCellLeft W c n)) :=
      add_le_add hc (mul_le_mul_of_nonneg_left hr hK)
    _ = (cfzp050CarrierSensitivityConstant epsilon W +
        cfzp036PrimeAxisRemainderConstant epsilon W *
          cfzp050RemainderSensitivityConstant W) *
        Real.exp (-W.rectangle.σ * cfzp039CarrierCellLeft W c n) := by ring

/-! ## Gate B: reusable logarithmic-cell geometry -/

/-- Points in a late exponential cell have positive x- and log-coordinates.
This small lemma keeps the endpoint and derivative certificates branch-free. -/
theorem cfzp050_cell_log_bounds
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hU : 1 ≤ cfzp039CarrierCellLeft W c n)
    {x : ℝ}
    (hx : x ∈ Set.Icc
      (cfzp040CarrierCellExpLeft W c n)
      (cfzp040CarrierCellExpRight W c n)) :
    0 < x ∧
      cfzp039CarrierCellLeft W c n ≤ Real.log x ∧
      Real.log x ≤ cfzp039CarrierCellRight W c n ∧
      1 ≤ Real.log x := by
  have hxpos : 0 < x :=
    (Real.exp_pos (cfzp039CarrierCellLeft W c n)).trans_le hx.1
  have hleft : cfzp039CarrierCellLeft W c n ≤ Real.log x :=
    (Real.le_log_iff_exp_le hxpos).2 hx.1
  have hright : Real.log x ≤ cfzp039CarrierCellRight W c n :=
    (Real.log_le_iff_le_exp hxpos).2 hx.2
  exact ⟨hxpos, hleft, hright,
    le_trans hU hleft⟩

/-! ## Gate F: the explicit relative envelope -/

/-- The common finite envelope after the sensitivity has been eliminated. -/
noncomputable def cfzp050RelativeCombinedDiscrepancyExplicitEnvelope
    (epsilon delta : ℝ)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) : ℝ :=
  delta * Real.exp (cfzp036PrimeAxisCarrierPeriod W) *
    cfzp050CombinedSensitivityConstant epsilon W *
    (Real.exp (cfzp039PrimeAxisGrowthExponent W *
      cfzp039CarrierCellLeft W c n) /
      cfzp039CarrierCellLeft W c n)

theorem cfzp050RelativeCombinedDiscrepancyExplicitEnvelope_eq_normalForm
    (epsilon delta : ℝ)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) :
    cfzp050RelativeCombinedDiscrepancyExplicitEnvelope epsilon delta W c n =
      delta * Real.exp (cfzp036PrimeAxisCarrierPeriod W) *
        cfzp050CombinedSensitivityConstant epsilon W *
        (Real.exp (cfzp039PrimeAxisGrowthExponent W *
          cfzp039CarrierCellLeft W c n) /
          cfzp039CarrierCellLeft W c n) := by
  rfl

theorem cfzp050CombinedDebt_le_explicitRelativeEnvelope
    {epsilon delta : ℝ} (hε : 0 < epsilon) (hδ : 0 ≤ delta)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hU : 1 ≤ cfzp039CarrierCellLeft W c n)
    (hRel : Cfzp049PrimeCountingRelativeDiscrepancyBoundAt W c n delta)
    (hCarrier : Cfzp050CellSensitivityEnvelope
      (cfzp040PrimeAxisCarrierTestFunction epsilon W)
      (cfzp040CarrierCellExpLeft W c n)
      (cfzp040CarrierCellExpRight W c n)
      (cfzp039CarrierCellLeft W c n) W.rectangle.σ
      (cfzp050CarrierSensitivityConstant epsilon W))
    (hRemainder : Cfzp050CellSensitivityEnvelope
      (cfzp048PrimeAxisRemainderTestFunction W)
      (cfzp040CarrierCellExpLeft W c n)
      (cfzp040CarrierCellExpRight W c n)
      (cfzp039CarrierCellLeft W c n) W.rectangle.σ
      (cfzp050RemainderSensitivityConstant W))
    (hCarrierDerivAbsInt : IntegrableOn
      (fun x => |deriv (cfzp040PrimeAxisCarrierTestFunction epsilon W) x|)
        (Set.Ioc (cfzp040CarrierCellExpLeft W c n)
          (cfzp040CarrierCellExpRight W c n)))
    (hCarrierDerivDiscInt : IntegrableOn
      (fun x => deriv (cfzp040PrimeAxisCarrierTestFunction epsilon W) x *
        cfzp040PrimeCountingDiscrepancy x)
        (Set.Ioc (cfzp040CarrierCellExpLeft W c n)
          (cfzp040CarrierCellExpRight W c n)))
    (hRemainderDerivAbsInt : IntegrableOn
      (fun x => |deriv (cfzp048PrimeAxisRemainderTestFunction W) x|)
        (Set.Ioc (cfzp040CarrierCellExpLeft W c n)
          (cfzp040CarrierCellExpRight W c n)))
    (hRemainderDerivDiscInt : IntegrableOn
      (fun x => deriv (cfzp048PrimeAxisRemainderTestFunction W) x *
        cfzp040PrimeCountingDiscrepancy x)
        (Set.Ioc (cfzp040CarrierCellExpLeft W c n)
          (cfzp040CarrierCellExpRight W c n))) :
    cfzp049CombinedPrimeCountingDiscrepancyCellDebt epsilon W c n ≤
      cfzp050RelativeCombinedDiscrepancyExplicitEnvelope
        epsilon delta W c n := by
  have hU0 : 0 < cfzp039CarrierCellLeft W c n :=
    lt_of_lt_of_le (by norm_num) hU
  have hSens := cfzp050CombinedPrimeCountingDiscrepancySensitivity_le
    hε W c n hCarrier hRemainder
  have hRelEnv := cfzp049CombinedDebt_le_relativeEnvelope
    hε hδ W c n hU hRel hCarrierDerivAbsInt hCarrierDerivDiscInt
      hRemainderDerivAbsInt hRemainderDerivDiscInt
  have hfactor : 0 ≤
      delta * Real.exp (cfzp039CarrierCellRight W c n) /
        cfzp039CarrierCellLeft W c n := by
    exact div_nonneg
      (mul_nonneg hδ (Real.exp_pos _).le) hU0.le
  have hscaled := mul_le_mul_of_nonneg_left hSens hfactor
  have hR := cfzp046CarrierCellRight_eq_left_add_period W c n
  have hexp :
      Real.exp (cfzp039CarrierCellRight W c n) *
          Real.exp (-W.rectangle.σ * cfzp039CarrierCellLeft W c n) =
        Real.exp (cfzp036PrimeAxisCarrierPeriod W) *
          Real.exp (cfzp039PrimeAxisGrowthExponent W *
            cfzp039CarrierCellLeft W c n) := by
    rw [hR]
    calc
      Real.exp (cfzp039CarrierCellLeft W c n +
          cfzp036PrimeAxisCarrierPeriod W) *
          Real.exp (-W.rectangle.σ * cfzp039CarrierCellLeft W c n) =
        Real.exp (cfzp036PrimeAxisCarrierPeriod W) *
          (Real.exp (cfzp039CarrierCellLeft W c n) *
            Real.exp (-W.rectangle.σ * cfzp039CarrierCellLeft W c n)) := by
          rw [Real.exp_add]
          ring
      _ = Real.exp (cfzp036PrimeAxisCarrierPeriod W) *
          Real.exp (cfzp039CarrierCellLeft W c n +
            (-W.rectangle.σ * cfzp039CarrierCellLeft W c n)) := by
          rw [Real.exp_add]
      _ = Real.exp (cfzp036PrimeAxisCarrierPeriod W) *
          Real.exp (cfzp039PrimeAxisGrowthExponent W *
            cfzp039CarrierCellLeft W c n) := by
          congr 2
          unfold cfzp039PrimeAxisGrowthExponent
          ring
  calc
    _ ≤ cfzp049RelativeCombinedDiscrepancyEnvelope epsilon delta W c n :=
      hRelEnv
    _ ≤ (delta * Real.exp (cfzp039CarrierCellRight W c n) /
          cfzp039CarrierCellLeft W c n) *
        (cfzp050CombinedSensitivityConstant epsilon W *
          Real.exp (-W.rectangle.σ * cfzp039CarrierCellLeft W c n)) := by
      simpa [cfzp049RelativeCombinedDiscrepancyEnvelope] using hscaled
    _ = cfzp050RelativeCombinedDiscrepancyExplicitEnvelope
        epsilon delta W c n := by
      unfold cfzp050RelativeCombinedDiscrepancyExplicitEnvelope
      rw [div_eq_mul_inv, div_eq_mul_inv]
      calc
        delta * Real.exp (cfzp039CarrierCellRight W c n) *
            (cfzp039CarrierCellLeft W c n)⁻¹ *
            (cfzp050CombinedSensitivityConstant epsilon W *
              Real.exp (-W.rectangle.σ * cfzp039CarrierCellLeft W c n)) =
          delta * cfzp050CombinedSensitivityConstant epsilon W *
            (Real.exp (cfzp039CarrierCellRight W c n) *
              Real.exp (-W.rectangle.σ * cfzp039CarrierCellLeft W c n)) *
            (cfzp039CarrierCellLeft W c n)⁻¹ := by ring
        _ = delta * cfzp050CombinedSensitivityConstant epsilon W *
            (Real.exp (cfzp036PrimeAxisCarrierPeriod W) *
              Real.exp (cfzp039PrimeAxisGrowthExponent W *
                cfzp039CarrierCellLeft W c n)) *
            (cfzp039CarrierCellLeft W c n)⁻¹ := by rw [hexp]
        _ = delta * Real.exp (cfzp036PrimeAxisCarrierPeriod W) *
            cfzp050CombinedSensitivityConstant epsilon W *
            (Real.exp (cfzp039PrimeAxisGrowthExponent W *
              cfzp039CarrierCellLeft W c n) *
              (cfzp039CarrierCellLeft W c n)⁻¹) := by ring

/-! ## Gate G: cancellation against the smooth margin -/

/-- A finite coefficient condition for an arbitrary requested margin share. -/
def Cfzp050RelativeDiscrepancyMarginShareCondition
    (epsilon delta theta : ℝ)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) : Prop :=
  4 * delta * Real.exp (cfzp036PrimeAxisCarrierPeriod W) *
      cfzp050CombinedSensitivityConstant epsilon W ≤
    theta * cfzp039ExponentialCarrierPeriodTransform epsilon W c

theorem cfzp050RelativeEnvelope_le_marginShare
    {epsilon delta theta : ℝ}
    (_hε : 0 < epsilon) (_hδ : 0 ≤ delta) (_hθ : 0 ≤ theta)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (_hM : 0 < cfzp039ExponentialCarrierPeriodTransform epsilon W c)
    (hU : 1 ≤ cfzp039CarrierCellLeft W c n)
    (hShare : Cfzp050RelativeDiscrepancyMarginShareCondition
      epsilon delta theta W c) :
    cfzp050RelativeCombinedDiscrepancyExplicitEnvelope epsilon delta W c n ≤
      theta * cfzp044ExplicitSmoothMargin epsilon W c n := by
  have hU0 : 0 < cfzp039CarrierCellLeft W c n :=
    lt_of_lt_of_le (by norm_num) hU
  have hfactor : 0 ≤
      Real.exp (cfzp039PrimeAxisGrowthExponent W *
        cfzp039CarrierCellLeft W c n) /
        cfzp039CarrierCellLeft W c n := by
    exact div_nonneg (Real.exp_pos _).le hU0.le
  have hcoef :
      delta * Real.exp (cfzp036PrimeAxisCarrierPeriod W) *
          cfzp050CombinedSensitivityConstant epsilon W ≤
        theta * cfzp039ExponentialCarrierPeriodTransform epsilon W c / 4 := by
    dsimp [Cfzp050RelativeDiscrepancyMarginShareCondition] at hShare
    linarith
  have hmul := mul_le_mul_of_nonneg_right hcoef hfactor
  unfold cfzp050RelativeCombinedDiscrepancyExplicitEnvelope
    cfzp044ExplicitSmoothMargin
  calc
    delta * Real.exp (cfzp036PrimeAxisCarrierPeriod W) *
        cfzp050CombinedSensitivityConstant epsilon W *
        (Real.exp (cfzp039PrimeAxisGrowthExponent W *
          cfzp039CarrierCellLeft W c n) /
          cfzp039CarrierCellLeft W c n) ≤
      (theta * cfzp039ExponentialCarrierPeriodTransform epsilon W c / 4) *
        (Real.exp (cfzp039PrimeAxisGrowthExponent W *
          cfzp039CarrierCellLeft W c n) /
          cfzp039CarrierCellLeft W c n) := hmul
    _ = theta *
        (Real.exp (cfzp039PrimeAxisGrowthExponent W *
          cfzp039CarrierCellLeft W c n) *
          (cfzp039ExponentialCarrierPeriodTransform epsilon W c /
            (4 * cfzp039CarrierCellLeft W c n))) := by ring

/-! ## Gate H: quarter and eighth specializations -/

/-- The coefficient condition sufficient for a quarter of the margin. -/
def Cfzp050RelativeDiscrepancyQuarterMarginCondition
    (epsilon delta : ℝ)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) : Prop :=
  16 * delta * Real.exp (cfzp036PrimeAxisCarrierPeriod W) *
      cfzp050CombinedSensitivityConstant epsilon W ≤
    cfzp039ExponentialCarrierPeriodTransform epsilon W c

theorem cfzp050CombinedDebt_le_quarter_explicitSmoothMargin
    {epsilon delta : ℝ} (hε : 0 < epsilon) (hδ : 0 ≤ delta)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hM : 0 < cfzp039ExponentialCarrierPeriodTransform epsilon W c)
    (hU : 1 ≤ cfzp039CarrierCellLeft W c n)
    (hCondition : Cfzp050RelativeDiscrepancyQuarterMarginCondition
      epsilon delta W c)
    (hDebt : cfzp049CombinedPrimeCountingDiscrepancyCellDebt epsilon W c n ≤
      cfzp050RelativeCombinedDiscrepancyExplicitEnvelope epsilon delta W c n) :
    cfzp049CombinedPrimeCountingDiscrepancyCellDebt epsilon W c n ≤
      cfzp044ExplicitSmoothMargin epsilon W c n / 4 := by
  have hShare : Cfzp050RelativeDiscrepancyMarginShareCondition
      epsilon delta (1 / 4 : ℝ) W c := by
    dsimp [Cfzp050RelativeDiscrepancyQuarterMarginCondition,
      Cfzp050RelativeDiscrepancyMarginShareCondition] at hCondition ⊢
    linarith
  have henv := cfzp050RelativeEnvelope_le_marginShare
    hε hδ (by norm_num : (0 : ℝ) ≤ 1 / 4) W c n hM hU hShare
  linarith

/-- A quarter condition in its canonical coefficient form. -/
theorem cfzp050QuarterCondition_implies_marginShare
    {epsilon delta : ℝ}
    (W : PascalCenteredXiResidueTransportWindow) (c : ℝ)
    (hCondition : Cfzp050RelativeDiscrepancyQuarterMarginCondition
      epsilon delta W c) :
    Cfzp050RelativeDiscrepancyMarginShareCondition
      epsilon delta (1 / 4 : ℝ) W c := by
  dsimp [Cfzp050RelativeDiscrepancyQuarterMarginCondition,
    Cfzp050RelativeDiscrepancyMarginShareCondition] at *
  linarith

/-- The stronger eighth-margin coefficient condition. -/
def Cfzp050RelativeDiscrepancyEighthMarginCondition
    (epsilon delta : ℝ)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) : Prop :=
  32 * delta * Real.exp (cfzp036PrimeAxisCarrierPeriod W) *
      cfzp050CombinedSensitivityConstant epsilon W ≤
    cfzp039ExponentialCarrierPeriodTransform epsilon W c

/-! ## Gate I: the reduced remaining-quarter adapter -/

/-- The only uncharged term left after the explicit discrepancy quarter is
the initial radial contact deficit. -/
def Cfzp050LeftRadialDeficitBudgetAt
    (epsilon eta : ℝ)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) : Prop :=
  pascalCenteredXiPrimeSideFiniteRadialContactDeficit epsilon W
      (cfzp040CarrierCellNaturalLeft W c n) ≤ eta

theorem cfzp050_quarterDiscrepancy_and_leftDeficit_implies_combinedBudget
    {epsilon eta : ℝ}
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hDisc : cfzp049CombinedPrimeCountingDiscrepancyCellDebt epsilon W c n ≤
      cfzp044ExplicitSmoothMargin epsilon W c n / 4)
    (hLeft : Cfzp050LeftRadialDeficitBudgetAt epsilon eta W c n) :
    Cfzp049CombinedRemainingQuarterBudgetAt epsilon eta W c n := by
  dsimp [Cfzp050LeftRadialDeficitBudgetAt] at hLeft
  unfold Cfzp049CombinedRemainingQuarterBudgetAt
  linarith

/-! ## Explicit remaining providers -/

/-- These are the finite providers deliberately left outside CFZP-050. -/
inductive Cfzp050CombinedDiscrepancySensitivityEnvelopeGap : Prop
  | noAutomaticInteriorStripWindowProvider
  | noAutomaticLeadingSmoothAbelLogCellReadinessProvider
  | noRelativePrimeCountingDiscrepancyDecayProvider
  | noAutomaticLeftRadialDeficitBudgetProvider
  | noCofinalReducedRemainingQuarterBudgetProvider

end DkMath.RH.CFBRCProjection
