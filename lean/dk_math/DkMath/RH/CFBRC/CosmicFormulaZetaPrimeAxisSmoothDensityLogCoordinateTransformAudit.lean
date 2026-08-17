/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.RH.CFBRC.CosmicFormulaZetaPrimeAxisSmoothDiscrepancyCellReservoirAudit
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CosmicFormulaZetaPrimeAxisSmoothDensityLogCoordinateTransformAudit"

/-!
# CFZP-042: smooth density and log-coordinate transform

This module gives finite analytic identities for the smooth cell model.  The
prime-counting discrepancy and all asymptotic questions remain outside the
module's scope.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.NumberTheory
open MeasureTheory
open Set

/-! ## Gate A: smooth counting density -/

/-- The derivative density of the elementary model `x / log x`. -/
noncomputable def cfzp042PrimeCountingSmoothDensity (x : ℝ) : ℝ :=
  1 / Real.log x - 1 / (Real.log x) ^ 2

/-- A convenient explicit derivative for the carrier test function. -/
noncomputable def cfzp042CarrierTestFunctionDerivative
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (x : ℝ) : ℝ :=
  Real.exp (-(W.rectangle.σ) * Real.log x) / x *
    (-W.rectangle.σ *
        cfzp036PrimeAxisLeadingPeriodicCarrier ε W (Real.log x) +
      cfzp040LeadingCarrierDerivative ε W (Real.log x))

theorem cfzp042PrimeCountingSmoothModel_hasDerivAt
    {x : ℝ} (hx : 1 < x) :
    HasDerivAt cfzp040PrimeCountingSmoothModel
      (cfzp042PrimeCountingSmoothDensity x) x := by
  have hx0 : x ≠ 0 := ne_of_gt (lt_trans (by norm_num) hx)
  have hlog : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx0
  have hlog_ne : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
  have hquot := (hasDerivAt_id x).div hlog hlog_ne
  apply hquot.congr_deriv
  change (1 * Real.log x - x * x⁻¹) / (Real.log x) ^ 2 =
    cfzp042PrimeCountingSmoothDensity x
  unfold cfzp042PrimeCountingSmoothDensity
  field_simp [hlog_ne, hx.ne']

theorem cfzp042PrimeCountingSmoothDensity_eq_log_sub_one_div_sq
    {x : ℝ} (hx : Real.log x ≠ 0) :
    cfzp042PrimeCountingSmoothDensity x =
      (Real.log x - 1) / (Real.log x) ^ 2 := by
  unfold cfzp042PrimeCountingSmoothDensity
  field_simp [hx]

theorem cfzp042CarrierTestFunction_hasDerivAt
    {ε x : ℝ} (hε : ε ≠ 0) (hx : 0 < x)
    (W : PascalCenteredXiResidueTransportWindow) :
    HasDerivAt (cfzp040PrimeAxisCarrierTestFunction ε W)
      (cfzp042CarrierTestFunctionDerivative ε W x) x := by
  simpa [cfzp042CarrierTestFunctionDerivative] using
    (cfzp040PrimeAxisCarrierTestFunction_hasDerivAt hε hx W)

/-! ## Gate B: smooth Abel model and density integral -/

theorem cfzp042SmoothAbelCarrierModel_eq_densityIntegral
    {ε a b : ℝ} (_hε : ε ≠ 0)
    (_ha : 1 < a) (hab : a ≤ b)
    (W : PascalCenteredXiResidueTransportWindow)
    (hF : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (cfzp040PrimeAxisCarrierTestFunction ε W)
        (cfzp042CarrierTestFunctionDerivative ε W x) x)
    (hM : ∀ x ∈ Set.uIcc a b,
      HasDerivAt cfzp040PrimeCountingSmoothModel
        (cfzp042PrimeCountingSmoothDensity x) x)
    (hF_int : IntervalIntegrable
      (cfzp042CarrierTestFunctionDerivative ε W) volume a b)
    (hM_int : IntervalIntegrable
      (cfzp042PrimeCountingSmoothDensity) volume a b) :
    cfzp040SmoothAbelCarrierModel ε W a b =
      ∫ x in Set.Ioc a b,
    cfzp040PrimeAxisCarrierTestFunction ε W x *
          cfzp042PrimeCountingSmoothDensity x := by
  have hderiv_eq : ∀ x ∈ Set.uIcc a b,
      deriv (cfzp040PrimeAxisCarrierTestFunction ε W) x =
        cfzp042CarrierTestFunctionDerivative ε W x := by
    intro x hx
    exact (hF x hx).deriv
  have hreplace :
      (∫ x in Set.Ioc a b,
        deriv (cfzp040PrimeAxisCarrierTestFunction ε W) x *
          cfzp040PrimeCountingSmoothModel x) =
        ∫ x in Set.Ioc a b,
          cfzp042CarrierTestFunctionDerivative ε W x *
            cfzp040PrimeCountingSmoothModel x := by
    calc
      (∫ x in Set.Ioc a b,
          deriv (cfzp040PrimeAxisCarrierTestFunction ε W) x *
            cfzp040PrimeCountingSmoothModel x) =
          ∫ x in a..b,
            deriv (cfzp040PrimeAxisCarrierTestFunction ε W) x *
              cfzp040PrimeCountingSmoothModel x :=
        (intervalIntegral.integral_of_le hab).symm
      _ = ∫ x in a..b,
          cfzp042CarrierTestFunctionDerivative ε W x *
            cfzp040PrimeCountingSmoothModel x := by
        apply intervalIntegral.integral_congr
        intro x hx
        change deriv (cfzp040PrimeAxisCarrierTestFunction ε W) x *
            cfzp040PrimeCountingSmoothModel x = _
        rw [hderiv_eq x hx]
      _ = ∫ x in Set.Ioc a b,
          cfzp042CarrierTestFunctionDerivative ε W x *
            cfzp040PrimeCountingSmoothModel x :=
        intervalIntegral.integral_of_le hab
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := cfzp040PrimeAxisCarrierTestFunction ε W)
    (u' := cfzp042CarrierTestFunctionDerivative ε W)
    (v := cfzp040PrimeCountingSmoothModel)
    (v' := cfzp042PrimeCountingSmoothDensity)
    hF hM hF_int hM_int
  unfold cfzp040SmoothAbelCarrierModel
  rw [hreplace]
  simpa only [intervalIntegral.integral_of_le hab] using hparts.symm

/-! ## Gate C: log density weight and finite cell integral -/

/-- The density weight in the logarithmic coordinate. -/
noncomputable def cfzp042LogDensityWeight (u : ℝ) : ℝ :=
  1 / u - 1 / u ^ 2

/-- Smooth density integral over one logarithmic carrier cell. -/
noncomputable def cfzp042SmoothLogCellIntegral
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) : ℝ :=
  ∫ u in cfzp039CarrierCellLeft W c n..cfzp039CarrierCellRight W c n,
    Real.exp (cfzp039PrimeAxisGrowthExponent W * u) *
      cfzp036PrimeAxisLeadingPeriodicCarrier ε W u *
      cfzp042LogDensityWeight u

private noncomputable def cfzp042SmoothLogIntegrand
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) : ℝ → ℝ :=
  fun u => Real.exp (cfzp039PrimeAxisGrowthExponent W * u) *
    cfzp036PrimeAxisLeadingPeriodicCarrier ε W u *
    cfzp042LogDensityWeight u

theorem cfzp042_smoothDensity_exp_integrand_eq_logIntegrand
    {ε : ℝ} (W : PascalCenteredXiResidueTransportWindow)
    (u : ℝ) :
    (cfzp040PrimeAxisCarrierTestFunction ε W (Real.exp u) *
        cfzp042PrimeCountingSmoothDensity (Real.exp u)) * Real.exp u =
      cfzp042SmoothLogIntegrand ε W u := by
  unfold cfzp040PrimeAxisCarrierTestFunction
    cfzp042PrimeCountingSmoothDensity cfzp042SmoothLogIntegrand
    cfzp039PrimeAxisGrowthExponent cfzp042LogDensityWeight
  simp only [Real.log_exp]
  calc
    (Real.exp (-W.rectangle.σ * u) *
          cfzp036PrimeAxisLeadingPeriodicCarrier ε W u *
          (1 / u - 1 / u ^ 2)) * Real.exp u =
        (Real.exp (-W.rectangle.σ * u) * Real.exp u) *
          cfzp036PrimeAxisLeadingPeriodicCarrier ε W u *
          (1 / u - 1 / u ^ 2) := by ring
    _ = Real.exp ((1 - W.rectangle.σ) * u) *
          cfzp036PrimeAxisLeadingPeriodicCarrier ε W u *
          (1 / u - 1 / u ^ 2) := by
      rw [← Real.exp_add]
      congr 1
      ring_nf

/-!
The finite change-of-variables theorem is stated with the regularity data
needed by the current interval-integral API.  No asymptotic input occurs.
-/
theorem cfzp042SmoothDensityIntegral_eq_logCellIntegral
    {ε : ℝ} (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (_hL : 1 < cfzp039CarrierCellLeft W c n)
    (hDensity :
      cfzp040SmoothAbelCarrierModel ε W
          (cfzp040CarrierCellExpLeft W c n)
          (cfzp040CarrierCellExpRight W c n) =
        ∫ x in Set.Ioc
          (cfzp040CarrierCellExpLeft W c n)
          (cfzp040CarrierCellExpRight W c n),
          cfzp040PrimeAxisCarrierTestFunction ε W x *
            cfzp042PrimeCountingSmoothDensity x)
    (hg_cont : ContinuousOn
      (fun x => cfzp040PrimeAxisCarrierTestFunction ε W x *
        cfzp042PrimeCountingSmoothDensity x)
      (Real.exp '' Set.uIcc
        (cfzp039CarrierCellLeft W c n)
        (cfzp039CarrierCellRight W c n)))
    (hg_int : IntegrableOn
      (fun x => cfzp040PrimeAxisCarrierTestFunction ε W x *
        cfzp042PrimeCountingSmoothDensity x)
      (Real.exp '' Set.uIcc
        (cfzp039CarrierCellLeft W c n)
        (cfzp039CarrierCellRight W c n)))
    (hg_comp_int : IntegrableOn
      (fun u =>
        ((fun x => cfzp040PrimeAxisCarrierTestFunction ε W x *
          cfzp042PrimeCountingSmoothDensity x) ∘ Real.exp) u *
          Real.exp u)
      (Set.uIcc (cfzp039CarrierCellLeft W c n)
        (cfzp039CarrierCellRight W c n))) :
    cfzp040SmoothAbelCarrierModel ε W
        (cfzp040CarrierCellExpLeft W c n)
        (cfzp040CarrierCellExpRight W c n) =
      cfzp042SmoothLogCellIntegral ε W c n := by
  have himage :
      Real.exp '' Set.Ioo
          (min (cfzp039CarrierCellLeft W c n)
            (cfzp039CarrierCellRight W c n))
          (max (cfzp039CarrierCellLeft W c n)
            (cfzp039CarrierCellRight W c n)) ⊆
        Real.exp '' Set.uIcc (cfzp039CarrierCellLeft W c n)
          (cfzp039CarrierCellRight W c n) := by
    rintro y ⟨u, hu, rfl⟩
    refine ⟨u, ?_, rfl⟩
    have hLR : cfzp039CarrierCellLeft W c n ≤
        cfzp039CarrierCellRight W c n := by
      apply Real.exp_le_exp.mp
      exact (cfzp040CarrierCellExpLeft_lt_right W c n).le
    change min (cfzp039CarrierCellLeft W c n)
        (cfzp039CarrierCellRight W c n) < u ∧
      u < max (cfzp039CarrierCellLeft W c n)
        (cfzp039CarrierCellRight W c n) at hu
    have hu' : cfzp039CarrierCellLeft W c n < u ∧
        u < cfzp039CarrierCellRight W c n := by
      simpa [min_eq_left hLR, max_eq_right hLR] using hu
    exact mem_uIcc.mpr (Or.inl ⟨le_of_lt hu'.1, le_of_lt hu'.2⟩)
  have hsub := intervalIntegral.integral_comp_mul_deriv'''
    (a := cfzp039CarrierCellLeft W c n)
    (b := cfzp039CarrierCellRight W c n)
    (f := Real.exp) (f' := Real.exp)
    (g := fun x => cfzp040PrimeAxisCarrierTestFunction ε W x *
      cfzp042PrimeCountingSmoothDensity x)
    Real.continuous_exp.continuousOn
    (fun x hx => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    (hg_cont.mono himage)
    hg_int hg_comp_int
  rw [hDensity]
  have hsub' :
      (∫ x in cfzp039CarrierCellLeft W c n..cfzp039CarrierCellRight W c n,
        ((fun x => cfzp040PrimeAxisCarrierTestFunction ε W x *
          cfzp042PrimeCountingSmoothDensity x) ∘ Real.exp) x *
          Real.exp x) =
        ∫ x in Set.Ioc
          (cfzp040CarrierCellExpLeft W c n)
          (cfzp040CarrierCellExpRight W c n),
          cfzp040PrimeAxisCarrierTestFunction ε W x *
            cfzp042PrimeCountingSmoothDensity x := by
    have hexp : Real.exp (cfzp039CarrierCellLeft W c n) ≤
        Real.exp (cfzp039CarrierCellRight W c n) :=
      (cfzp040CarrierCellExpLeft_lt_right W c n).le
    simpa only [cfzp040CarrierCellExpLeft, cfzp040CarrierCellExpRight,
      intervalIntegral.integral_of_le hexp] using hsub
  rw [← hsub']
  unfold cfzp042SmoothLogCellIntegral
  apply intervalIntegral.integral_congr
  intro u hu
  exact cfzp042_smoothDensity_exp_integrand_eq_logIntegrand W u

/-! ## Gate D: translation to a natural `[0,P]` period cell -/

private theorem cfzp042_carrier_nat_period_translate
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (c t : ℝ) (n : ℕ) :
    cfzp036PrimeAxisLeadingPeriodicCarrier ε W
        (c + (n : ℝ) * cfzp036PrimeAxisCarrierPeriod W + t) =
      cfzp036PrimeAxisLeadingPeriodicCarrier ε W (c + t) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hp := cfzp036PrimeAxisLeadingPeriodicCarrier_periodic
        (ε := ε) W (c + (n : ℝ) * cfzp036PrimeAxisCarrierPeriod W + t)
      convert hp.trans ih using 1
      simp [Nat.cast_succ, add_left_comm, add_comm]
      ring_nf

/-- The translated smooth logarithmic cell integral. -/
noncomputable def cfzp042TranslatedSmoothCellIntegral
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) : ℝ :=
  Real.exp (cfzp039PrimeAxisGrowthExponent W *
      cfzp039CarrierCellLeft W c n) *
    ∫ t in (0 : ℝ)..cfzp036PrimeAxisCarrierPeriod W,
      Real.exp (cfzp039PrimeAxisGrowthExponent W * t) *
        cfzp036PrimeAxisLeadingPeriodicCarrier ε W (c + t) *
        cfzp042LogDensityWeight
          (cfzp039CarrierCellLeft W c n + t)

theorem cfzp042SmoothLogCellIntegral_eq_translated
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) :
    cfzp042SmoothLogCellIntegral ε W c n =
      cfzp042TranslatedSmoothCellIntegral ε W c n := by
  let β := cfzp039PrimeAxisGrowthExponent W
  let P := cfzp036PrimeAxisCarrierPeriod W
  let U := cfzp039CarrierCellLeft W c n
  have hR : cfzp039CarrierCellRight W c n = U + P := by
    unfold U P cfzp039CarrierCellRight cfzp039CarrierCellLeft
    norm_num [Nat.cast_add]
    ring
  have htranslate :
      (fun t => Real.exp (β * (U + t)) *
          cfzp036PrimeAxisLeadingPeriodicCarrier ε W (U + t) *
          cfzp042LogDensityWeight (U + t)) =
        (fun t => Real.exp (β * U) *
          (Real.exp (β * t) *
            cfzp036PrimeAxisLeadingPeriodicCarrier ε W (c + t) *
            cfzp042LogDensityWeight (U + t))) := by
    funext t
    have hper := cfzp042_carrier_nat_period_translate ε W c t n
    have hU : U = c + (n : ℝ) * P := by
      unfold U P cfzp039CarrierCellLeft cfzp036PrimeAxisCarrierPeriod
      ring
    rw [hU]
    rw [hper]
    calc
      Real.exp (β * (c + (n : ℝ) * P + t)) *
          cfzp036PrimeAxisLeadingPeriodicCarrier ε W (c + t) *
          cfzp042LogDensityWeight (c + (n : ℝ) * P + t) =
        (Real.exp (β * (c + (n : ℝ) * P)) * Real.exp (β * t)) *
          cfzp036PrimeAxisLeadingPeriodicCarrier ε W (c + t) *
          cfzp042LogDensityWeight (c + (n : ℝ) * P + t) := by
        rw [← Real.exp_add]
        congr 1
        ring_nf
      _ = Real.exp (β * (c + (n : ℝ) * P)) *
          (Real.exp (β * t) *
            cfzp036PrimeAxisLeadingPeriodicCarrier ε W (c + t) *
            cfzp042LogDensityWeight (c + (n : ℝ) * P + t)) := by ring
  unfold cfzp042SmoothLogCellIntegral
  change (∫ u in U..cfzp039CarrierCellRight W c n,
      Real.exp (β * u) *
        cfzp036PrimeAxisLeadingPeriodicCarrier ε W u *
        cfzp042LogDensityWeight u) = _
  rw [hR]
  have hshift :
      (∫ t in (0 : ℝ)..P,
        Real.exp (β * (U + t)) *
          cfzp036PrimeAxisLeadingPeriodicCarrier ε W (U + t) *
          cfzp042LogDensityWeight (U + t)) =
        ∫ u in U..U + P,
          Real.exp (β * u) *
            cfzp036PrimeAxisLeadingPeriodicCarrier ε W u *
            cfzp042LogDensityWeight u :=
    by
      convert intervalIntegral.integral_comp_add_right
        (a := (0 : ℝ)) (b := P)
        (fun u => Real.exp (β * u) *
          cfzp036PrimeAxisLeadingPeriodicCarrier ε W u *
          cfzp042LogDensityWeight u) U using 1 <;>
        simp [add_comm]
  rw [← hshift]
  rw [htranslate, intervalIntegral.integral_const_mul]
  dsimp [cfzp042TranslatedSmoothCellIntegral, U, P]

/-! ## Gate E: exponential carrier moment -/

/-- The uncorrected exponentially weighted carrier moment on one period. -/
noncomputable def cfzp042ExponentialCarrierMoment
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..cfzp036PrimeAxisCarrierPeriod W,
      Real.exp (cfzp039PrimeAxisGrowthExponent W * t) *
      cfzp036PrimeAxisLeadingPeriodicCarrier ε W (c + t)

private noncomputable def cfzp042ExponentialCarrierAntiderivative
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (c t : ℝ) : ℝ :=
  Real.exp (cfzp039PrimeAxisGrowthExponent W * t) /
      (ε * (cfzp039PrimeAxisGrowthExponent W ^ 2 + W.rectangle.T ^ 2)) *
    (cfzp036LeadingSinCoeffNumerator ε W *
        (cfzp039PrimeAxisGrowthExponent W *
            Real.sin (W.rectangle.T * (c + t)) -
          W.rectangle.T * Real.cos (W.rectangle.T * (c + t))) +
      cfzp036LeadingCosCoeffNumerator ε W *
        (cfzp039PrimeAxisGrowthExponent W *
            Real.cos (W.rectangle.T * (c + t)) +
          W.rectangle.T * Real.sin (W.rectangle.T * (c + t))))

private theorem cfzp042ExponentialCarrierAntiderivative_hasDerivAt
    {ε : ℝ} (hε : ε ≠ 0)
    (W : PascalCenteredXiResidueTransportWindow) (c t : ℝ) :
    HasDerivAt (cfzp042ExponentialCarrierAntiderivative ε W c)
      (Real.exp (cfzp039PrimeAxisGrowthExponent W * t) *
        cfzp036PrimeAxisLeadingPeriodicCarrier ε W (c + t)) t := by
  let β := cfzp039PrimeAxisGrowthExponent W
  let T := W.rectangle.T
  let S := cfzp036LeadingSinCoeffNumerator ε W
  let C := cfzp036LeadingCosCoeffNumerator ε W
  let D := β ^ 2 + T ^ 2
  have hD : D ≠ 0 := by
    dsimp [D]
    nlinarith [sq_nonneg β, sq_pos_of_pos W.rectangle.hT]
  have hD' : β ^ 2 + T ^ 2 ≠ 0 := by
    dsimp [T]
    nlinarith [sq_nonneg β, sq_pos_of_pos W.rectangle.hT]
  have hden : ε * D ≠ 0 := mul_ne_zero hε hD
  have hE : HasDerivAt (fun v : ℝ => Real.exp (β * v))
      (β * Real.exp (β * t)) t := by
    simpa [Function.comp_def, id_eq, mul_comm, mul_left_comm, mul_assoc] using
      (Real.hasDerivAt_exp (β * t)).comp t
        ((hasDerivAt_id t).const_mul β)
  have hinner : HasDerivAt (fun v : ℝ => T * (c + v)) T t := by
    simpa [Function.comp_def, id_eq, add_comm, mul_comm, mul_left_comm, mul_assoc] using
      ((hasDerivAt_id t).add_const c).const_mul T
  have hsin : HasDerivAt
      (fun v : ℝ => Real.sin (T * (c + v)))
      (T * Real.cos (T * (c + t))) t := by
    simpa [Function.comp_def, id_eq, mul_comm, mul_left_comm, mul_assoc] using
      (Real.hasDerivAt_sin (T * (c + t))).comp t hinner
  have hcos : HasDerivAt
      (fun v : ℝ => Real.cos (T * (c + v)))
      (-T * Real.sin (T * (c + t))) t := by
    simpa [Function.comp_def, id_eq, mul_comm, mul_left_comm, mul_assoc] using
      (Real.hasDerivAt_cos (T * (c + t))).comp t hinner
  have hB :=
    ((hsin.const_mul (S * β)).add (hcos.const_mul (-S * T))).add
      ((hcos.const_mul (C * β)).add (hsin.const_mul (C * T)))
  have hprod := hE.mul hB
  have hscaled := hprod.div_const (ε * D)
  have hfun :
      (cfzp042ExponentialCarrierAntiderivative ε W c : ℝ → ℝ) =
        (fun x =>
          ((fun v => Real.exp (β * v)) *
              (((fun y => S * β * Real.sin (T * (c + y))) +
                  fun y => -S * T * Real.cos (T * (c + y))) +
                ((fun y => C * β * Real.cos (T * (c + y))) +
                  fun y => C * T * Real.sin (T * (c + y))))) x /
            (ε * D)) := by
    funext v
    unfold cfzp042ExponentialCarrierAntiderivative
    dsimp [β, T, S, C, D]
    ring
  have heq :
      (cfzp042ExponentialCarrierAntiderivative ε W c) =ᶠ[nhds t]
        (fun x =>
          ((fun v => Real.exp (β * v)) *
              (((fun y => S * β * Real.sin (T * (c + y))) +
                  fun y => -S * T * Real.cos (T * (c + y))) +
                ((fun y => C * β * Real.cos (T * (c + y))) +
                  fun y => C * T * Real.sin (T * (c + y))))) x /
            (ε * D)) :=
    Filter.Eventually.of_forall (fun v => congrFun hfun v)
  have hscaled' := hscaled.congr_of_eventuallyEq heq
  apply hscaled'.congr_deriv
  dsimp [β, T, S, C, D]
  rw [cfzp036PrimeAxisLeadingPeriodicCarrier_eq_sin_cos_pair
    (ε := ε) (u := c + t) hε W]
  have hD'' :
      cfzp039PrimeAxisGrowthExponent W ^ 2 + W.rectangle.T ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg (cfzp039PrimeAxisGrowthExponent W),
      sq_pos_of_pos W.rectangle.hT]
  field_simp [hε, hD'']
  ring

theorem cfzp042ExponentialCarrierMoment_eq_transform
    {ε : ℝ} (hε : ε ≠ 0)
    (W : PascalCenteredXiResidueTransportWindow) (c : ℝ) :
    cfzp042ExponentialCarrierMoment ε W c =
      cfzp039ExponentialCarrierPeriodTransform ε W c := by
  let β := cfzp039PrimeAxisGrowthExponent W
  let P := cfzp036PrimeAxisCarrierPeriod W
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) P,
      HasDerivAt (cfzp042ExponentialCarrierAntiderivative ε W c)
        (Real.exp (β * t) *
          cfzp036PrimeAxisLeadingPeriodicCarrier ε W (c + t)) t := by
    intro t _
    simpa [β] using cfzp042ExponentialCarrierAntiderivative_hasDerivAt
      hε W c t
  have hcont : ContinuousOn
      (fun t => Real.exp (β * t) *
        cfzp036PrimeAxisLeadingPeriodicCarrier ε W (c + t))
      (Set.uIcc (0 : ℝ) P) := by
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
  have hInt : IntervalIntegrable
      (fun t => Real.exp (β * t) *
        cfzp036PrimeAxisLeadingPeriodicCarrier ε W (c + t)) volume 0 P := by
    exact hcont.intervalIntegrable
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    hderiv hInt
  have hphase : W.rectangle.T * (c + P) = W.rectangle.T * c + 2 * Real.pi := by
    unfold P cfzp036PrimeAxisCarrierPeriod
    field_simp [W.rectangle.hT.ne']
  unfold cfzp042ExponentialCarrierMoment
  rw [hFTC]
  unfold cfzp042ExponentialCarrierAntiderivative
    cfzp039ExponentialCarrierPeriodTransform
    cfzp039ExponentialCarrierPeriodScale
  rw [hphase, Real.sin_add_two_pi, Real.cos_add_two_pi]
  dsimp [β, P]
  unfold cfzp039ExponentialCarrierSinCoeff
    cfzp039ExponentialCarrierCosCoeff
  simp [Real.exp_zero]
  field_simp [hε]
  ring

/-! ## Gate F: exact transform plus weight variation error -/

/-- The exact error from replacing the density weight by its left endpoint. -/
noncomputable def cfzp042SmoothWeightVariationError
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) : ℝ :=
  ∫ t in (0 : ℝ)..cfzp036PrimeAxisCarrierPeriod W,
    Real.exp (cfzp039PrimeAxisGrowthExponent W * t) *
      cfzp036PrimeAxisLeadingPeriodicCarrier ε W (c + t) *
      (cfzp042LogDensityWeight
          (cfzp039CarrierCellLeft W c n + t) -
        cfzp042LogDensityWeight
          (cfzp039CarrierCellLeft W c n))

/--
The smooth cell is exactly the principal exponential carrier transform plus
the error caused by retaining the varying density weight.  The two
integrability hypotheses are deliberately finite and local; this theorem
does not estimate the error.
-/
theorem cfzp042SmoothAbelCell_eq_transform_add_weightError
    {ε : ℝ} (hε : ε ≠ 0)
    (W : PascalCenteredXiResidueTransportWindow) (c : ℝ) (n : ℕ)
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
    cfzp040SmoothAbelCarrierModel ε W
        (cfzp040CarrierCellExpLeft W c n)
        (cfzp040CarrierCellExpRight W c n) =
      Real.exp (cfzp039PrimeAxisGrowthExponent W *
          cfzp039CarrierCellLeft W c n) *
        (cfzp042LogDensityWeight
            (cfzp039CarrierCellLeft W c n) *
            cfzp039ExponentialCarrierPeriodTransform ε W c +
          cfzp042SmoothWeightVariationError ε W c n) := by
  let β := cfzp039PrimeAxisGrowthExponent W
  let P := cfzp036PrimeAxisCarrierPeriod W
  let U := cfzp039CarrierCellLeft W c n
  let A : ℝ → ℝ := fun t =>
    Real.exp (β * t) *
      cfzp036PrimeAxisLeadingPeriodicCarrier ε W (c + t)
  let qU := cfzp042LogDensityWeight U
  have hE_int' : IntervalIntegrable
      (fun t => A t *
        (cfzp042LogDensityWeight (U + t) - qU)) volume 0 P := by
    simpa [A, U, qU, β, P] using hE_int
  have hA_int' : IntervalIntegrable A volume 0 P := by
    simpa [A, β, P] using hA_int
  have hsplit :
      (∫ t in (0 : ℝ)..P,
        A t * cfzp042LogDensityWeight (U + t)) =
        qU * (∫ t in (0 : ℝ)..P, A t) +
          ∫ t in (0 : ℝ)..P,
            A t * (cfzp042LogDensityWeight (U + t) - qU) := by
    calc
      (∫ t in (0 : ℝ)..P,
          A t * cfzp042LogDensityWeight (U + t)) =
          ∫ t in (0 : ℝ)..P,
            (qU * A t +
              A t * (cfzp042LogDensityWeight (U + t) - qU)) := by
        apply intervalIntegral.integral_congr
        intro t ht
        ring
      _ = (∫ t in (0 : ℝ)..P, qU * A t) +
          ∫ t in (0 : ℝ)..P,
            A t * (cfzp042LogDensityWeight (U + t) - qU) := by
        rw [intervalIntegral.integral_add
          (hA_int'.const_mul qU) hE_int']
      _ = qU * (∫ t in (0 : ℝ)..P, A t) +
          ∫ t in (0 : ℝ)..P,
            A t * (cfzp042LogDensityWeight (U + t) - qU) := by
        rw [intervalIntegral.integral_const_mul]
  have hAeq :
      (∫ t in (0 : ℝ)..P, A t) =
        cfzp042ExponentialCarrierMoment ε W c := by
    simpa [A, β, P] using
      (show
        (∫ t in (0 : ℝ)..cfzp036PrimeAxisCarrierPeriod W,
          Real.exp (cfzp039PrimeAxisGrowthExponent W * t) *
            cfzp036PrimeAxisLeadingPeriodicCarrier ε W (c + t)) =
          cfzp042ExponentialCarrierMoment ε W c by rfl)
  have hEeq :
      (∫ t in (0 : ℝ)..P,
        A t * (cfzp042LogDensityWeight (U + t) - qU)) =
        cfzp042SmoothWeightVariationError ε W c n := by
    simpa [A, β, P, U, qU] using
      (show
        (∫ t in (0 : ℝ)..cfzp036PrimeAxisCarrierPeriod W,
          Real.exp (cfzp039PrimeAxisGrowthExponent W * t) *
            cfzp036PrimeAxisLeadingPeriodicCarrier ε W (c + t) *
            (cfzp042LogDensityWeight
                (cfzp039CarrierCellLeft W c n + t) -
              cfzp042LogDensityWeight
                (cfzp039CarrierCellLeft W c n))) =
          cfzp042SmoothWeightVariationError ε W c n by rfl)
  calc
    cfzp040SmoothAbelCarrierModel ε W
        (cfzp040CarrierCellExpLeft W c n)
        (cfzp040CarrierCellExpRight W c n) =
        cfzp042SmoothLogCellIntegral ε W c n := hcell
    _ = cfzp042TranslatedSmoothCellIntegral ε W c n :=
      cfzp042SmoothLogCellIntegral_eq_translated ε W c n
    _ = Real.exp (β * U) *
        (∫ t in (0 : ℝ)..P,
          A t * cfzp042LogDensityWeight (U + t)) := by
      unfold cfzp042TranslatedSmoothCellIntegral
      rfl
    _ = Real.exp (β * U) *
        (qU * (∫ t in (0 : ℝ)..P, A t) +
          ∫ t in (0 : ℝ)..P,
            A t * (cfzp042LogDensityWeight (U + t) - qU)) := by
      rw [hsplit]
    _ = Real.exp (β * U) *
        (cfzp042LogDensityWeight U *
            cfzp039ExponentialCarrierPeriodTransform ε W c +
          cfzp042SmoothWeightVariationError ε W c n) := by
      rw [hAeq, hEeq, cfzp042ExponentialCarrierMoment_eq_transform hε W c]

/-! ## Explicit open boundaries -/

inductive Cfzp042PrimeAxisSmoothDensityLogCoordinateTransformGap : Prop
  | noAutomaticInteriorStripWindowProvider
  | noSmoothWeightVariationErrorBound
  | noEventualSmoothAbelCellPositiveLowerBound
  | noPrimeCountingDiscrepancyFunctionalDecayProvider
  | noPointwiseDiscrepancyToFunctionalBound
  | noExceptionalPrimeAxisResidualElimination
  | noHigherPrimePowerResidualElimination

end DkMath.RH.CFBRCProjection
