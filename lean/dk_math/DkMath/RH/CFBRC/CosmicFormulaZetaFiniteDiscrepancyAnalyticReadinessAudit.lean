/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.RH.CFBRC.CosmicFormulaZetaPrimeCountingPNTToRelativeDiscrepancyAudit
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CosmicFormulaZetaFiniteDiscrepancyAnalyticReadinessAudit"

/-!
# CFZP-052: automatic finite discrepancy analytic readiness

The previous checkpoint left four finite `IntegrableOn` hypotheses in the
PNT-to-margin theorem.  This file supplies them from the actual floor,
smooth-model, derivative, and finite-cell definitions.  The estimates here
are distribution-free and finite; they do not prove PNT, a limit exchange, or
any radial eighth-credit statement.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.NumberTheory
open MeasureTheory
open Set

/-! ## Gate A: measurable finite prime-counting objects -/

/-- The floor prime-counting term is measurable on the real axis. -/
theorem cfzp052_primeCountingFloor_measurable :
    Measurable (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ)) := by
  fun_prop

/-- The finite smooth model is measurable, without a global continuity claim. -/
theorem cfzp052_primeCountingSmoothModel_measurable :
    Measurable cfzp040PrimeCountingSmoothModel := by
  unfold cfzp040PrimeCountingSmoothModel
  fun_prop

/-- The exact finite discrepancy is measurable. -/
theorem cfzp052_primeCountingDiscrepancy_measurable :
    Measurable cfzp040PrimeCountingDiscrepancy := by
  unfold cfzp040PrimeCountingDiscrepancy
  exact cfzp052_primeCountingFloor_measurable.sub
    cfzp052_primeCountingSmoothModel_measurable

/-! ## Gates B-C: exact derivative formulas on late cells -/

/-- The carrier derivative formula used only as a finite-cell measurable proxy. -/
noncomputable def cfzp052CarrierDerivativeFormula
    (epsilon : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (x : ℝ) : ℝ :=
  Real.exp (-W.rectangle.σ * Real.log x) / x *
    (-W.rectangle.σ *
        cfzp036PrimeAxisLeadingPeriodicCarrier epsilon W (Real.log x) +
      cfzp040LeadingCarrierDerivative epsilon W (Real.log x))

/-- The carrier derivative agrees with its explicit formula on a late cell. -/
theorem cfzp052_carrier_deriv_eq_formula_on_cell
    {epsilon : ℝ} (hε : 0 < epsilon)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hU : 1 ≤ cfzp039CarrierCellLeft W c n)
    {x : ℝ}
    (hx : x ∈ Set.Ioc
      (cfzp040CarrierCellExpLeft W c n)
      (cfzp040CarrierCellExpRight W c n)) :
    deriv (cfzp040PrimeAxisCarrierTestFunction epsilon W) x =
      cfzp052CarrierDerivativeFormula epsilon W x := by
  have hgeom := cfzp050_cell_log_bounds W c n hU
    ⟨le_of_lt hx.1, hx.2⟩
  simpa [cfzp052CarrierDerivativeFormula] using
    (cfzp040PrimeAxisCarrierTestFunction_hasDerivAt hε.ne' hgeom.1 W).deriv

/-- The carrier derivative formula is continuous on the closed late cell. -/
theorem cfzp052_carrierDerivativeFormula_continuousOn_cell
    {epsilon : ℝ} (_hε : 0 < epsilon)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hU : 1 ≤ cfzp039CarrierCellLeft W c n) :
    ContinuousOn (cfzp052CarrierDerivativeFormula epsilon W)
      (Set.Icc (cfzp040CarrierCellExpLeft W c n)
        (cfzp040CarrierCellExpRight W c n)) := by
  intro x hx
  have hgeom := cfzp050_cell_log_bounds W c n hU hx
  have hx0 : x ≠ 0 := ne_of_gt hgeom.1
  change ContinuousWithinAt
    (fun y => Real.exp (-W.rectangle.σ * Real.log y) / y *
      (-W.rectangle.σ *
          cfzp036PrimeAxisLeadingPeriodicCarrier epsilon W (Real.log y) +
        cfzp040LeadingCarrierDerivative epsilon W (Real.log y))) _ x
  have hlog : ContinuousAt Real.log x := Real.continuousAt_log hx0
  have hlead : ContinuousAt
      (fun u => cfzp036PrimeAxisLeadingPeriodicCarrier epsilon W u)
      (Real.log x) := by
    unfold cfzp036PrimeAxisLeadingPeriodicCarrier cfzp036LinearPhaseCore
    fun_prop
  have hlead' : ContinuousAt
      (fun y => cfzp036PrimeAxisLeadingPeriodicCarrier epsilon W (Real.log y)) x := by
    exact hlead.comp hlog
  have hderiv : ContinuousAt
      (fun u => cfzp040LeadingCarrierDerivative epsilon W u)
      (Real.log x) := by
    unfold cfzp040LeadingCarrierDerivative
    fun_prop
  have hderiv' : ContinuousAt
      (fun y => cfzp040LeadingCarrierDerivative epsilon W (Real.log y)) x := by
    exact hderiv.comp hlog
  have harg : ContinuousAt (fun y => -W.rectangle.σ * Real.log y) x := by
    fun_prop
  have hexp : ContinuousAt
      (fun y => Real.exp (-W.rectangle.σ * Real.log y)) x :=
    by exact Real.continuous_exp.continuousAt.comp harg
  have hquot : ContinuousAt
      (fun y => Real.exp (-W.rectangle.σ * Real.log y) / y) x := by
    exact hexp.div continuousAt_id hx0
  have hinner : ContinuousAt
      (fun y => -W.rectangle.σ *
          cfzp036PrimeAxisLeadingPeriodicCarrier epsilon W (Real.log y) +
        cfzp040LeadingCarrierDerivative epsilon W (Real.log y)) x := by
    exact (continuousAt_const.mul hlead').add hderiv'
  exact (hquot.mul hinner).continuousWithinAt

/-- The remainder derivative agrees with its named formula on a late cell. -/
theorem cfzp052_remainder_deriv_eq_formula_on_cell
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hU : 1 ≤ cfzp039CarrierCellLeft W c n)
    {x : ℝ}
    (hx : x ∈ Set.Ioc
      (cfzp040CarrierCellExpLeft W c n)
      (cfzp040CarrierCellExpRight W c n)) :
    deriv (cfzp048PrimeAxisRemainderTestFunction W) x =
      cfzp048PrimeAxisRemainderTestDerivative W x := by
  have hgeom := cfzp050_cell_log_bounds W c n hU
    ⟨le_of_lt hx.1, hx.2⟩
  have hxexp : Real.exp 1 ≤ x := by
    exact (Real.le_log_iff_exp_le hgeom.1).mp hgeom.2.2.2
  have hx1 : 1 < x :=
    (Real.one_lt_exp_iff.mpr (by norm_num)).trans_le hxexp
  exact (cfzp048PrimeAxisRemainderTestFunction_hasDerivAt W hx1).deriv

/-- The remainder derivative formula is continuous on the closed late cell. -/
theorem cfzp052_remainderDerivativeFormula_continuousOn_cell
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hU : 1 ≤ cfzp039CarrierCellLeft W c n) :
    ContinuousOn (cfzp048PrimeAxisRemainderTestDerivative W)
      (Set.Icc (cfzp040CarrierCellExpLeft W c n)
        (cfzp040CarrierCellExpRight W c n)) := by
  intro x hx
  have hgeom := cfzp050_cell_log_bounds W c n hU hx
  have hx0 : x ≠ 0 := ne_of_gt hgeom.1
  have hlog0 : Real.log x ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (by norm_num) hgeom.2.2.2)
  change ContinuousWithinAt
    (fun y => -(Real.exp (-W.rectangle.σ * Real.log y) / y) *
      (W.rectangle.σ / Real.log y + 1 / (Real.log y)^2)) _ x
  have hlog : ContinuousAt Real.log x := Real.continuousAt_log hx0
  have harg : ContinuousAt (fun y => -W.rectangle.σ * Real.log y) x := by
    fun_prop
  have hexp : ContinuousAt
      (fun y => Real.exp (-W.rectangle.σ * Real.log y)) x :=
    by exact Real.continuous_exp.continuousAt.comp harg
  have hquot : ContinuousAt
      (fun y => Real.exp (-W.rectangle.σ * Real.log y) / y) x := by
    exact hexp.div continuousAt_id hx0
  have hlogInv : ContinuousAt (fun y => 1 / Real.log y) x := by
    exact continuousAt_const.div hlog hlog0
  have hlogSqInv : ContinuousAt (fun y => 1 / (Real.log y)^2) x := by
    exact continuousAt_const.div (hlog.pow 2) (pow_ne_zero _ hlog0)
  have hinner : ContinuousAt
      (fun y => W.rectangle.σ / Real.log y + 1 / (Real.log y)^2) x := by
    have hsigma : ContinuousAt (fun _ : ℝ => W.rectangle.σ) x :=
      continuousAt_const
    convert (hsigma.mul hlogInv).add hlogSqInv using 1
    ext y
    simp [div_eq_mul_inv]
  exact (hquot.neg.mul hinner).continuousWithinAt

/-! ## Measurable finite-cell helpers -/

private theorem cfzp052_integrableOn_of_abs_bound
    {f : ℝ → ℝ} {a b C : ℝ}
    (hf : Measurable f) (_hC : 0 ≤ C)
    (hbound : ∀ x ∈ Set.Ioc a b, |f x| ≤ C) :
    IntegrableOn f (Set.Ioc a b) := by
  refine IntegrableOn.of_bound measure_Ioc_lt_top
    hf.aestronglyMeasurable.restrict C ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  simpa only [Real.norm_eq_abs] using hbound x hx

/-! ## Gate D: absolute derivative integrability -/

/-- The carrier absolute derivative is integrable on every late finite cell. -/
theorem cfzp052CarrierDerivativeAbs_integrableOn
    {epsilon : ℝ} (hε : 0 < epsilon)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hU : 1 ≤ cfzp039CarrierCellLeft W c n) :
    IntegrableOn
      (fun x => |deriv (cfzp040PrimeAxisCarrierTestFunction epsilon W) x|)
      (Set.Ioc (cfzp040CarrierCellExpLeft W c n)
        (cfzp040CarrierCellExpRight W c n)) := by
  let D := Real.exp (-W.rectangle.σ * cfzp039CarrierCellLeft W c n) *
      Real.exp (-cfzp039CarrierCellLeft W c n) *
      (W.rectangle.σ * cfzp050LeadingCarrierAbsConstant epsilon W +
        cfzp050LeadingCarrierDerivativeAbsConstant epsilon W)
  have hD : 0 ≤ D := by
    dsimp [D]
    have hσ : 0 ≤ W.rectangle.σ := by
      linarith [cfzp034_rectangleSigma_gt_half W]
    exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
      (add_nonneg
        (mul_nonneg hσ (cfzp050LeadingCarrierAbsConstant_nonneg hε W))
        (cfzp050LeadingCarrierDerivativeAbsConstant_nonneg hε W))
  have hmeas : Measurable
      (fun x => |cfzp052CarrierDerivativeFormula epsilon W x|) := by
    unfold cfzp052CarrierDerivativeFormula
      cfzp036PrimeAxisLeadingPeriodicCarrier cfzp036LinearPhaseCore
      cfzp040LeadingCarrierDerivative
    measurability
  have hI : IntegrableOn
      (fun x => |cfzp052CarrierDerivativeFormula epsilon W x|)
      (Set.Ioc (cfzp040CarrierCellExpLeft W c n)
        (cfzp040CarrierCellExpRight W c n)) := by
    apply cfzp052_integrableOn_of_abs_bound hmeas hD
    intro x hx
    rw [← cfzp052_carrier_deriv_eq_formula_on_cell hε W c n hU hx]
    simpa [D] using
      (cfzp050CarrierTestFunction_deriv_abs_le_on_cell hε W c n hU hx)
  apply hI.congr_fun
  · intro x hx
    change |cfzp052CarrierDerivativeFormula epsilon W x| =
      |deriv (cfzp040PrimeAxisCarrierTestFunction epsilon W) x|
    rw [cfzp052_carrier_deriv_eq_formula_on_cell hε W c n hU hx]
  · exact measurableSet_Ioc

/-- The remainder absolute derivative is integrable on every late finite cell. -/
theorem cfzp052RemainderDerivativeAbs_integrableOn
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hU : 1 ≤ cfzp039CarrierCellLeft W c n) :
    IntegrableOn
      (fun x => |deriv (cfzp048PrimeAxisRemainderTestFunction W) x|)
      (Set.Ioc (cfzp040CarrierCellExpLeft W c n)
        (cfzp040CarrierCellExpRight W c n)) := by
  let D := Real.exp (-W.rectangle.σ * cfzp039CarrierCellLeft W c n) *
      Real.exp (-cfzp039CarrierCellLeft W c n) * (W.rectangle.σ + 1)
  have hD : 0 ≤ D := by
    dsimp [D]
    have hσ : 0 ≤ W.rectangle.σ := by
      linarith [cfzp034_rectangleSigma_gt_half W]
    exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
      (by linarith)
  have hmeas : Measurable
      (fun x => |cfzp048PrimeAxisRemainderTestDerivative W x|) := by
    unfold cfzp048PrimeAxisRemainderTestDerivative
    measurability
  have hI : IntegrableOn
      (fun x => |cfzp048PrimeAxisRemainderTestDerivative W x|)
      (Set.Ioc (cfzp040CarrierCellExpLeft W c n)
        (cfzp040CarrierCellExpRight W c n)) := by
    apply cfzp052_integrableOn_of_abs_bound hmeas hD
    intro x hx
    rw [← cfzp052_remainder_deriv_eq_formula_on_cell W c n hU hx]
    simpa [D] using
      (cfzp050RemainderTestFunction_deriv_abs_le_on_cell W c n hU hx)
  apply hI.congr_fun
  · intro x hx
    change |cfzp048PrimeAxisRemainderTestDerivative W x| =
      |deriv (cfzp048PrimeAxisRemainderTestFunction W) x|
    rw [cfzp052_remainder_deriv_eq_formula_on_cell W c n hU hx]
  · exact measurableSet_Ioc

/-! ## Gate E: a distribution-free discrepancy bound -/

/-- A deliberately coarse finite bound for the discrepancy on one cell. -/
noncomputable def cfzp052FiniteCellDiscrepancyAbsBound
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) : ℝ :=
  (cfzp040CarrierCellNaturalRight W c n : ℝ) + 1 +
    cfzp040CarrierCellExpRight W c n

theorem cfzp052FiniteCellDiscrepancyAbsBound_nonneg
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) :
    0 ≤ cfzp052FiniteCellDiscrepancyAbsBound W c n := by
  unfold cfzp052FiniteCellDiscrepancyAbsBound
  have hN : 0 ≤ (cfzp040CarrierCellNaturalRight W c n : ℝ) :=
    Nat.cast_nonneg _
  have hE : 0 ≤ cfzp040CarrierCellExpRight W c n :=
    by rw [cfzp040CarrierCellExpRight]; exact (Real.exp_pos _).le
  linarith

theorem cfzp052_primeCountingDiscrepancy_abs_le_on_cell
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hU : 1 ≤ cfzp039CarrierCellLeft W c n)
    {x : ℝ}
    (hx : x ∈ Set.Ioc
      (cfzp040CarrierCellExpLeft W c n)
      (cfzp040CarrierCellExpRight W c n)) :
    |cfzp040PrimeCountingDiscrepancy x| ≤
      cfzp052FiniteCellDiscrepancyAbsBound W c n := by
  have hgeom := cfzp050_cell_log_bounds W c n hU
    ⟨le_of_lt hx.1, hx.2⟩
  have hfloor : ⌊x⌋₊ ≤ cfzp040CarrierCellNaturalRight W c n := by
    exact Nat.floor_mono hx.2
  have hpcNat : Nat.primeCounting ⌊x⌋₊ ≤
      Nat.primeCounting (cfzp040CarrierCellNaturalRight W c n) :=
    Nat.monotone_primeCounting hfloor
  have hpcRight : (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤
      (Nat.primeCounting (cfzp040CarrierCellNaturalRight W c n) : ℝ) := by
    exact_mod_cast hpcNat
  have hpcRightNat : Nat.primeCounting (cfzp040CarrierCellNaturalRight W c n) ≤
      cfzp040CarrierCellNaturalRight W c n + 1 := by
    unfold Nat.primeCounting Nat.primeCounting'
    exact Nat.count_le (p := Nat.Prime)
  have hpcRightBound :
      (Nat.primeCounting (cfzp040CarrierCellNaturalRight W c n) : ℝ) ≤
        (cfzp040CarrierCellNaturalRight W c n : ℝ) + 1 := by
    exact_mod_cast hpcRightNat
  have hpc : (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤
      (cfzp040CarrierCellNaturalRight W c n : ℝ) + 1 :=
    hpcRight.trans hpcRightBound
  have hpc0 : 0 ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) :=
    Nat.cast_nonneg _
  have hlog0 : 0 < Real.log x :=
    lt_of_lt_of_le (by norm_num) hgeom.2.2.2
  have hs0 : 0 ≤ cfzp040PrimeCountingSmoothModel x := by
    unfold cfzp040PrimeCountingSmoothModel
    exact div_nonneg hgeom.1.le hlog0.le
  have hsx : cfzp040PrimeCountingSmoothModel x ≤ x := by
    unfold cfzp040PrimeCountingSmoothModel
    apply (div_le_iff₀ hlog0).2
    have hmul := mul_nonneg hgeom.1.le
      (sub_nonneg.mpr hgeom.2.2.2)
    nlinarith
  have hsb : cfzp040PrimeCountingSmoothModel x ≤
      cfzp040CarrierCellExpRight W c n := hsx.trans hx.2
  unfold cfzp040PrimeCountingDiscrepancy
  calc
    |(Nat.primeCounting ⌊x⌋₊ : ℝ) -
        cfzp040PrimeCountingSmoothModel x| ≤
      |(Nat.primeCounting ⌊x⌋₊ : ℝ)| +
        |cfzp040PrimeCountingSmoothModel x| := abs_sub _ _
    _ = (Nat.primeCounting ⌊x⌋₊ : ℝ) +
        cfzp040PrimeCountingSmoothModel x := by
      rw [abs_of_nonneg hpc0, abs_of_nonneg hs0]
    _ ≤ (cfzp040CarrierCellNaturalRight W c n : ℝ) + 1 +
        cfzp040CarrierCellExpRight W c n := add_le_add hpc hsb
    _ ≤ cfzp052FiniteCellDiscrepancyAbsBound W c n := by
      dsimp [cfzp052FiniteCellDiscrepancyAbsBound]
      linarith

/-! ## Gate F: derivative-times-discrepancy integrability -/

/-- The carrier derivative times discrepancy is integrable without PNT input. -/
theorem cfzp052CarrierDerivativeMulDiscrepancy_integrableOn
    {epsilon : ℝ} (hε : 0 < epsilon)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hU : 1 ≤ cfzp039CarrierCellLeft W c n) :
    IntegrableOn
      (fun x => deriv (cfzp040PrimeAxisCarrierTestFunction epsilon W) x *
        cfzp040PrimeCountingDiscrepancy x)
      (Set.Ioc (cfzp040CarrierCellExpLeft W c n)
        (cfzp040CarrierCellExpRight W c n)) := by
  let D := Real.exp (-W.rectangle.σ * cfzp039CarrierCellLeft W c n) *
      Real.exp (-cfzp039CarrierCellLeft W c n) *
      (W.rectangle.σ * cfzp050LeadingCarrierAbsConstant epsilon W +
        cfzp050LeadingCarrierDerivativeAbsConstant epsilon W)
  let B := cfzp052FiniteCellDiscrepancyAbsBound W c n
  have hD : 0 ≤ D := by
    dsimp [D]
    have hσ : 0 ≤ W.rectangle.σ := by
      linarith [cfzp034_rectangleSigma_gt_half W]
    exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
      (add_nonneg
        (mul_nonneg hσ (cfzp050LeadingCarrierAbsConstant_nonneg hε W))
        (cfzp050LeadingCarrierDerivativeAbsConstant_nonneg hε W))
  have hB : 0 ≤ B := cfzp052FiniteCellDiscrepancyAbsBound_nonneg W c n
  have hformula : Measurable
      (fun x => cfzp052CarrierDerivativeFormula epsilon W x) := by
    unfold cfzp052CarrierDerivativeFormula
      cfzp036PrimeAxisLeadingPeriodicCarrier cfzp036LinearPhaseCore
      cfzp040LeadingCarrierDerivative
    measurability
  have hmeas : Measurable
      (fun x => cfzp052CarrierDerivativeFormula epsilon W x *
        cfzp040PrimeCountingDiscrepancy x) :=
    hformula.mul cfzp052_primeCountingDiscrepancy_measurable
  have hI : IntegrableOn
      (fun x => cfzp052CarrierDerivativeFormula epsilon W x *
        cfzp040PrimeCountingDiscrepancy x)
      (Set.Ioc (cfzp040CarrierCellExpLeft W c n)
        (cfzp040CarrierCellExpRight W c n)) := by
    apply cfzp052_integrableOn_of_abs_bound hmeas (mul_nonneg hD hB)
    intro x hx
    have hderiv : |cfzp052CarrierDerivativeFormula epsilon W x| ≤ D := by
      rw [← cfzp052_carrier_deriv_eq_formula_on_cell hε W c n hU hx]
      simpa [D] using
        (cfzp050CarrierTestFunction_deriv_abs_le_on_cell hε W c n hU hx)
    have hdisc : |cfzp040PrimeCountingDiscrepancy x| ≤ B := by
      exact cfzp052_primeCountingDiscrepancy_abs_le_on_cell W c n hU hx
    calc
      |cfzp052CarrierDerivativeFormula epsilon W x *
          cfzp040PrimeCountingDiscrepancy x| =
          |cfzp052CarrierDerivativeFormula epsilon W x| *
            |cfzp040PrimeCountingDiscrepancy x| := abs_mul _ _
      _ ≤ D * B := mul_le_mul hderiv hdisc (abs_nonneg _) hD
  apply hI.congr_fun
  · intro x hx
    change cfzp052CarrierDerivativeFormula epsilon W x *
        cfzp040PrimeCountingDiscrepancy x =
      deriv (cfzp040PrimeAxisCarrierTestFunction epsilon W) x *
        cfzp040PrimeCountingDiscrepancy x
    rw [cfzp052_carrier_deriv_eq_formula_on_cell hε W c n hU hx]
  · exact measurableSet_Ioc

/-- The remainder derivative times discrepancy is integrable without PNT input. -/
theorem cfzp052RemainderDerivativeMulDiscrepancy_integrableOn
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hU : 1 ≤ cfzp039CarrierCellLeft W c n) :
    IntegrableOn
      (fun x => deriv (cfzp048PrimeAxisRemainderTestFunction W) x *
        cfzp040PrimeCountingDiscrepancy x)
      (Set.Ioc (cfzp040CarrierCellExpLeft W c n)
        (cfzp040CarrierCellExpRight W c n)) := by
  let D := Real.exp (-W.rectangle.σ * cfzp039CarrierCellLeft W c n) *
      Real.exp (-cfzp039CarrierCellLeft W c n) * (W.rectangle.σ + 1)
  let B := cfzp052FiniteCellDiscrepancyAbsBound W c n
  have hD : 0 ≤ D := by
    dsimp [D]
    have hσ : 0 ≤ W.rectangle.σ := by
      linarith [cfzp034_rectangleSigma_gt_half W]
    exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
      (by linarith)
  have hB : 0 ≤ B := cfzp052FiniteCellDiscrepancyAbsBound_nonneg W c n
  have hformula : Measurable
      (fun x => cfzp048PrimeAxisRemainderTestDerivative W x) := by
    unfold cfzp048PrimeAxisRemainderTestDerivative
    measurability
  have hmeas : Measurable
      (fun x => cfzp048PrimeAxisRemainderTestDerivative W x *
        cfzp040PrimeCountingDiscrepancy x) :=
    hformula.mul cfzp052_primeCountingDiscrepancy_measurable
  have hI : IntegrableOn
      (fun x => cfzp048PrimeAxisRemainderTestDerivative W x *
        cfzp040PrimeCountingDiscrepancy x)
      (Set.Ioc (cfzp040CarrierCellExpLeft W c n)
        (cfzp040CarrierCellExpRight W c n)) := by
    apply cfzp052_integrableOn_of_abs_bound hmeas (mul_nonneg hD hB)
    intro x hx
    have hderiv : |cfzp048PrimeAxisRemainderTestDerivative W x| ≤ D := by
      rw [← cfzp052_remainder_deriv_eq_formula_on_cell W c n hU hx]
      simpa [D] using
        (cfzp050RemainderTestFunction_deriv_abs_le_on_cell W c n hU hx)
    have hdisc : |cfzp040PrimeCountingDiscrepancy x| ≤ B := by
      exact cfzp052_primeCountingDiscrepancy_abs_le_on_cell W c n hU hx
    calc
      |cfzp048PrimeAxisRemainderTestDerivative W x *
          cfzp040PrimeCountingDiscrepancy x| =
          |cfzp048PrimeAxisRemainderTestDerivative W x| *
            |cfzp040PrimeCountingDiscrepancy x| := abs_mul _ _
      _ ≤ D * B := mul_le_mul hderiv hdisc (abs_nonneg _) hD
  apply hI.congr_fun
  · intro x hx
    change cfzp048PrimeAxisRemainderTestDerivative W x *
        cfzp040PrimeCountingDiscrepancy x =
      deriv (cfzp048PrimeAxisRemainderTestFunction W) x *
        cfzp040PrimeCountingDiscrepancy x
    rw [cfzp052_remainder_deriv_eq_formula_on_cell W c n hU hx]
  · exact measurableSet_Ioc

/-! ## Gates G-J: readiness, eventual readiness, and PNT synchronization -/

/-- All four finite readiness certificates follow from `1 ≤ U`. -/
theorem cfzp052FiniteDiscrepancyAnalyticReadyAt_of_late
    {epsilon : ℝ} (hε : 0 < epsilon)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hU : 1 ≤ cfzp039CarrierCellLeft W c n) :
    Cfzp051FiniteDiscrepancyAnalyticReadyAt epsilon W c n := by
  refine ⟨cfzp052CarrierDerivativeAbs_integrableOn hε W c n hU,
    cfzp052CarrierDerivativeMulDiscrepancy_integrableOn hε W c n hU,
    cfzp052RemainderDerivativeAbs_integrableOn W c n hU,
    cfzp052RemainderDerivativeMulDiscrepancy_integrableOn W c n hU⟩

/-- Finite analytic readiness is eventual along the cofinal carrier cells. -/
theorem cfzp052_eventually_finiteDiscrepancyAnalyticReady
    {epsilon : ℝ} (hε : 0 < epsilon)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      Cfzp051FiniteDiscrepancyAnalyticReadyAt epsilon W c n := by
  filter_upwards [
    (cfzp047CarrierCellLeft_tendsto_atTop W c).eventually
      (Filter.eventually_ge_atTop (1 : ℝ))] with n hU
  exact cfzp052FiniteDiscrepancyAnalyticReadyAt_of_late hε W c n hU

/-- The PNT eighth-margin theorem with finite readiness generated internally. -/
theorem cfzp052_pntRatio_eventually_combinedDebt_le_eighthMargin_autoReady
    {epsilon : ℝ} (hε : 0 < epsilon)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ)
    (hM : 0 < cfzp039ExponentialCarrierPeriodTransform epsilon W c)
    (hPNT : Cfzp051PrimeCountingPNTRatioAtTop) :
    ∀ᶠ n : ℕ in Filter.atTop,
      cfzp049CombinedPrimeCountingDiscrepancyCellDebt epsilon W c n ≤
        cfzp044ExplicitSmoothMargin epsilon W c n / 8 := by
  exact cfzp051_pntRatio_eventually_combinedDebt_le_eighthMargin
    hε W c hM hPNT
    (cfzp052_eventually_finiteDiscrepancyAnalyticReady hε W c)

/-- PNT and an external left eighth-credit provider imply the remaining budget. -/
theorem cfzp052_pntRatio_and_leftEighthCredit_eventually_remainingQuarter
    {epsilon eta : ℝ} (hε : 0 < epsilon)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ)
    (hM : 0 < cfzp039ExponentialCarrierPeriodTransform epsilon W c)
    (hPNT : Cfzp051PrimeCountingPNTRatioAtTop)
    (hLeft : ∀ᶠ n : ℕ in Filter.atTop,
      Cfzp051LeftRadialEighthCreditBudgetAt epsilon eta W c n) :
    ∀ᶠ n : ℕ in Filter.atTop,
      Cfzp049CombinedRemainingQuarterBudgetAt epsilon eta W c n := by
  have hDebt := cfzp052_pntRatio_eventually_combinedDebt_le_eighthMargin_autoReady
    hε W c hM hPNT
  filter_upwards [hDebt, hLeft] with n hn hLn
  exact cfzp051_eighthDiscrepancy_and_leftEighthCredit_implies_combinedBudget
    W c n hn hLn

/-! ## Explicit firewall -/

/-- Remaining providers after finite analytic readiness has been closed. -/
inductive Cfzp052FiniteDiscrepancyAnalyticReadinessGap : Prop
  | noPrimeCountingPNTRatioProvider
  | noAutomaticInteriorStripWindowProvider
  | noAutomaticLeadingSmoothAbelLogCellReadinessProvider
  | noAutomaticLeftRadialEighthCreditBudgetProvider
  | noCofinalFinalRadialBudgetProvider

end DkMath.RH.CFBRCProjection
