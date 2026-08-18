/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.RH.CFBRC.CosmicFormulaZetaFiniteDiscrepancyAnalyticReadinessAudit
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CosmicFormulaZetaFiniteSmoothAbelReadinessRadialEighthDescentAudit"

/-!
# CFZP-053: finite smooth-Abel readiness and one-cell radial descent

This module generates the finite smooth-Abel certificates needed by the
CFZP-049 radial adapter.  Its final descent theorem is one-cell and finite:
it does not assert divergence of the smooth margins, a limit exchange, PNT,
or the Riemann hypothesis.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.NumberTheory
open MeasureTheory
open Set

/-! ## Gate A: finite late-cell geometry -/

private theorem cfzp053_late_hU_one
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hU : 2 ≤ cfzp039CarrierCellLeft W c n) :
    1 ≤ cfzp039CarrierCellLeft W c n := by linarith

private theorem cfzp053_late_exp_left_gt_one
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hU : 2 ≤ cfzp039CarrierCellLeft W c n) :
    1 < cfzp040CarrierCellExpLeft W c n := by
  rw [show (1 : ℝ) = Real.exp 0 by simp]
  exact Real.exp_lt_exp.mpr (by linarith [hU])

private theorem cfzp053_late_exp_left_le_right
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (_hU : 2 ≤ cfzp039CarrierCellLeft W c n) :
    cfzp040CarrierCellExpLeft W c n ≤
      cfzp040CarrierCellExpRight W c n :=
  (cfzp040CarrierCellExpLeft_lt_right W c n).le

private theorem cfzp053_late_mem_log_bounds
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hU : 2 ≤ cfzp039CarrierCellLeft W c n)
    {x : ℝ}
    (hx : x ∈ Set.Icc (cfzp040CarrierCellExpLeft W c n)
      (cfzp040CarrierCellExpRight W c n)) :
    0 < x ∧ 1 < x ∧ 0 < Real.log x := by
  have hgeom := cfzp050_cell_log_bounds W c n
    (cfzp053_late_hU_one W c n hU) hx
  have hx1 : 1 < x := by
    have hleft := cfzp053_late_exp_left_gt_one W c n hU
    exact lt_of_lt_of_le hleft hx.1
  exact ⟨hgeom.1, hx1, Real.log_pos hx1⟩

private theorem cfzp053_intervalIntegrable_of_continuousOn_Icc
    {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) :
    IntervalIntegrable f volume a b :=
  hf.intervalIntegrable_of_Icc hab

/-! ## Gates B-C: differentiability and derivative integrability -/

/-- The actual carrier test function is differentiable at every point of a
late finite cell. -/
theorem cfzp053CarrierTestFunction_differentiableOn_cell
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hU : 2 ≤ cfzp039CarrierCellLeft W c n) :
    ∀ x ∈ Set.Icc (cfzp040CarrierCellExpLeft W c n)
      (cfzp040CarrierCellExpRight W c n),
      DifferentiableAt ℝ
        (cfzp040PrimeAxisCarrierTestFunction epsilon W) x := by
  intro x hx
  exact (cfzp040PrimeAxisCarrierTestFunction_hasDerivAt hepsilon.ne'
    (cfzp053_late_mem_log_bounds W c n hU hx).1 W).differentiableAt

/-- The actual remainder test function is differentiable at every point of a
late finite cell. -/
theorem cfzp053RemainderTestFunction_differentiableOn_cell
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hU : 2 ≤ cfzp039CarrierCellLeft W c n) :
    ∀ x ∈ Set.Icc (cfzp040CarrierCellExpLeft W c n)
      (cfzp040CarrierCellExpRight W c n),
      DifferentiableAt ℝ
        (cfzp048PrimeAxisRemainderTestFunction W) x := by
  intro x hx
  exact (cfzp048PrimeAxisRemainderTestFunction_hasDerivAt W
    (cfzp053_late_mem_log_bounds W c n hU hx).2.1).differentiableAt

private theorem cfzp053_carrier_deriv_eq_formula_on_Icc
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) (hU : 2 ≤ cfzp039CarrierCellLeft W c n)
    {x : ℝ}
    (hx : x ∈ Set.Icc (cfzp040CarrierCellExpLeft W c n)
      (cfzp040CarrierCellExpRight W c n)) :
    deriv (cfzp040PrimeAxisCarrierTestFunction epsilon W) x =
      cfzp052CarrierDerivativeFormula epsilon W x := by
  have h := cfzp040PrimeAxisCarrierTestFunction_hasDerivAt hepsilon.ne'
    (cfzp053_late_mem_log_bounds W c n hU hx).1 W
  simpa [cfzp052CarrierDerivativeFormula] using h.deriv

private theorem cfzp053_remainder_deriv_eq_formula_on_Icc
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) (hU : 2 ≤ cfzp039CarrierCellLeft W c n)
    {x : ℝ}
    (hx : x ∈ Set.Icc (cfzp040CarrierCellExpLeft W c n)
      (cfzp040CarrierCellExpRight W c n)) :
    deriv (cfzp048PrimeAxisRemainderTestFunction W) x =
      cfzp048PrimeAxisRemainderTestDerivative W x := by
  exact (cfzp048PrimeAxisRemainderTestFunction_hasDerivAt W
    (cfzp053_late_mem_log_bounds W c n hU hx).2.1).deriv

/-! ## Gate D: derivative integrability on the closed cell -/

/-- The carrier derivative is integrable on the closed late cell. -/
theorem cfzp053CarrierDerivative_integrableOn_Icc
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hU : 2 ≤ cfzp039CarrierCellLeft W c n) :
    IntegrableOn
      (deriv (cfzp040PrimeAxisCarrierTestFunction epsilon W))
      (Set.Icc (cfzp040CarrierCellExpLeft W c n)
        (cfzp040CarrierCellExpRight W c n)) := by
  have hcont := cfzp052_carrierDerivativeFormula_continuousOn_cell
    hepsilon W c n (cfzp053_late_hU_one W c n hU)
  have hI : IntegrableOn
      (cfzp052CarrierDerivativeFormula epsilon W)
      (Set.Icc (cfzp040CarrierCellExpLeft W c n)
        (cfzp040CarrierCellExpRight W c n)) :=
    hcont.integrableOn_Icc
  apply hI.congr_fun
  · intro x hx
    exact (cfzp053_carrier_deriv_eq_formula_on_Icc hepsilon W c n hU hx).symm
  · exact measurableSet_Icc

/-- The remainder derivative is integrable on the closed late cell. -/
theorem cfzp053RemainderDerivative_integrableOn_Icc
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hU : 2 ≤ cfzp039CarrierCellLeft W c n) :
    IntegrableOn
      (deriv (cfzp048PrimeAxisRemainderTestFunction W))
      (Set.Icc (cfzp040CarrierCellExpLeft W c n)
        (cfzp040CarrierCellExpRight W c n)) := by
  have hcont := cfzp052_remainderDerivativeFormula_continuousOn_cell
    W c n (cfzp053_late_hU_one W c n hU)
  have hI : IntegrableOn
      (cfzp048PrimeAxisRemainderTestDerivative W)
      (Set.Icc (cfzp040CarrierCellExpLeft W c n)
        (cfzp040CarrierCellExpRight W c n)) :=
    hcont.integrableOn_Icc
  apply hI.congr_fun
  · intro x hx
    exact (cfzp053_remainder_deriv_eq_formula_on_Icc W c n hU hx).symm
  · exact measurableSet_Icc

/-! ## Gate E: smooth density regularity -/

private theorem cfzp053_smoothDensity_continuousOn_cell
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hU : 2 ≤ cfzp039CarrierCellLeft W c n) :
    ContinuousOn cfzp042PrimeCountingSmoothDensity
      (Set.Icc (cfzp040CarrierCellExpLeft W c n)
        (cfzp040CarrierCellExpRight W c n)) := by
  intro x hx
  have hgeom := cfzp053_late_mem_log_bounds W c n hU hx
  have hx0 : x ≠ 0 := ne_of_gt hgeom.1
  have hlog : ContinuousAt Real.log x := Real.continuousAt_log hx0
  have hlog0 : Real.log x ≠ 0 := ne_of_gt hgeom.2.2
  change ContinuousWithinAt
    (fun y => 1 / Real.log y - 1 / (Real.log y) ^ 2) _ x
  exact ((continuousAt_const.div hlog hlog0).sub
    (continuousAt_const.div (hlog.pow 2) (pow_ne_zero _ hlog0))).continuousWithinAt

/-- The elementary smooth density is interval-integrable on a late cell. -/
theorem cfzp053SmoothDensity_intervalIntegrable
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hU : 2 ≤ cfzp039CarrierCellLeft W c n) :
    IntervalIntegrable cfzp042PrimeCountingSmoothDensity volume
      (cfzp040CarrierCellExpLeft W c n)
      (cfzp040CarrierCellExpRight W c n) :=
  (cfzp053_smoothDensity_continuousOn_cell W c n hU).intervalIntegrable_of_Icc
    (cfzp053_late_exp_left_le_right W c n hU)

private theorem cfzp053_carrierSmooth_continuousOn_cell
    {epsilon : ℝ} (_hepsilon : 0 < epsilon)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hU : 2 ≤ cfzp039CarrierCellLeft W c n) :
    ContinuousOn
      (fun x => cfzp040PrimeAxisCarrierTestFunction epsilon W x *
        cfzp042PrimeCountingSmoothDensity x)
      (Set.Icc (cfzp040CarrierCellExpLeft W c n)
        (cfzp040CarrierCellExpRight W c n)) := by
  intro x hx
  have hgeom := cfzp053_late_mem_log_bounds W c n hU hx
  have hx0 : x ≠ 0 := ne_of_gt hgeom.1
  have hlog : ContinuousAt Real.log x := Real.continuousAt_log hx0
  have hlog0 : Real.log x ≠ 0 := ne_of_gt hgeom.2.2
  have hcarrier : ContinuousAt
      (cfzp040PrimeAxisCarrierTestFunction epsilon W) x := by
    unfold cfzp040PrimeAxisCarrierTestFunction
      cfzp036PrimeAxisLeadingPeriodicCarrier cfzp036LinearPhaseCore
    fun_prop
  have hdensity : ContinuousAt cfzp042PrimeCountingSmoothDensity x := by
    unfold cfzp042PrimeCountingSmoothDensity
    exact (continuousAt_const.div hlog hlog0).sub
      (continuousAt_const.div (hlog.pow 2) (pow_ne_zero _ hlog0))
  exact (hcarrier.mul hdensity).continuousWithinAt

private theorem cfzp053_remainderSmooth_continuousOn_cell
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hU : 2 ≤ cfzp039CarrierCellLeft W c n) :
    ContinuousOn
      (fun x => cfzp048PrimeAxisRemainderTestFunction W x *
        cfzp042PrimeCountingSmoothDensity x)
      (Set.Icc (cfzp040CarrierCellExpLeft W c n)
        (cfzp040CarrierCellExpRight W c n)) := by
  intro x hx
  have hgeom := cfzp053_late_mem_log_bounds W c n hU hx
  have hx0 : x ≠ 0 := ne_of_gt hgeom.1
  have hlog : ContinuousAt Real.log x := Real.continuousAt_log hx0
  have hlog0 : Real.log x ≠ 0 := ne_of_gt hgeom.2.2
  have hrem : ContinuousAt
      (cfzp048PrimeAxisRemainderTestFunction W) x := by
    unfold cfzp048PrimeAxisRemainderTestFunction
    exact (Real.continuous_exp.continuousAt.comp
      (by fun_prop)).div hlog hlog0
  have hdensity : ContinuousAt cfzp042PrimeCountingSmoothDensity x := by
    unfold cfzp042PrimeCountingSmoothDensity
    exact (continuousAt_const.div hlog hlog0).sub
      (continuousAt_const.div (hlog.pow 2) (pow_ne_zero _ hlog0))
  exact (hrem.mul hdensity).continuousWithinAt

private theorem cfzp053_smoothModel_continuousOn_cell
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hU : 2 ≤ cfzp039CarrierCellLeft W c n) :
    ContinuousOn cfzp040PrimeCountingSmoothModel
      (Set.Icc (cfzp040CarrierCellExpLeft W c n)
        (cfzp040CarrierCellExpRight W c n)) := by
  intro x hx
  have hgeom := cfzp053_late_mem_log_bounds W c n hU hx
  have hx0 : x ≠ 0 := ne_of_gt hgeom.1
  have hlog : ContinuousAt Real.log x := Real.continuousAt_log hx0
  have hlog0 : Real.log x ≠ 0 := ne_of_gt hgeom.2.2
  change ContinuousWithinAt (fun y => y / Real.log y) _ x
  exact (continuousAt_id.div hlog hlog0).continuousWithinAt

private theorem cfzp053_carrierDerivSmooth_continuousOn_cell
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hU : 2 ≤ cfzp039CarrierCellLeft W c n) :
    ContinuousOn
      (fun x => deriv (cfzp040PrimeAxisCarrierTestFunction epsilon W) x *
        cfzp040PrimeCountingSmoothModel x)
      (Set.Icc (cfzp040CarrierCellExpLeft W c n)
        (cfzp040CarrierCellExpRight W c n)) := by
  have hformula := cfzp052_carrierDerivativeFormula_continuousOn_cell
    hepsilon W c n (cfzp053_late_hU_one W c n hU)
  have hsmooth := cfzp053_smoothModel_continuousOn_cell W c n hU
  have hprod := hformula.mul hsmooth
  exact hprod.congr fun x hx => by
    rw [cfzp053_carrier_deriv_eq_formula_on_Icc hepsilon W c n hU hx]
    simp only [Pi.mul_apply]

private theorem cfzp053_remainderDerivSmooth_continuousOn_cell
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hU : 2 ≤ cfzp039CarrierCellLeft W c n) :
    ContinuousOn
      (fun x => deriv (cfzp048PrimeAxisRemainderTestFunction W) x *
        cfzp040PrimeCountingSmoothModel x)
      (Set.Icc (cfzp040CarrierCellExpLeft W c n)
        (cfzp040CarrierCellExpRight W c n)) := by
  have hformula := cfzp052_remainderDerivativeFormula_continuousOn_cell
    W c n (cfzp053_late_hU_one W c n hU)
  have hsmooth := cfzp053_smoothModel_continuousOn_cell W c n hU
  have hprod := hformula.mul hsmooth
  exact hprod.congr fun x hx => by
    rw [cfzp053_remainder_deriv_eq_formula_on_Icc W c n hU hx]
    simp only [Pi.mul_apply]

/-- Carrier derivative times the smooth counting model is integrable on one
late finite cell. -/
theorem cfzp053CarrierDerivativeMulSmooth_integrableOn
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hU : 2 ≤ cfzp039CarrierCellLeft W c n) :
    IntegrableOn
      (fun x => deriv (cfzp040PrimeAxisCarrierTestFunction epsilon W) x *
        cfzp040PrimeCountingSmoothModel x)
      (Set.Ioc (cfzp040CarrierCellExpLeft W c n)
        (cfzp040CarrierCellExpRight W c n)) := by
  have hI : IntegrableOn
      (fun x => deriv (cfzp040PrimeAxisCarrierTestFunction epsilon W) x *
        cfzp040PrimeCountingSmoothModel x)
      (Set.Icc (cfzp040CarrierCellExpLeft W c n)
        (cfzp040CarrierCellExpRight W c n)) :=
    ContinuousOn.integrableOn_Icc
      (cfzp053_carrierDerivSmooth_continuousOn_cell hepsilon W c n hU)
  exact hI.mono_set Ioc_subset_Icc_self

/-- Remainder derivative times the smooth counting model is integrable on one
late finite cell. -/
theorem cfzp053RemainderDerivativeMulSmooth_integrableOn
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hU : 2 ≤ cfzp039CarrierCellLeft W c n) :
    IntegrableOn
      (fun x => deriv (cfzp048PrimeAxisRemainderTestFunction W) x *
        cfzp040PrimeCountingSmoothModel x)
      (Set.Ioc (cfzp040CarrierCellExpLeft W c n)
        (cfzp040CarrierCellExpRight W c n)) := by
  have hI : IntegrableOn
      (fun x => deriv (cfzp048PrimeAxisRemainderTestFunction W) x *
        cfzp040PrimeCountingSmoothModel x)
      (Set.Icc (cfzp040CarrierCellExpLeft W c n)
        (cfzp040CarrierCellExpRight W c n)) :=
    ContinuousOn.integrableOn_Icc
      (cfzp053_remainderDerivSmooth_continuousOn_cell W c n hU)
  exact hI.mono_set Ioc_subset_Icc_self

private theorem cfzp053_exp_uIcc_subset_expCell
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (_hU : 2 ≤ cfzp039CarrierCellLeft W c n) :
    Real.exp '' Set.uIcc (cfzp039CarrierCellLeft W c n)
        (cfzp039CarrierCellRight W c n) ⊆
      Set.Icc (cfzp040CarrierCellExpLeft W c n)
        (cfzp040CarrierCellExpRight W c n) := by
  intro x hx
  rcases hx with ⟨u, hu, rfl⟩
  have hLR : cfzp039CarrierCellLeft W c n ≤
      cfzp039CarrierCellRight W c n := by
    apply Real.exp_le_exp.mp
    exact (cfzp040CarrierCellExpLeft_lt_right W c n).le
  have hu' := mem_uIcc.mp hu
  have huL : cfzp039CarrierCellLeft W c n ≤ u := by
    rcases hu' with h | h
    · exact h.1
    · exact le_trans hLR h.1
  have huR : u ≤ cfzp039CarrierCellRight W c n := by
    rcases hu' with h | h
    · exact h.2
    · exact le_trans h.2 hLR
  exact ⟨by
      simpa [cfzp040CarrierCellExpLeft] using Real.exp_le_exp.mpr huL,
    by simpa [cfzp040CarrierCellExpRight] using Real.exp_le_exp.mpr huR⟩

private theorem cfzp053_carrierDensity_exp_comp_integrableOn
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hU : 2 ≤ cfzp039CarrierCellLeft W c n) :
    IntegrableOn
      (fun u =>
        ((fun x => cfzp040PrimeAxisCarrierTestFunction epsilon W x *
          cfzp042PrimeCountingSmoothDensity x) ∘ Real.exp) u *
          Real.exp u)
      (Set.uIcc (cfzp039CarrierCellLeft W c n)
        (cfzp039CarrierCellRight W c n)) := by
  have hcont := cfzp053_carrierSmooth_continuousOn_cell
    hepsilon W c n hU
  have hcont' := hcont.mono (cfzp053_exp_uIcc_subset_expCell W c n hU)
  have hcomp := hcont'.comp Real.continuous_exp.continuousOn
    (fun u hu => ⟨u, hu, rfl⟩)
  have hcomp' : ContinuousOn
      (fun u =>
        ((fun x => cfzp040PrimeAxisCarrierTestFunction epsilon W x *
          cfzp042PrimeCountingSmoothDensity x) ∘ Real.exp) u *
          Real.exp u)
      (Set.uIcc (cfzp039CarrierCellLeft W c n)
        (cfzp039CarrierCellRight W c n)) := by
    exact hcomp.mul Real.continuous_exp.continuousOn
  exact hcomp'.integrableOn_uIcc

private theorem cfzp053_remainderDensity_exp_comp_integrableOn
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hU : 2 ≤ cfzp039CarrierCellLeft W c n) :
    IntegrableOn
      (fun u =>
        ((fun x => cfzp048PrimeAxisRemainderTestFunction W x *
          cfzp042PrimeCountingSmoothDensity x) ∘ Real.exp) u *
          Real.exp u)
      (Set.uIcc (cfzp039CarrierCellLeft W c n)
        (cfzp039CarrierCellRight W c n)) := by
  have hcont := cfzp053_remainderSmooth_continuousOn_cell W c n hU
  have hcont' := hcont.mono (cfzp053_exp_uIcc_subset_expCell W c n hU)
  have hcomp := hcont'.comp Real.continuous_exp.continuousOn
    (fun u hu => ⟨u, hu, rfl⟩)
  have hcomp' : ContinuousOn
      (fun u =>
        ((fun x => cfzp048PrimeAxisRemainderTestFunction W x *
          cfzp042PrimeCountingSmoothDensity x) ∘ Real.exp) u *
          Real.exp u)
      (Set.uIcc (cfzp039CarrierCellLeft W c n)
        (cfzp039CarrierCellRight W c n)) := by
    exact hcomp.mul Real.continuous_exp.continuousOn
  exact hcomp'.integrableOn_uIcc

/-! ## Gates F-G: automatic smooth Abel-to-log-cell bridges -/

/-- The carrier smooth Abel model is automatically identified with its
logarithmic-cell integral on every thresholded cell. -/
theorem cfzp053CarrierSmoothAbel_eq_logCell_auto
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hU : 2 ≤ cfzp039CarrierCellLeft W c n) :
    cfzp040SmoothAbelCarrierModel epsilon W
        (cfzp040CarrierCellExpLeft W c n)
        (cfzp040CarrierCellExpRight W c n) =
      cfzp042SmoothLogCellIntegral epsilon W c n := by
  let a := cfzp040CarrierCellExpLeft W c n
  let b := cfzp040CarrierCellExpRight W c n
  have hab : a ≤ b := cfzp053_late_exp_left_le_right W c n hU
  have ha : 1 < a := cfzp053_late_exp_left_gt_one W c n hU
  have hF : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (cfzp040PrimeAxisCarrierTestFunction epsilon W)
        (cfzp042CarrierTestFunctionDerivative epsilon W x) x := by
    intro x hx
    have hx' : x ∈ Set.Icc a b := by
      simpa [uIcc_of_le hab] using hx
    exact cfzp042CarrierTestFunction_hasDerivAt hepsilon.ne'
      (cfzp053_late_mem_log_bounds W c n hU hx').1 W
  have hM : ∀ x ∈ Set.uIcc a b,
      HasDerivAt cfzp040PrimeCountingSmoothModel
        (cfzp042PrimeCountingSmoothDensity x) x := by
    intro x hx
    have hx' : x ∈ Set.Icc a b := by
      simpa [uIcc_of_le hab] using hx
    exact cfzp042PrimeCountingSmoothModel_hasDerivAt
      (cfzp053_late_mem_log_bounds W c n hU hx').2.1
  have hF_int : IntervalIntegrable
      (cfzp042CarrierTestFunctionDerivative epsilon W) volume a b := by
    change IntervalIntegrable (cfzp052CarrierDerivativeFormula epsilon W)
      volume a b
    exact (cfzp052_carrierDerivativeFormula_continuousOn_cell hepsilon W c n
      (cfzp053_late_hU_one W c n hU)).intervalIntegrable_of_Icc hab
  have hM_int : IntervalIntegrable cfzp042PrimeCountingSmoothDensity
      volume a b := by
    simpa [a, b] using cfzp053SmoothDensity_intervalIntegrable W c n hU
  have hDensity := cfzp042SmoothAbelCarrierModel_eq_densityIntegral
    hepsilon.ne' ha hab W hF hM hF_int hM_int
  have hcont := cfzp053_carrierSmooth_continuousOn_cell
    hepsilon W c n hU
  have hcont' := hcont.mono (cfzp053_exp_uIcc_subset_expCell W c n hU)
  have hK : IsCompact
      (Real.exp '' Set.uIcc (cfzp039CarrierCellLeft W c n)
        (cfzp039CarrierCellRight W c n)) :=
    isCompact_uIcc.image Real.continuous_exp
  have hInt : IntegrableOn
      (fun x => cfzp040PrimeAxisCarrierTestFunction epsilon W x *
        cfzp042PrimeCountingSmoothDensity x)
      (Real.exp '' Set.uIcc (cfzp039CarrierCellLeft W c n)
        (cfzp039CarrierCellRight W c n)) :=
    ContinuousOn.integrableOn_compact hK hcont'
  have hCompInt := cfzp053_carrierDensity_exp_comp_integrableOn
    hepsilon W c n hU
  have hLog := cfzp042SmoothDensityIntegral_eq_logCellIntegral
    W c n (by linarith [cfzp039CarrierCellLeft W c n, hU])
    hDensity hcont' hInt hCompInt
  exact hLog

/-- The remainder smooth Abel model is automatically identified with its
logarithmic-cell integral on every thresholded cell. -/
theorem cfzp053RemainderSmoothAbel_eq_logCell_auto
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hU : 2 ≤ cfzp039CarrierCellLeft W c n) :
    cfzp048PrimeRemainderSmoothAbelModel W
        (cfzp040CarrierCellExpLeft W c n)
        (cfzp040CarrierCellExpRight W c n) =
      cfzp048PrimeRemainderSmoothLogCell W c n := by
  let a := cfzp040CarrierCellExpLeft W c n
  let b := cfzp040CarrierCellExpRight W c n
  have hab : a ≤ b := cfzp053_late_exp_left_le_right W c n hU
  have ha : 1 < a := cfzp053_late_exp_left_gt_one W c n hU
  have hF : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (cfzp048PrimeAxisRemainderTestFunction W)
        (cfzp048PrimeAxisRemainderTestDerivative W x) x := by
    intro x hx
    have hx' : x ∈ Set.Icc a b := by
      simpa [uIcc_of_le hab] using hx
    exact cfzp048PrimeAxisRemainderTestFunction_hasDerivAt W
      (cfzp053_late_mem_log_bounds W c n hU hx').2.1
  have hM : ∀ x ∈ Set.uIcc a b,
      HasDerivAt cfzp040PrimeCountingSmoothModel
        (cfzp042PrimeCountingSmoothDensity x) x := by
    intro x hx
    have hx' : x ∈ Set.Icc a b := by
      simpa [uIcc_of_le hab] using hx
    exact cfzp042PrimeCountingSmoothModel_hasDerivAt
      (cfzp053_late_mem_log_bounds W c n hU hx').2.1
  have hF_int : IntervalIntegrable
      (cfzp048PrimeAxisRemainderTestDerivative W) volume a b := by
    exact (cfzp052_remainderDerivativeFormula_continuousOn_cell W c n
      (cfzp053_late_hU_one W c n hU)).intervalIntegrable_of_Icc hab
  have hM_int : IntervalIntegrable cfzp042PrimeCountingSmoothDensity
      volume a b := by
    simpa [a, b] using cfzp053SmoothDensity_intervalIntegrable W c n hU
  have hDensity := cfzp048PrimeRemainderSmoothAbelModel_eq_densityIntegral
    ha hab W hF hM hF_int hM_int
  have hcont := cfzp053_remainderSmooth_continuousOn_cell W c n hU
  have hcont' := hcont.mono (cfzp053_exp_uIcc_subset_expCell W c n hU)
  have hK : IsCompact
      (Real.exp '' Set.uIcc (cfzp039CarrierCellLeft W c n)
        (cfzp039CarrierCellRight W c n)) :=
    isCompact_uIcc.image Real.continuous_exp
  have hInt : IntegrableOn
      (fun x => cfzp048PrimeAxisRemainderTestFunction W x *
        cfzp042PrimeCountingSmoothDensity x)
      (Real.exp '' Set.uIcc (cfzp039CarrierCellLeft W c n)
        (cfzp039CarrierCellRight W c n)) :=
    ContinuousOn.integrableOn_compact hK hcont'
  have hCompInt := cfzp053_remainderDensity_exp_comp_integrableOn W c n hU
  have hLog := cfzp048PrimeRemainderSmoothAbelCell_eq_logCell
    W c n (by linarith [cfzp039CarrierCellLeft W c n, hU])
    hDensity hcont' hInt hCompInt
  exact hLog

/-! ## Gates H-I: exact finite split and remaining analytic inputs -/

/-- The finite remainder Abel split is generated from the actual derivative
and the discrepancy integrability certificates. -/
theorem cfzp053PrimeRemainderSum_eq_smooth_add_discrepancy_auto
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hU : 2 ≤ cfzp039CarrierCellLeft W c n) :
    cfzp048PrimeRemainderSumIoc W
        (cfzp040CarrierCellExpLeft W c n)
        (cfzp040CarrierCellExpRight W c n) =
      cfzp048PrimeRemainderSmoothAbelModel W
        (cfzp040CarrierCellExpLeft W c n)
        (cfzp040CarrierCellExpRight W c n) +
      cfzp048PrimeRemainderCellDiscrepancyFunctional W c n := by
  let a := cfzp040CarrierCellExpLeft W c n
  let b := cfzp040CarrierCellExpRight W c n
  have hab : a ≤ b := cfzp053_late_exp_left_le_right W c n hU
  have ha : 1 < a := cfzp053_late_exp_left_gt_one W c n hU
  have hdiff := cfzp053RemainderTestFunction_differentiableOn_cell W c n hU
  have hf_diff : ∀ t ∈ Set.Icc a b,
      DifferentiableAt ℝ (cfzp048PrimeAxisRemainderTestFunction W) t := by
    intro t ht
    exact hdiff t (by simpa [a, b] using ht)
  have hf_int : IntegrableOn
      (deriv (cfzp048PrimeAxisRemainderTestFunction W)) (Set.Icc a b) := by
    simpa [a, b] using cfzp053RemainderDerivative_integrableOn_Icc W c n hU
  have hM_int := cfzp053RemainderDerivativeMulSmooth_integrableOn W c n hU
  have hD_int := cfzp052RemainderDerivativeMulDiscrepancy_integrableOn W c n
    (cfzp053_late_hU_one W c n hU)
  have hsplit := cfzp048PrimeRemainderSumIoc_eq_smooth_add_discrepancy
    ha hab W hf_diff hf_int hM_int hD_int
  simpa [a, b, cfzp048PrimeRemainderCellDiscrepancyFunctional] using hsplit

/-- The smooth remainder logarithmic integrand is interval-integrable on a
late finite cell. -/
theorem cfzp053RemainderSmoothLogIntegrand_intervalIntegrable
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hU : 2 ≤ cfzp039CarrierCellLeft W c n) :
    IntervalIntegrable
      (fun u => Real.exp (cfzp039PrimeAxisGrowthExponent W * u) *
        (1 / u ^ 2 - 1 / u ^ 3)) volume
      (cfzp039CarrierCellLeft W c n)
      (cfzp039CarrierCellRight W c n) := by
  have hLR : cfzp039CarrierCellLeft W c n ≤
      cfzp039CarrierCellRight W c n := by
    apply Real.exp_le_exp.mp
    exact (cfzp040CarrierCellExpLeft_lt_right W c n).le
  have hcont : ContinuousOn
      (fun u => Real.exp (cfzp039PrimeAxisGrowthExponent W * u) *
        (1 / u ^ 2 - 1 / u ^ 3))
      (Set.Icc (cfzp039CarrierCellLeft W c n)
        (cfzp039CarrierCellRight W c n)) := by
    intro u hu
    have hu0 : 0 < u := by
      exact lt_of_lt_of_le (by linarith) hu.1
    have hne : u ≠ 0 := ne_of_gt hu0
    have harg : ContinuousAt
        (fun y => cfzp039PrimeAxisGrowthExponent W * y) u := by
      fun_prop
    have hexp : ContinuousAt
        (fun y => Real.exp (cfzp039PrimeAxisGrowthExponent W * y)) u :=
      Real.continuous_exp.continuousAt.comp harg
    have hinv2 : ContinuousAt (fun y : ℝ => 1 / y ^ 2) u := by
      exact continuousAt_const.div (continuousAt_id.pow 2)
        (pow_ne_zero _ hne)
    have hinv3 : ContinuousAt (fun y : ℝ => 1 / y ^ 3) u := by
      exact continuousAt_const.div (continuousAt_id.pow 3)
        (pow_ne_zero _ hne)
    exact (hexp.mul (hinv2.sub hinv3)).continuousWithinAt
  exact hcont.intervalIntegrable_of_Icc hLR

/-! ## Gate J: aggregate finite smooth readiness -/

/-- All finite smooth-Abel certificates required by the radial adapter. -/
structure Cfzp053FiniteSmoothRadialReadyAt
    (epsilon : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) : Prop where
  smoothLog :
    cfzp040SmoothAbelCarrierModel epsilon W
        (cfzp040CarrierCellExpLeft W c n)
        (cfzp040CarrierCellExpRight W c n) =
      cfzp042SmoothLogCellIntegral epsilon W c n
  remainderSplit :
    cfzp048PrimeRemainderSumIoc W
        (cfzp040CarrierCellExpLeft W c n)
        (cfzp040CarrierCellExpRight W c n) =
      cfzp048PrimeRemainderSmoothAbelModel W
        (cfzp040CarrierCellExpLeft W c n)
        (cfzp040CarrierCellExpRight W c n) +
      cfzp048PrimeRemainderCellDiscrepancyFunctional W c n
  remainderDebtEq :
    cfzp039PrimeAxisRemainderCellDebt epsilon W c n
        (cfzp040CarrierCellNaturalLeft W c n)
        (cfzp040CarrierCellNaturalRight W c n) =
      cfzp036PrimeAxisRemainderConstant epsilon W *
        cfzp048PrimeRemainderSumIoc W
          (cfzp040CarrierCellExpLeft W c n)
          (cfzp040CarrierCellExpRight W c n)
  remainderSmoothEq :
    cfzp048PrimeRemainderSmoothAbelModel W
        (cfzp040CarrierCellExpLeft W c n)
        (cfzp040CarrierCellExpRight W c n) =
      cfzp048PrimeRemainderSmoothLogCell W c n
  carrierDiff : ∀ t ∈ Set.Icc
      (cfzp040CarrierCellExpLeft W c n)
      (cfzp040CarrierCellExpRight W c n),
      DifferentiableAt ℝ (cfzp040PrimeAxisCarrierTestFunction epsilon W) t
  carrierDerivInt : IntegrableOn
      (deriv (cfzp040PrimeAxisCarrierTestFunction epsilon W))
      (Set.Icc (cfzp040CarrierCellExpLeft W c n)
        (cfzp040CarrierCellExpRight W c n))
  carrierDerivSmoothInt : IntegrableOn
      (fun t => deriv (cfzp040PrimeAxisCarrierTestFunction epsilon W) t *
        cfzp040PrimeCountingSmoothModel t)
      (Set.Ioc (cfzp040CarrierCellExpLeft W c n)
        (cfzp040CarrierCellExpRight W c n))
  carrierDerivDiscInt : IntegrableOn
      (fun t => deriv (cfzp040PrimeAxisCarrierTestFunction epsilon W) t *
        cfzp040PrimeCountingDiscrepancy t)
      (Set.Ioc (cfzp040CarrierCellExpLeft W c n)
        (cfzp040CarrierCellExpRight W c n))
  remainderDiff : ∀ t ∈ Set.Icc
      (cfzp040CarrierCellExpLeft W c n)
      (cfzp040CarrierCellExpRight W c n),
      DifferentiableAt ℝ (cfzp048PrimeAxisRemainderTestFunction W) t
  remainderDerivInt : IntegrableOn
      (deriv (cfzp048PrimeAxisRemainderTestFunction W))
      (Set.Icc (cfzp040CarrierCellExpLeft W c n)
        (cfzp040CarrierCellExpRight W c n))
  remainderDerivSmoothInt : IntegrableOn
      (fun t => deriv (cfzp048PrimeAxisRemainderTestFunction W) t *
        cfzp040PrimeCountingSmoothModel t)
      (Set.Ioc (cfzp040CarrierCellExpLeft W c n)
        (cfzp040CarrierCellExpRight W c n))
  remainderDerivDiscInt : IntegrableOn
      (fun t => deriv (cfzp048PrimeAxisRemainderTestFunction W) t *
        cfzp040PrimeCountingDiscrepancy t)
      (Set.Ioc (cfzp040CarrierCellExpLeft W c n)
        (cfzp040CarrierCellExpRight W c n))
  remainderLogInt : IntervalIntegrable
      (fun u => Real.exp (cfzp039PrimeAxisGrowthExponent W * u) *
        (1 / u ^ 2 - 1 / u ^ 3)) volume
      (cfzp039CarrierCellLeft W c n)
      (cfzp039CarrierCellRight W c n)

/-- The finite smooth readiness structure is generated from the quarter
threshold; no smooth-Abel certificate is supplied by the caller. -/
theorem cfzp053FiniteSmoothRadialReadyAt_of_threshold
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hThreshold : cfzp048PrimeAxisRemainderQuarterMarginThreshold epsilon W c ≤
      cfzp039CarrierCellLeft W c n) :
    Cfzp053FiniteSmoothRadialReadyAt epsilon W c n := by
  have hLate : cfzp044RadialLateThreshold epsilon W c ≤
      cfzp039CarrierCellLeft W c n :=
    le_trans (le_max_left _ _) hThreshold
  have hU : 2 ≤ cfzp039CarrierCellLeft W c n :=
    cfzp044_two_le_of_radialLate hLate
  refine ⟨cfzp053CarrierSmoothAbel_eq_logCell_auto hepsilon W c n hU,
    cfzp053PrimeRemainderSum_eq_smooth_add_discrepancy_auto W c n hU,
    cfzp048PrimeAxisRemainderCellDebt_eq_constant_mul_primeRemainderSum
      hepsilon W c n hLate,
    cfzp053RemainderSmoothAbel_eq_logCell_auto W c n hU,
    cfzp053CarrierTestFunction_differentiableOn_cell hepsilon W c n hU,
    cfzp053CarrierDerivative_integrableOn_Icc hepsilon W c n hU,
    cfzp053CarrierDerivativeMulSmooth_integrableOn hepsilon W c n hU,
    cfzp052CarrierDerivativeMulDiscrepancy_integrableOn hepsilon W c n
      (cfzp053_late_hU_one W c n hU),
    cfzp053RemainderTestFunction_differentiableOn_cell W c n hU,
    cfzp053RemainderDerivative_integrableOn_Icc W c n hU,
    cfzp053RemainderDerivativeMulSmooth_integrableOn W c n hU,
    cfzp052RemainderDerivativeMulDiscrepancy_integrableOn W c n
      (cfzp053_late_hU_one W c n hU),
    cfzp053RemainderSmoothLogIntegrand_intervalIntegrable W c n hU⟩

/-! ## Gate K: exact contiguity of adjacent carrier cells -/

/-- The right logarithmic endpoint of one carrier cell is the next left
endpoint. -/
theorem cfzp053CarrierCellRight_eq_nextLeft
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) :
    cfzp039CarrierCellRight W c n =
      cfzp039CarrierCellLeft W c (n + 1) := by
  unfold cfzp039CarrierCellRight cfzp039CarrierCellLeft
  norm_num [Nat.cast_add]

/-- The exponential endpoints of adjacent carrier cells agree exactly. -/
theorem cfzp053CarrierCellExpRight_eq_nextExpLeft
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) :
    cfzp040CarrierCellExpRight W c n =
      cfzp040CarrierCellExpLeft W c (n + 1) := by
  unfold cfzp040CarrierCellExpRight cfzp040CarrierCellExpLeft
  rw [cfzp053CarrierCellRight_eq_nextLeft W c n]

/-- The natural endpoints of adjacent carrier cells agree exactly. -/
theorem cfzp053CarrierCellNaturalRight_eq_nextNaturalLeft
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) :
    cfzp040CarrierCellNaturalRight W c n =
      cfzp040CarrierCellNaturalLeft W c (n + 1) := by
  unfold cfzp040CarrierCellNaturalRight cfzp040CarrierCellNaturalLeft
  rw [cfzp053CarrierCellExpRight_eq_nextExpLeft W c n]

/-! ## Gates L-M: one-cell descent and left-to-next-left recurrence -/

/-- The combined discrepancy eighth-credit yields an actual one-cell radial
deficit decrease after the finite smooth certificates are generated. -/
theorem cfzp053_oneCell_radialDeficit_le_sub_eighthMargin
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon2 : epsilon < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hstrip : Cfzp039PrimeAxisInteriorStrip W)
    (hM : 0 < cfzp039ExponentialCarrierPeriodTransform epsilon W c)
    (hThreshold :
      cfzp048PrimeAxisRemainderQuarterMarginThreshold epsilon W c ≤
        cfzp039CarrierCellLeft W c n)
    (hHigher :
      cfzp034HigherPowerReferenceMass epsilon W
          (cfzp040CarrierCellNaturalLeft W c n)
          (cfzp040CarrierCellNaturalRight W c n) ≤
        cfzp044ExplicitSmoothMargin epsilon W c n / 2)
    (hDisc :
      cfzp049CombinedPrimeCountingDiscrepancyCellDebt epsilon W c n ≤
        cfzp044ExplicitSmoothMargin epsilon W c n / 8) :
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit epsilon W
        (cfzp040CarrierCellNaturalRight W c n) ≤
      pascalCenteredXiPrimeSideFiniteRadialContactDeficit epsilon W
          (cfzp040CarrierCellNaturalLeft W c n) -
        cfzp044ExplicitSmoothMargin epsilon W c n / 8 := by
  let G := pascalCenteredXiPrimeSideFiniteRadialContactDeficit epsilon W
      (cfzp040CarrierCellNaturalLeft W c n)
  let M := cfzp044ExplicitSmoothMargin epsilon W c n
  let eta := G - M / 8
  have hready := cfzp053FiniteSmoothRadialReadyAt_of_threshold
    hepsilon W c n hThreshold
  have hQuarter : Cfzp049CombinedRemainingQuarterBudgetAt epsilon eta W c n := by
    unfold Cfzp049CombinedRemainingQuarterBudgetAt eta G M
    linarith
  have hEnd := cfzp049CombinedRemainingQuarterBudget_implies_radialContactDeficit_le
    hepsilon hepsilon2 W c n hstrip hM hThreshold
    hready.remainderLogInt hready.remainderSplit hready.remainderDebtEq
    hready.remainderSmoothEq hready.smoothLog hready.carrierDiff
    hready.carrierDerivInt hready.carrierDerivSmoothInt
    hready.carrierDerivDiscInt hHigher hQuarter
  simpa [G, M, eta] using hEnd

/-- Canonical left-radial deficit associated with the translated carrier
cell index. -/
noncomputable def cfzp053LeftRadialDeficit
    (epsilon : ℝ)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) : ℝ :=
  pascalCenteredXiPrimeSideFiniteRadialContactDeficit epsilon W
    (cfzp040CarrierCellNaturalLeft W c n)

/-- The one-cell descent is the next-left recurrence after exact endpoint
contiguity is applied. -/
theorem cfzp053_leftRadialDeficit_succ_le_sub_eighthMargin
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon2 : epsilon < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hstrip : Cfzp039PrimeAxisInteriorStrip W)
    (hM : 0 < cfzp039ExponentialCarrierPeriodTransform epsilon W c)
    (hThreshold :
      cfzp048PrimeAxisRemainderQuarterMarginThreshold epsilon W c ≤
        cfzp039CarrierCellLeft W c n)
    (hHigher :
      cfzp034HigherPowerReferenceMass epsilon W
          (cfzp040CarrierCellNaturalLeft W c n)
          (cfzp040CarrierCellNaturalRight W c n) ≤
        cfzp044ExplicitSmoothMargin epsilon W c n / 2)
    (hDisc :
      cfzp049CombinedPrimeCountingDiscrepancyCellDebt epsilon W c n ≤
        cfzp044ExplicitSmoothMargin epsilon W c n / 8) :
    cfzp053LeftRadialDeficit epsilon W c (n + 1) ≤
      cfzp053LeftRadialDeficit epsilon W c n -
        cfzp044ExplicitSmoothMargin epsilon W c n / 8 := by
  have h := cfzp053_oneCell_radialDeficit_le_sub_eighthMargin
    hepsilon hepsilon2 W c n hstrip hM hThreshold hHigher hDisc
  unfold cfzp053LeftRadialDeficit
  rw [← cfzp053CarrierCellNaturalRight_eq_nextNaturalLeft W c n]
  exact h

/-! ## Gate N: eventual recurrence under the PNT ratio provider -/

/-- The PNT ratio provider yields an eventual radial eighth recurrence after
the explicit interior-strip and subcritical-window hypotheses are supplied. -/
theorem cfzp053_pntRatio_eventually_leftRadialDeficit_succ_le_sub_eighthMargin
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon2 : epsilon < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    (hstrip : Cfzp039PrimeAxisInteriorStrip W)
    (hsub : Cfzp027SubcriticalPhaseAspect W)
    (c : ℝ)
    (hM : 0 < cfzp039ExponentialCarrierPeriodTransform epsilon W c)
    (hPNT : Cfzp051PrimeCountingPNTRatioAtTop) :
    ∀ᶠ n : ℕ in Filter.atTop,
      cfzp053LeftRadialDeficit epsilon W c (n + 1) ≤
        cfzp053LeftRadialDeficit epsilon W c n -
          cfzp044ExplicitSmoothMargin epsilon W c n / 8 := by
  have hDisc := cfzp052_pntRatio_eventually_combinedDebt_le_eighthMargin_autoReady
    hepsilon W c hM hPNT
  obtain ⟨N, hN⟩ := cfzp048_eventually_higherPowerHalf_and_remainderQuarterLate
    hepsilon hepsilon2 W hsub c hM
  filter_upwards [hDisc, Filter.eventually_ge_atTop N] with n hn hNn
  exact cfzp053_leftRadialDeficit_succ_le_sub_eighthMargin
    hepsilon hepsilon2 W c n hstrip hM (hN n hNn).1 (hN n hNn).2 hn

/-! ## Gate O: finite telescoping -/

/-- A finite block of the radial recurrence telescopes against the sum of
the intervening explicit smooth margins. -/
theorem cfzp053_leftRadialDeficit_iterate_le_sub_sum
    {epsilon : ℝ}
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (N m : ℕ)
    (hstep : ∀ k : ℕ, N ≤ k →
      cfzp053LeftRadialDeficit epsilon W c (k + 1) ≤
        cfzp053LeftRadialDeficit epsilon W c k -
          cfzp044ExplicitSmoothMargin epsilon W c k / 8) :
    cfzp053LeftRadialDeficit epsilon W c (N + m) ≤
      cfzp053LeftRadialDeficit epsilon W c N -
        ∑ k ∈ Finset.range m,
          cfzp044ExplicitSmoothMargin epsilon W c (N + k) / 8 := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hrec := hstep (N + m) (by omega)
      calc
        cfzp053LeftRadialDeficit epsilon W c (N + (m + 1)) =
            cfzp053LeftRadialDeficit epsilon W c ((N + m) + 1) := by
              rfl
        _ ≤ cfzp053LeftRadialDeficit epsilon W c (N + m) -
              cfzp044ExplicitSmoothMargin epsilon W c (N + m) / 8 := hrec
        _ ≤ (cfzp053LeftRadialDeficit epsilon W c N -
              ∑ k ∈ Finset.range m,
                cfzp044ExplicitSmoothMargin epsilon W c (N + k) / 8) -
              cfzp044ExplicitSmoothMargin epsilon W c (N + m) / 8 :=
          sub_le_sub_right ih _
        _ = cfzp053LeftRadialDeficit epsilon W c N -
              ∑ k ∈ Finset.range (m + 1),
                cfzp044ExplicitSmoothMargin epsilon W c (N + k) / 8 := by
          rw [Finset.sum_range_succ]
          ring

/-! ## Explicit firewall -/

/-- Providers that remain after finite smooth readiness and one-cell descent
have been closed. -/
inductive Cfzp053FiniteSmoothAbelReadinessRadialEighthDescentGap : Prop
  | noPrimeCountingPNTRatioProvider
  | noAutomaticInteriorStripWindowProvider
  | noAutomaticSubcriticalAspectProvider

end DkMath.RH.CFBRCProjection
