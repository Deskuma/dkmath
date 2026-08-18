/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.RH.CFBRC.CosmicFormulaZetaHigherPrimePowerCompetitionDecayAudit
import Mathlib.NumberTheory.AbelSummation
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CosmicFormulaZetaPrimeAxisRemainderAbelSmoothDiscrepancyAudit"

/-!
# CFZP-048: finite Abel reduction of the prime-axis remainder

The `K / log p` remainder is not bounded by a distribution-free count.  This
module instead exposes its finite Abel decomposition into an elementary smooth
model and a named prime-counting discrepancy functional.  The smooth part is
then treated by finite real analysis; no prime-distribution asymptotic is
introduced.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.NumberTheory
open MeasureTheory
open Set

/-! ## Gates A-B: test function and finite Abel identity -/

/-- The scalar x-axis test function for the `K / log p` remainder. -/
noncomputable def cfzp048PrimeAxisRemainderTestFunction
    (W : PascalCenteredXiResidueTransportWindow)
    (x : ℝ) : ℝ :=
  Real.exp (-(W.rectangle.σ) * Real.log x) / Real.log x

/-- The derivative of the remainder test function on the region `x > 1`. -/
noncomputable def cfzp048PrimeAxisRemainderTestDerivative
    (W : PascalCenteredXiResidueTransportWindow)
    (x : ℝ) : ℝ :=
  -(Real.exp (-(W.rectangle.σ) * Real.log x) / x) *
    (W.rectangle.σ / Real.log x + 1 / (Real.log x)^2)

/-- At a prime, the test function is the sigma weight divided by `log p`. -/
theorem cfzp048PrimeAxisRemainderTestFunction_natPrime
    (W : PascalCenteredXiResidueTransportWindow)
    {p : ℕ} (_hp : Nat.Prime p) :
    cfzp048PrimeAxisRemainderTestFunction W (p : ℝ) =
      cfzp034PrimeAxisSigmaWeight W p / Real.log (p : ℝ) := by
  rfl

/-- Exact derivative certificate for the remainder test function. -/
theorem cfzp048PrimeAxisRemainderTestFunction_hasDerivAt
    (W : PascalCenteredXiResidueTransportWindow)
    {x : ℝ} (hx : 1 < x) :
    HasDerivAt (cfzp048PrimeAxisRemainderTestFunction W)
      (cfzp048PrimeAxisRemainderTestDerivative W x) x := by
  have hx0 : x ≠ 0 := ne_of_gt (lt_trans (by norm_num) hx)
  have hlog : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx0
  have hlog_pos : 0 < Real.log x := Real.log_pos hx
  have hlog_ne : Real.log x ≠ 0 := ne_of_gt hlog_pos
  have hinner : HasDerivAt (fun y : ℝ => -(W.rectangle.σ) * Real.log y)
      (-(W.rectangle.σ) * x⁻¹) x := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      hlog.const_mul (-(W.rectangle.σ))
  have hexp := (Real.hasDerivAt_exp
    (-(W.rectangle.σ) * Real.log x)).comp x hinner
  have hdiv := hexp.div hlog hlog_ne
  apply hdiv.congr_deriv
  simp only [Function.comp_apply]
  unfold cfzp048PrimeAxisRemainderTestDerivative
  field_simp [hx0, hlog_ne]
  ring

/-- The finite prime remainder sum over a real `Ioc` interval. -/
noncomputable def cfzp048PrimeRemainderSumIoc
    (W : PascalCenteredXiResidueTransportWindow)
    (a b : ℝ) : ℝ :=
  ∑ k ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊,
    cfzp048PrimeAxisRemainderTestFunction W (k : ℝ) *
      cfzp040PrimeIndicator k

/-- Abel's finite endpoint-minus-integral identity for the remainder sum. -/
theorem cfzp048PrimeRemainderSumIoc_eq_abel
    {a b : ℝ} (ha : 1 < a) (hab : a ≤ b)
    (W : PascalCenteredXiResidueTransportWindow)
    (hf_diff : ∀ t ∈ Set.Icc a b,
      DifferentiableAt ℝ (cfzp048PrimeAxisRemainderTestFunction W) t)
    (hf_int : IntegrableOn
      (deriv (cfzp048PrimeAxisRemainderTestFunction W)) (Set.Icc a b)) :
    cfzp048PrimeRemainderSumIoc W a b =
      cfzp048PrimeAxisRemainderTestFunction W b *
          (Nat.primeCounting ⌊b⌋₊ : ℝ) -
        cfzp048PrimeAxisRemainderTestFunction W a *
          (Nat.primeCounting ⌊a⌋₊ : ℝ) -
        ∫ t in Set.Ioc a b,
          deriv (cfzp048PrimeAxisRemainderTestFunction W) t *
            (Nat.primeCounting ⌊t⌋₊ : ℝ) := by
  classical
  unfold cfzp048PrimeRemainderSumIoc
  have habel := sum_mul_eq_sub_sub_integral_mul
    (fun n : ℕ => cfzp040PrimeIndicator n)
    (f := cfzp048PrimeAxisRemainderTestFunction W)
    (show 0 ≤ a by linarith) hab hf_diff hf_int
  rw [habel]
  simp_rw [cfzp040_sum_primeIndicator_eq_primeCounting]

/-! ## Gate D: smooth model and discrepancy functional -/

/-- The smooth Abel model for the remainder test function. -/
noncomputable def cfzp048PrimeRemainderSmoothAbelModel
    (W : PascalCenteredXiResidueTransportWindow)
    (a b : ℝ) : ℝ :=
  cfzp048PrimeAxisRemainderTestFunction W b *
      cfzp040PrimeCountingSmoothModel b -
    cfzp048PrimeAxisRemainderTestFunction W a *
      cfzp040PrimeCountingSmoothModel a -
    ∫ t in Set.Ioc a b,
      deriv (cfzp048PrimeAxisRemainderTestFunction W) t *
        cfzp040PrimeCountingSmoothModel t

/-- The finite remainder discrepancy functional. -/
noncomputable def cfzp048PrimeRemainderDiscrepancyFunctional
    (W : PascalCenteredXiResidueTransportWindow)
    (a b : ℝ) : ℝ :=
  cfzp048PrimeAxisRemainderTestFunction W b *
      cfzp040PrimeCountingDiscrepancy b -
    cfzp048PrimeAxisRemainderTestFunction W a *
      cfzp040PrimeCountingDiscrepancy a -
    ∫ t in Set.Ioc a b,
      deriv (cfzp048PrimeAxisRemainderTestFunction W) t *
        cfzp040PrimeCountingDiscrepancy t

/-- The finite prime remainder sum splits exactly into smooth plus discrepancy. -/
theorem cfzp048PrimeRemainderSumIoc_eq_smooth_add_discrepancy
    {a b : ℝ} (ha : 1 < a) (hab : a ≤ b)
    (W : PascalCenteredXiResidueTransportWindow)
    (hf_diff : ∀ t ∈ Set.Icc a b,
      DifferentiableAt ℝ (cfzp048PrimeAxisRemainderTestFunction W) t)
    (hf_int : IntegrableOn
      (deriv (cfzp048PrimeAxisRemainderTestFunction W)) (Set.Icc a b))
    (hM_int : IntegrableOn
      (fun t => deriv (cfzp048PrimeAxisRemainderTestFunction W) t *
        cfzp040PrimeCountingSmoothModel t) (Set.Ioc a b))
    (hD_int : IntegrableOn
      (fun t => deriv (cfzp048PrimeAxisRemainderTestFunction W) t *
        cfzp040PrimeCountingDiscrepancy t) (Set.Ioc a b)) :
    cfzp048PrimeRemainderSumIoc W a b =
      cfzp048PrimeRemainderSmoothAbelModel W a b +
        cfzp048PrimeRemainderDiscrepancyFunctional W a b := by
  have habel := cfzp048PrimeRemainderSumIoc_eq_abel
    ha hab W hf_diff hf_int
  have hsplit :
      (fun t => deriv (cfzp048PrimeAxisRemainderTestFunction W) t *
          (Nat.primeCounting ⌊t⌋₊ : ℝ)) =
        (fun t => deriv (cfzp048PrimeAxisRemainderTestFunction W) t *
            cfzp040PrimeCountingSmoothModel t) +
          (fun t => deriv (cfzp048PrimeAxisRemainderTestFunction W) t *
            cfzp040PrimeCountingDiscrepancy t) := by
    funext t
    rw [cfzp040PrimeCounting_eq_smooth_add_discrepancy]
    simp only [Pi.add_apply]
    ring
  have hint :
      (∫ t in Set.Ioc a b,
          deriv (cfzp048PrimeAxisRemainderTestFunction W) t *
            (Nat.primeCounting ⌊t⌋₊ : ℝ)) =
        (∫ t in Set.Ioc a b,
            deriv (cfzp048PrimeAxisRemainderTestFunction W) t *
              cfzp040PrimeCountingSmoothModel t) +
          (∫ t in Set.Ioc a b,
            deriv (cfzp048PrimeAxisRemainderTestFunction W) t *
              cfzp040PrimeCountingDiscrepancy t) := by
    rw [show (fun t => deriv (cfzp048PrimeAxisRemainderTestFunction W) t *
          (Nat.primeCounting ⌊t⌋₊ : ℝ)) = _ from hsplit]
    exact MeasureTheory.integral_add hM_int hD_int
  unfold cfzp048PrimeRemainderSmoothAbelModel
    cfzp048PrimeRemainderDiscrepancyFunctional
  rw [habel, hint]
  simp_rw [cfzp040PrimeCounting_eq_smooth_add_discrepancy]
  ring

/-! ## Gates E-F: density and logarithmic-cell forms -/

/-- The smooth Abel model written as a finite density integral. -/
theorem cfzp048PrimeRemainderSmoothAbelModel_eq_densityIntegral
    {a b : ℝ} (_ha : 1 < a) (hab : a ≤ b)
    (W : PascalCenteredXiResidueTransportWindow)
    (hF : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (cfzp048PrimeAxisRemainderTestFunction W)
        (cfzp048PrimeAxisRemainderTestDerivative W x) x)
    (hM : ∀ x ∈ Set.uIcc a b,
      HasDerivAt cfzp040PrimeCountingSmoothModel
        (cfzp042PrimeCountingSmoothDensity x) x)
    (hF_int : IntervalIntegrable
      (cfzp048PrimeAxisRemainderTestDerivative W) volume a b)
    (hM_int : IntervalIntegrable
      cfzp042PrimeCountingSmoothDensity volume a b) :
    cfzp048PrimeRemainderSmoothAbelModel W a b =
      ∫ x in Set.Ioc a b,
        cfzp048PrimeAxisRemainderTestFunction W x *
          cfzp042PrimeCountingSmoothDensity x := by
  have hderiv_eq : ∀ x ∈ Set.uIcc a b,
      deriv (cfzp048PrimeAxisRemainderTestFunction W) x =
        cfzp048PrimeAxisRemainderTestDerivative W x := by
    intro x hx
    exact (hF x hx).deriv
  have hreplace :
      (∫ x in Set.Ioc a b,
        deriv (cfzp048PrimeAxisRemainderTestFunction W) x *
          cfzp040PrimeCountingSmoothModel x) =
        ∫ x in Set.Ioc a b,
          cfzp048PrimeAxisRemainderTestDerivative W x *
            cfzp040PrimeCountingSmoothModel x := by
    calc
      (∫ x in Set.Ioc a b,
          deriv (cfzp048PrimeAxisRemainderTestFunction W) x *
            cfzp040PrimeCountingSmoothModel x) =
          ∫ x in a..b,
            deriv (cfzp048PrimeAxisRemainderTestFunction W) x *
              cfzp040PrimeCountingSmoothModel x :=
        (intervalIntegral.integral_of_le hab).symm
      _ = ∫ x in a..b,
          cfzp048PrimeAxisRemainderTestDerivative W x *
            cfzp040PrimeCountingSmoothModel x := by
        apply intervalIntegral.integral_congr
        intro x hx
        change deriv (cfzp048PrimeAxisRemainderTestFunction W) x *
          cfzp040PrimeCountingSmoothModel x = _
        rw [hderiv_eq x hx]
      _ = ∫ x in Set.Ioc a b,
          cfzp048PrimeAxisRemainderTestDerivative W x *
            cfzp040PrimeCountingSmoothModel x :=
        intervalIntegral.integral_of_le hab
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := cfzp048PrimeAxisRemainderTestFunction W)
    (u' := cfzp048PrimeAxisRemainderTestDerivative W)
    (v := cfzp040PrimeCountingSmoothModel)
    (v' := cfzp042PrimeCountingSmoothDensity)
    hF hM hF_int hM_int
  unfold cfzp048PrimeRemainderSmoothAbelModel
  rw [hreplace]
  simpa only [intervalIntegral.integral_of_le hab] using hparts.symm

/-- The smooth remainder integrand after the logarithmic substitution. -/
noncomputable def cfzp048PrimeRemainderSmoothLogCell
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) : ℝ :=
  ∫ u in cfzp039CarrierCellLeft W c n..cfzp039CarrierCellRight W c n,
    Real.exp (cfzp039PrimeAxisGrowthExponent W * u) *
      (1 / u ^ 2 - 1 / u ^ 3)

/-- The density integrand transforms exactly to the smooth remainder cell. -/
theorem cfzp048_smoothDensity_exp_integrand_eq_logCellIntegrand
    (W : PascalCenteredXiResidueTransportWindow) (u : ℝ) :
    (cfzp048PrimeAxisRemainderTestFunction W (Real.exp u) *
        cfzp042PrimeCountingSmoothDensity (Real.exp u)) * Real.exp u =
      Real.exp (cfzp039PrimeAxisGrowthExponent W * u) *
        (1 / u ^ 2 - 1 / u ^ 3) := by
  unfold cfzp048PrimeAxisRemainderTestFunction
    cfzp042PrimeCountingSmoothDensity cfzp039PrimeAxisGrowthExponent
  simp only [Real.log_exp]
  by_cases hu : u = 0
  · simp [hu]
  · field_simp [hu]
    calc
      Real.exp (-(W.rectangle.σ * u)) * (u - 1) * Real.exp u =
          (u - 1) *
            (Real.exp (-(W.rectangle.σ * u)) * Real.exp u) := by ring
      _ = (u - 1) * Real.exp (u * (1 - W.rectangle.σ)) := by
        rw [← Real.exp_add]
        congr 1
        ring_nf

/-!
The change of variables is deliberately stated with the finite regularity
certificates required by the interval-integral API.  It does not assert a
prime-counting asymptotic or exchange any infinite limit.
-/
theorem cfzp048PrimeRemainderSmoothAbelCell_eq_logCell
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (_hL : 1 < cfzp039CarrierCellLeft W c n)
    (hDensity :
      cfzp048PrimeRemainderSmoothAbelModel W
          (cfzp040CarrierCellExpLeft W c n)
          (cfzp040CarrierCellExpRight W c n) =
        ∫ x in Set.Ioc
          (cfzp040CarrierCellExpLeft W c n)
          (cfzp040CarrierCellExpRight W c n),
          cfzp048PrimeAxisRemainderTestFunction W x *
            cfzp042PrimeCountingSmoothDensity x)
    (hg_cont : ContinuousOn
      (fun x => cfzp048PrimeAxisRemainderTestFunction W x *
        cfzp042PrimeCountingSmoothDensity x)
      (Real.exp '' Set.uIcc
        (cfzp039CarrierCellLeft W c n)
        (cfzp039CarrierCellRight W c n)))
    (hg_int : IntegrableOn
      (fun x => cfzp048PrimeAxisRemainderTestFunction W x *
        cfzp042PrimeCountingSmoothDensity x)
      (Real.exp '' Set.uIcc
        (cfzp039CarrierCellLeft W c n)
        (cfzp039CarrierCellRight W c n)))
    (hg_comp_int : IntegrableOn
      (fun u =>
        ((fun x => cfzp048PrimeAxisRemainderTestFunction W x *
          cfzp042PrimeCountingSmoothDensity x) ∘ Real.exp) u *
          Real.exp u)
      (Set.uIcc (cfzp039CarrierCellLeft W c n)
        (cfzp039CarrierCellRight W c n))) :
    cfzp048PrimeRemainderSmoothAbelModel W
        (cfzp040CarrierCellExpLeft W c n)
        (cfzp040CarrierCellExpRight W c n) =
      cfzp048PrimeRemainderSmoothLogCell W c n := by
  have hLR : cfzp039CarrierCellLeft W c n ≤
      cfzp039CarrierCellRight W c n := by
    apply Real.exp_le_exp.mp
    exact (cfzp040CarrierCellExpLeft_lt_right W c n).le
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
    simpa [min_eq_left hLR, max_eq_right hLR] using
      (mem_uIcc.mpr (Or.inl ⟨le_of_lt hu.1, le_of_lt hu.2⟩))
  have hsub := intervalIntegral.integral_comp_mul_deriv'''
    (a := cfzp039CarrierCellLeft W c n)
    (b := cfzp039CarrierCellRight W c n)
    (f := Real.exp) (f' := Real.exp)
    (g := fun x => cfzp048PrimeAxisRemainderTestFunction W x *
      cfzp042PrimeCountingSmoothDensity x)
    Real.continuous_exp.continuousOn
    (fun x hx => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    (hg_cont.mono himage) hg_int hg_comp_int
  rw [hDensity]
  have hsub' :
      (∫ x in cfzp039CarrierCellLeft W c n..cfzp039CarrierCellRight W c n,
        ((fun x => cfzp048PrimeAxisRemainderTestFunction W x *
          cfzp042PrimeCountingSmoothDensity x) ∘ Real.exp) x *
          Real.exp x) =
        ∫ x in Set.Ioc
          (cfzp040CarrierCellExpLeft W c n)
          (cfzp040CarrierCellExpRight W c n),
          cfzp048PrimeAxisRemainderTestFunction W x *
            cfzp042PrimeCountingSmoothDensity x := by
    have hExp : Real.exp (cfzp039CarrierCellLeft W c n) ≤
        Real.exp (cfzp039CarrierCellRight W c n) :=
      (cfzp040CarrierCellExpLeft_lt_right W c n).le
    simpa only [cfzp040CarrierCellExpLeft,
      cfzp040CarrierCellExpRight,
      intervalIntegral.integral_of_le hExp] using hsub
  rw [← hsub']
  unfold cfzp048PrimeRemainderSmoothLogCell
  apply intervalIntegral.integral_congr
  intro u hu
  exact cfzp048_smoothDensity_exp_integrand_eq_logCellIntegrand W u

/-! ## Gates G-H: smooth remainder debt and the quarter-margin budget -/

/-- The smooth remainder debt in one exponential period cell. -/
noncomputable def cfzp048PrimeAxisSmoothRemainderCellDebt
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) : ℝ :=
  cfzp036PrimeAxisRemainderConstant ε W *
    cfzp048PrimeRemainderSmoothLogCell W c n

/-- A distribution-free envelope for the smooth remainder debt. -/
noncomputable def cfzp048PrimeAxisSmoothRemainderEnvelope
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) : ℝ :=
  cfzp036PrimeAxisRemainderConstant ε W *
    cfzp036PrimeAxisCarrierPeriod W *
    Real.exp (cfzp039PrimeAxisGrowthExponent W *
      cfzp039CarrierCellRight W c n) /
    (cfzp039CarrierCellLeft W c n) ^ 2

private theorem cfzp048_smoothRemainder_pointwise_le
    {W : PascalCenteredXiResidueTransportWindow}
    {c : ℝ} {n : ℕ}
    (hU : 2 ≤ cfzp039CarrierCellLeft W c n)
    (hβ : 0 ≤ cfzp039PrimeAxisGrowthExponent W)
    {u : ℝ}
    (hu : u ∈ Set.uIcc (cfzp039CarrierCellLeft W c n)
      (cfzp039CarrierCellRight W c n)) :
    0 ≤ Real.exp (cfzp039PrimeAxisGrowthExponent W * u) *
        (1 / u ^ 2 - 1 / u ^ 3) ∧
      Real.exp (cfzp039PrimeAxisGrowthExponent W * u) *
          (1 / u ^ 2 - 1 / u ^ 3) ≤
        Real.exp (cfzp039PrimeAxisGrowthExponent W *
          cfzp039CarrierCellRight W c n) /
          (cfzp039CarrierCellLeft W c n) ^ 2 := by
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
  have hU0 : 0 < cfzp039CarrierCellLeft W c n :=
    lt_of_lt_of_le (by norm_num) hU
  have hu0 : 0 < u := lt_of_lt_of_le hU0 huL
  have hdiff : 0 ≤ 1 / u ^ 2 - 1 / u ^ 3 := by
    field_simp [ne_of_gt hu0]
    nlinarith [sq_nonneg (u - 1)]
  have hsq : 1 / u ^ 2 ≤
      1 / (cfzp039CarrierCellLeft W c n) ^ 2 := by
    gcongr
  have hweight : 1 / u ^ 2 - 1 / u ^ 3 ≤
      1 / (cfzp039CarrierCellLeft W c n) ^ 2 := by
    have htail : 0 ≤ 1 / u ^ 3 := by positivity
    linarith
  have hexp : Real.exp (cfzp039PrimeAxisGrowthExponent W * u) ≤
      Real.exp (cfzp039PrimeAxisGrowthExponent W *
        cfzp039CarrierCellRight W c n) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left huR hβ
  constructor
  · exact mul_nonneg (Real.exp_pos _).le hdiff
  · simpa [div_eq_mul_inv, one_div] using
      (mul_le_mul hexp hweight hdiff (Real.exp_pos _).le)

/-- The smooth remainder log-cell is nonnegative. -/
theorem cfzp048PrimeRemainderSmoothLogCell_nonneg
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hU : 2 ≤ cfzp039CarrierCellLeft W c n)
    (hβ : 0 ≤ cfzp039PrimeAxisGrowthExponent W)
    (hG_int : IntervalIntegrable
      (fun u => Real.exp (cfzp039PrimeAxisGrowthExponent W * u) *
        (1 / u ^ 2 - 1 / u ^ 3)) volume
      (cfzp039CarrierCellLeft W c n)
      (cfzp039CarrierCellRight W c n)) :
    0 ≤ cfzp048PrimeRemainderSmoothLogCell W c n := by
  unfold cfzp048PrimeRemainderSmoothLogCell
  have hLR : cfzp039CarrierCellLeft W c n ≤
      cfzp039CarrierCellRight W c n := by
    apply Real.exp_le_exp.mp
    exact (cfzp040CarrierCellExpLeft_lt_right W c n).le
  have hmono :
      ∫ u in cfzp039CarrierCellLeft W c n..cfzp039CarrierCellRight W c n,
        (0 : ℝ) ≤
      ∫ u in cfzp039CarrierCellLeft W c n..cfzp039CarrierCellRight W c n,
        Real.exp (cfzp039PrimeAxisGrowthExponent W * u) *
          (1 / u ^ 2 - 1 / u ^ 3) := by
    apply intervalIntegral.integral_mono_on hLR
      (intervalIntegrable_const :
        IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume
          (cfzp039CarrierCellLeft W c n)
          (cfzp039CarrierCellRight W c n)) hG_int
    intro u hu
    exact (cfzp048_smoothRemainder_pointwise_le hU hβ
      (mem_uIcc.mpr (Or.inl hu))).1
  simpa using hmono

/-- The smooth log-cell is bounded by its endpoint exponential envelope. -/
theorem cfzp048PrimeRemainderSmoothLogCell_le
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hU : 2 ≤ cfzp039CarrierCellLeft W c n)
    (hβ : 0 ≤ cfzp039PrimeAxisGrowthExponent W)
    (hG_int : IntervalIntegrable
      (fun u => Real.exp (cfzp039PrimeAxisGrowthExponent W * u) *
        (1 / u ^ 2 - 1 / u ^ 3)) volume
      (cfzp039CarrierCellLeft W c n)
      (cfzp039CarrierCellRight W c n)) :
    cfzp048PrimeRemainderSmoothLogCell W c n ≤
      cfzp036PrimeAxisCarrierPeriod W *
        Real.exp (cfzp039PrimeAxisGrowthExponent W *
          cfzp039CarrierCellRight W c n) /
        (cfzp039CarrierCellLeft W c n) ^ 2 := by
  have hLR : cfzp039CarrierCellLeft W c n ≤
      cfzp039CarrierCellRight W c n := by
    apply Real.exp_le_exp.mp
    exact (cfzp040CarrierCellExpLeft_lt_right W c n).le
  have hmono := intervalIntegral.integral_mono_on hLR hG_int
    (intervalIntegrable_const :
      IntervalIntegrable
        (fun _ : ℝ => Real.exp (cfzp039PrimeAxisGrowthExponent W *
          cfzp039CarrierCellRight W c n) /
          (cfzp039CarrierCellLeft W c n) ^ 2) volume
        (cfzp039CarrierCellLeft W c n)
        (cfzp039CarrierCellRight W c n))
    (fun u hu => (cfzp048_smoothRemainder_pointwise_le hU hβ
      (mem_uIcc.mpr (Or.inl hu))).2)
  unfold cfzp048PrimeRemainderSmoothLogCell
  simpa [cfzp046CarrierCellRight_eq_left_add_period,
    intervalIntegral.integral_const] using hmono

/-- The smooth part of the remainder debt is nonnegative. -/
theorem cfzp048PrimeAxisSmoothRemainderCellDebt_nonneg
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hSmooth : 0 ≤ cfzp048PrimeRemainderSmoothLogCell W c n) :
    0 ≤ cfzp048PrimeAxisSmoothRemainderCellDebt ε W c n := by
  unfold cfzp048PrimeAxisSmoothRemainderCellDebt
  exact mul_nonneg
    (cfzp036PrimeAxisRemainderConstant_pos hε W).le hSmooth

/-- The smooth remainder debt is bounded by the explicit envelope. -/
theorem cfzp048PrimeAxisSmoothRemainderCellDebt_le_envelope
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hU : 2 ≤ cfzp039CarrierCellLeft W c n)
    (hβ : 0 ≤ cfzp039PrimeAxisGrowthExponent W)
    (hG_int : IntervalIntegrable
      (fun u => Real.exp (cfzp039PrimeAxisGrowthExponent W * u) *
        (1 / u ^ 2 - 1 / u ^ 3)) volume
      (cfzp039CarrierCellLeft W c n)
      (cfzp039CarrierCellRight W c n)) :
    cfzp048PrimeAxisSmoothRemainderCellDebt ε W c n ≤
      cfzp048PrimeAxisSmoothRemainderEnvelope ε W c n := by
  unfold cfzp048PrimeAxisSmoothRemainderCellDebt
    cfzp048PrimeAxisSmoothRemainderEnvelope
  calc
    cfzp036PrimeAxisRemainderConstant ε W *
        cfzp048PrimeRemainderSmoothLogCell W c n ≤
      cfzp036PrimeAxisRemainderConstant ε W *
        (cfzp036PrimeAxisCarrierPeriod W *
          Real.exp (cfzp039PrimeAxisGrowthExponent W *
            cfzp039CarrierCellRight W c n) /
          (cfzp039CarrierCellLeft W c n) ^ 2) :=
      mul_le_mul_of_nonneg_left
        (cfzp048PrimeRemainderSmoothLogCell_le W c n hU hβ hG_int)
        (cfzp036PrimeAxisRemainderConstant_pos hε W).le
    _ = cfzp036PrimeAxisRemainderConstant ε W *
        cfzp036PrimeAxisCarrierPeriod W *
          Real.exp (cfzp039PrimeAxisGrowthExponent W *
            cfzp039CarrierCellRight W c n) /
          (cfzp039CarrierCellLeft W c n) ^ 2 := by ring

/-- The radial threshold at which the smooth remainder consumes at most one
quarter of the explicit smooth margin. -/
noncomputable def cfzp048PrimeAxisRemainderQuarterMarginThreshold
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) : ℝ :=
  max (cfzp044RadialLateThreshold ε W c)
    (16 * cfzp036PrimeAxisRemainderConstant ε W *
      cfzp036PrimeAxisCarrierPeriod W *
      Real.exp (cfzp039PrimeAxisGrowthExponent W *
        cfzp036PrimeAxisCarrierPeriod W) /
      cfzp039ExponentialCarrierPeriodTransform ε W c)

/-- The smooth remainder envelope fits inside one quarter of the explicit
margin once the quarter-margin threshold has been reached. -/
theorem cfzp048PrimeAxisSmoothRemainderEnvelope_le_quarter_explicitSmoothMargin
    {ε : ℝ} (_hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hstrip : Cfzp039PrimeAxisInteriorStrip W)
    (hM : 0 < cfzp039ExponentialCarrierPeriodTransform ε W c)
    (hThreshold : cfzp048PrimeAxisRemainderQuarterMarginThreshold ε W c ≤
      cfzp039CarrierCellLeft W c n)
    (_hG_int : IntervalIntegrable
      (fun u => Real.exp (cfzp039PrimeAxisGrowthExponent W * u) *
        (1 / u ^ 2 - 1 / u ^ 3)) volume
      (cfzp039CarrierCellLeft W c n)
      (cfzp039CarrierCellRight W c n)) :
    cfzp048PrimeAxisSmoothRemainderEnvelope ε W c n ≤
      cfzp044ExplicitSmoothMargin ε W c n / 4 := by
  have hLate : cfzp044RadialLateThreshold ε W c ≤
      cfzp039CarrierCellLeft W c n :=
    le_trans (le_max_left _ _) hThreshold
  have hU : 2 ≤ cfzp039CarrierCellLeft W c n :=
    cfzp044_two_le_of_radialLate hLate
  have hβ : 0 ≤ cfzp039PrimeAxisGrowthExponent W :=
    (cfzp039PrimeAxisGrowthExponent_pos W hstrip).le
  have hL : 0 < cfzp039CarrierCellLeft W c n :=
    lt_of_lt_of_le (by norm_num) hU
  have hterm := le_trans (le_max_right _ _) hThreshold
  have hterm' :
      16 * cfzp036PrimeAxisRemainderConstant ε W *
          cfzp036PrimeAxisCarrierPeriod W *
          Real.exp (cfzp039PrimeAxisGrowthExponent W *
            cfzp036PrimeAxisCarrierPeriod W) ≤
        cfzp039ExponentialCarrierPeriodTransform ε W c *
          cfzp039CarrierCellLeft W c n := by
    have h := (div_le_iff₀ hM).mp hterm
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  have hcore :
      (cfzp036PrimeAxisRemainderConstant ε W *
        cfzp036PrimeAxisCarrierPeriod W *
        Real.exp (cfzp039PrimeAxisGrowthExponent W *
          cfzp036PrimeAxisCarrierPeriod W)) /
          (cfzp039CarrierCellLeft W c n) ^ 2 ≤
        cfzp039ExponentialCarrierPeriodTransform ε W c /
          (16 * cfzp039CarrierCellLeft W c n) := by
    have h16 :
        cfzp036PrimeAxisRemainderConstant ε W *
            cfzp036PrimeAxisCarrierPeriod W *
            Real.exp (cfzp039PrimeAxisGrowthExponent W *
              cfzp036PrimeAxisCarrierPeriod W) ≤
          (cfzp039ExponentialCarrierPeriodTransform ε W c *
            cfzp039CarrierCellLeft W c n) / 16 := by
      nlinarith [hterm']
    calc
      (cfzp036PrimeAxisRemainderConstant ε W *
          cfzp036PrimeAxisCarrierPeriod W *
          Real.exp (cfzp039PrimeAxisGrowthExponent W *
            cfzp036PrimeAxisCarrierPeriod W)) /
            (cfzp039CarrierCellLeft W c n) ^ 2 ≤
          ((cfzp039ExponentialCarrierPeriodTransform ε W c *
            cfzp039CarrierCellLeft W c n) / 16) /
              (cfzp039CarrierCellLeft W c n) ^ 2 := by
        exact div_le_div_of_nonneg_right h16 (by positivity)
      _ = cfzp039ExponentialCarrierPeriodTransform ε W c /
          (16 * cfzp039CarrierCellLeft W c n) := by
        field_simp [ne_of_gt hL]
  unfold cfzp048PrimeAxisSmoothRemainderEnvelope
    cfzp044ExplicitSmoothMargin
  calc
    cfzp036PrimeAxisRemainderConstant ε W *
        cfzp036PrimeAxisCarrierPeriod W *
        Real.exp (cfzp039PrimeAxisGrowthExponent W *
          cfzp039CarrierCellRight W c n) /
          (cfzp039CarrierCellLeft W c n) ^ 2 =
      Real.exp (cfzp039PrimeAxisGrowthExponent W *
          cfzp039CarrierCellLeft W c n) *
        ((cfzp036PrimeAxisRemainderConstant ε W *
          cfzp036PrimeAxisCarrierPeriod W *
          Real.exp (cfzp039PrimeAxisGrowthExponent W *
            cfzp036PrimeAxisCarrierPeriod W)) /
          (cfzp039CarrierCellLeft W c n) ^ 2) := by
      rw [cfzp046CarrierCellRight_eq_left_add_period]
      rw [show cfzp039PrimeAxisGrowthExponent W *
          (cfzp039CarrierCellLeft W c n +
            cfzp036PrimeAxisCarrierPeriod W) =
          cfzp039PrimeAxisGrowthExponent W *
            cfzp039CarrierCellLeft W c n +
          cfzp039PrimeAxisGrowthExponent W *
            cfzp036PrimeAxisCarrierPeriod W by ring]
      rw [Real.exp_add]
      ring
    _ ≤ Real.exp (cfzp039PrimeAxisGrowthExponent W *
          cfzp039CarrierCellLeft W c n) *
        (cfzp039ExponentialCarrierPeriodTransform ε W c /
          (16 * cfzp039CarrierCellLeft W c n)) := by
      exact mul_le_mul_of_nonneg_left hcore (Real.exp_pos _).le
    _ = (Real.exp (cfzp039PrimeAxisGrowthExponent W *
          cfzp039CarrierCellLeft W c n) *
        (cfzp039ExponentialCarrierPeriodTransform ε W c /
          (4 * cfzp039CarrierCellLeft W c n))) / 4 := by
      ring

/-! ## Gates I-J: discrepancy debt and the remaining budget -/

/-- The prime-axis remainder discrepancy attached to one exponential cell. -/
noncomputable def cfzp048PrimeRemainderCellDiscrepancyFunctional
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) : ℝ :=
  cfzp048PrimeRemainderDiscrepancyFunctional W
    (cfzp040CarrierCellExpLeft W c n)
    (cfzp040CarrierCellExpRight W c n)

/-- The absolute discrepancy debt in one prime-axis remainder cell. -/
noncomputable def cfzp048PrimeAxisRemainderDiscrepancyCellDebt
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) : ℝ :=
  cfzp036PrimeAxisRemainderConstant ε W *
    |cfzp048PrimeRemainderCellDiscrepancyFunctional W c n|

/-- The discrepancy debt is nonnegative by construction. -/
theorem cfzp048PrimeAxisRemainderDiscrepancyCellDebt_nonneg
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) :
    0 ≤ cfzp048PrimeAxisRemainderDiscrepancyCellDebt ε W c n := by
  unfold cfzp048PrimeAxisRemainderDiscrepancyCellDebt
  exact mul_nonneg
    (cfzp036PrimeAxisRemainderConstant_pos hε W).le (abs_nonneg _)

/-- Exact smooth-plus-discrepancy control for the finite remainder debt. -/
theorem cfzp048PrimeAxisRemainderCellDebt_le_smooth_add_discrepancyDebt
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (_hLate : cfzp044RadialLateThreshold ε W c ≤
      cfzp039CarrierCellLeft W c n)
    (hSplit :
      cfzp048PrimeRemainderSumIoc W
          (cfzp040CarrierCellExpLeft W c n)
          (cfzp040CarrierCellExpRight W c n) =
        cfzp048PrimeRemainderSmoothAbelModel W
          (cfzp040CarrierCellExpLeft W c n)
          (cfzp040CarrierCellExpRight W c n) +
        cfzp048PrimeRemainderCellDiscrepancyFunctional W c n)
    (hDebtEq :
      cfzp039PrimeAxisRemainderCellDebt ε W c n
          (cfzp040CarrierCellNaturalLeft W c n)
          (cfzp040CarrierCellNaturalRight W c n) =
        cfzp036PrimeAxisRemainderConstant ε W *
          cfzp048PrimeRemainderSumIoc W
            (cfzp040CarrierCellExpLeft W c n)
            (cfzp040CarrierCellExpRight W c n))
    (hSmoothEq :
      cfzp048PrimeRemainderSmoothAbelModel W
          (cfzp040CarrierCellExpLeft W c n)
          (cfzp040CarrierCellExpRight W c n) =
        cfzp048PrimeRemainderSmoothLogCell W c n) :
    cfzp039PrimeAxisRemainderCellDebt ε W c n
        (cfzp040CarrierCellNaturalLeft W c n)
        (cfzp040CarrierCellNaturalRight W c n) ≤
      cfzp048PrimeAxisSmoothRemainderCellDebt ε W c n +
        cfzp048PrimeAxisRemainderDiscrepancyCellDebt ε W c n := by
  have hK : 0 ≤ cfzp036PrimeAxisRemainderConstant ε W :=
    (cfzp036PrimeAxisRemainderConstant_pos hε W).le
  rw [hDebtEq]
  unfold cfzp048PrimeAxisSmoothRemainderCellDebt
    cfzp048PrimeAxisRemainderDiscrepancyCellDebt
  rw [hSplit]
  rw [hSmoothEq]
  calc
    cfzp036PrimeAxisRemainderConstant ε W *
        (cfzp048PrimeRemainderSmoothLogCell W c n +
          cfzp048PrimeRemainderCellDiscrepancyFunctional W c n) =
      cfzp036PrimeAxisRemainderConstant ε W *
          cfzp048PrimeRemainderSmoothLogCell W c n +
        cfzp036PrimeAxisRemainderConstant ε W *
          cfzp048PrimeRemainderCellDiscrepancyFunctional W c n := by ring
    _ ≤ cfzp036PrimeAxisRemainderConstant ε W *
          cfzp048PrimeRemainderSmoothLogCell W c n +
        cfzp036PrimeAxisRemainderConstant ε W *
          |cfzp048PrimeRemainderCellDiscrepancyFunctional W c n| := by
      have hdisc := mul_le_mul_of_nonneg_left
        (le_abs_self (cfzp048PrimeRemainderCellDiscrepancyFunctional W c n)) hK
      exact add_le_add_right
        hdisc
        (cfzp036PrimeAxisRemainderConstant ε W *
          cfzp048PrimeRemainderSmoothLogCell W c n)

/-- The same debt estimate after spending one quarter of the smooth margin. -/
theorem cfzp048PrimeAxisRemainderCellDebt_le_quarterMargin_add_discrepancyDebt
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hstrip : Cfzp039PrimeAxisInteriorStrip W)
    (hM : 0 < cfzp039ExponentialCarrierPeriodTransform ε W c)
    (hThreshold : cfzp048PrimeAxisRemainderQuarterMarginThreshold ε W c ≤
      cfzp039CarrierCellLeft W c n)
    (hG_int : IntervalIntegrable
      (fun u => Real.exp (cfzp039PrimeAxisGrowthExponent W * u) *
        (1 / u ^ 2 - 1 / u ^ 3)) volume
      (cfzp039CarrierCellLeft W c n)
      (cfzp039CarrierCellRight W c n))
    (hSplit :
      cfzp048PrimeRemainderSumIoc W
          (cfzp040CarrierCellExpLeft W c n)
          (cfzp040CarrierCellExpRight W c n) =
        cfzp048PrimeRemainderSmoothAbelModel W
          (cfzp040CarrierCellExpLeft W c n)
          (cfzp040CarrierCellExpRight W c n) +
        cfzp048PrimeRemainderCellDiscrepancyFunctional W c n)
    (hDebtEq :
      cfzp039PrimeAxisRemainderCellDebt ε W c n
          (cfzp040CarrierCellNaturalLeft W c n)
          (cfzp040CarrierCellNaturalRight W c n) =
        cfzp036PrimeAxisRemainderConstant ε W *
          cfzp048PrimeRemainderSumIoc W
            (cfzp040CarrierCellExpLeft W c n)
            (cfzp040CarrierCellExpRight W c n))
    (hSmoothEq :
      cfzp048PrimeRemainderSmoothAbelModel W
          (cfzp040CarrierCellExpLeft W c n)
          (cfzp040CarrierCellExpRight W c n) =
        cfzp048PrimeRemainderSmoothLogCell W c n) :
    cfzp039PrimeAxisRemainderCellDebt ε W c n
        (cfzp040CarrierCellNaturalLeft W c n)
        (cfzp040CarrierCellNaturalRight W c n) ≤
      cfzp044ExplicitSmoothMargin ε W c n / 4 +
        cfzp048PrimeAxisRemainderDiscrepancyCellDebt ε W c n := by
  have hLate : cfzp044RadialLateThreshold ε W c ≤
      cfzp039CarrierCellLeft W c n :=
    le_trans (le_max_left _ _) hThreshold
  have hU := cfzp044_two_le_of_radialLate hLate
  have hβ := (cfzp039PrimeAxisGrowthExponent_pos W hstrip).le
  have hbase := cfzp048PrimeAxisRemainderCellDebt_le_smooth_add_discrepancyDebt
    hε W c n hLate hSplit hDebtEq hSmoothEq
  have hsmooth := cfzp048PrimeAxisSmoothRemainderCellDebt_le_envelope
    hε W c n hU hβ hG_int
  have hquarter :=
    cfzp048PrimeAxisSmoothRemainderEnvelope_le_quarter_explicitSmoothMargin
      hε W c n hstrip hM hThreshold hG_int
  have hcombined :
      cfzp048PrimeAxisSmoothRemainderCellDebt ε W c n ≤
        cfzp044ExplicitSmoothMargin ε W c n / 4 :=
    le_trans hsmooth hquarter
  linarith

/-- The remaining three-quarter margin budget after the smooth quarter is
spent.  This is an interface, not an assertion that the budget is available. -/
  def Cfzp048RemainingQuarterMarginBudgetAt
    (ε η D : ℝ)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) : Prop :=
  pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W
      (cfzp040CarrierCellNaturalLeft W c n) +
    cfzp048PrimeAxisRemainderDiscrepancyCellDebt ε W c n +
    cfzp034HigherPowerReferenceMass ε W
      (cfzp040CarrierCellNaturalLeft W c n)
      (cfzp040CarrierCellNaturalRight W c n) + D ≤
    (3 / 4 : ℝ) * cfzp044ExplicitSmoothMargin ε W c n + η

/-- A supplied remaining-quarter budget feeds the existing finite radial
reservoir theorem.  All discrepancy and smooth-cell certificates remain
explicit inputs. -/
theorem Cfzp048RemainingQuarterMarginBudget_implies_radialContactDeficit_le
    {ε η D : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hstrip : Cfzp039PrimeAxisInteriorStrip W)
    (hM : 0 < cfzp039ExponentialCarrierPeriodTransform ε W c)
    (hThreshold : cfzp048PrimeAxisRemainderQuarterMarginThreshold ε W c ≤
      cfzp039CarrierCellLeft W c n)
    (hG_int : IntervalIntegrable
      (fun u => Real.exp (cfzp039PrimeAxisGrowthExponent W * u) *
        (1 / u ^ 2 - 1 / u ^ 3)) volume
      (cfzp039CarrierCellLeft W c n)
      (cfzp039CarrierCellRight W c n))
    (hSplit :
      cfzp048PrimeRemainderSumIoc W
          (cfzp040CarrierCellExpLeft W c n)
          (cfzp040CarrierCellExpRight W c n) =
        cfzp048PrimeRemainderSmoothAbelModel W
          (cfzp040CarrierCellExpLeft W c n)
          (cfzp040CarrierCellExpRight W c n) +
        cfzp048PrimeRemainderCellDiscrepancyFunctional W c n)
    (hDebtEq :
      cfzp039PrimeAxisRemainderCellDebt ε W c n
          (cfzp040CarrierCellNaturalLeft W c n)
          (cfzp040CarrierCellNaturalRight W c n) =
        cfzp036PrimeAxisRemainderConstant ε W *
          cfzp048PrimeRemainderSumIoc W
            (cfzp040CarrierCellExpLeft W c n)
            (cfzp040CarrierCellExpRight W c n))
    (hSmoothEq :
      cfzp048PrimeRemainderSmoothAbelModel W
          (cfzp040CarrierCellExpLeft W c n)
          (cfzp040CarrierCellExpRight W c n) =
        cfzp048PrimeRemainderSmoothLogCell W c n)
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
    (hbudget : Cfzp048RemainingQuarterMarginBudgetAt ε η D W c n) :
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W
      (cfzp040CarrierCellNaturalRight W c n) ≤ η := by
  have hLate : cfzp044RadialLateThreshold ε W c ≤
      cfzp039CarrierCellLeft W c n :=
    le_trans (le_max_left _ _) hThreshold
  have hrem := cfzp048PrimeAxisRemainderCellDebt_le_quarterMargin_add_discrepancyDebt
    hε W c n hstrip hM hThreshold hG_int hSplit hDebtEq hSmoothEq
  have hcell := cfzp044_eligibilityThreshold_le_of_radialLate hLate
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
    unfold Cfzp048RemainingQuarterMarginBudgetAt at hbudget
    rw [hexception]
    have hmargin := cfzp044_explicitSmoothMargin_le_smoothCell
      hε W c n hM hLate hSmoothLog
    linarith
  exact cfzp041SmoothDiscrepancyCellReservoir_implies_radialContactDeficit_le
    hε hε2 W c n hcell hf_diff hf_int hM_int hD_int hD hreservoir

/-- Explicit boundaries left open by the finite Abel reduction. -/
inductive Cfzp048PrimeAxisRemainderAbelSmoothDiscrepancyGap : Prop
  | noAutomaticInteriorStripWindowProvider
  | noAutomaticLeadingSmoothAbelLogCellReadinessProvider
  | noPrimeCountingCarrierDiscrepancyFunctionalDecayProvider
  | noPrimeAxisRemainderDiscrepancyFunctionalDecayProvider
  | noPointwiseDiscrepancyToCombinedFunctionalBound
  | noCofinalRemainingQuarterMarginBudgetProvider



/-! ## Gate C: exact prime-axis remainder-cell bridge -/

/-- The raw prime sum at exponential cell endpoints. -/
noncomputable def cfzp048PrimeRemainderRawCellSum
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) : ℝ :=
  ∑ p ∈ cfzp040RawPrimeCarrierCellSupport W c n,
    cfzp048PrimeAxisRemainderTestFunction W (p : ℝ)

private theorem cfzp048_raw_prime_mem_eligible_pair
    {ε : ℝ} (_hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n p : ℕ)
    (hcell : max (3 * ε) 1 ≤ cfzp039CarrierCellLeft W c n)
    (hp : p ∈ cfzp040RawPrimeCarrierCellSupport W c n) :
    (p, 0) ∈ cfzp034EligiblePrimeAxisPairBlockSupport ε
      (cfzp040CarrierCellNaturalLeft W c n)
      (cfzp040CarrierCellNaturalRight W c n) := by
  classical
  have hprime := (Finset.mem_filter.mp hp).2
  have hraw := (cfzp040RawPrimeCarrierCellSupport_mem_iff hprime).mp hp
  have hcell' : 3 * ε ≤ cfzp039CarrierCellLeft W c n ∧
      1 ≤ cfzp039CarrierCellLeft W c n := max_le_iff.mp hcell
  have hEligible : Cfzp034PrimeAxisMassEligible ε p :=
    ⟨le_trans hcell'.1 hraw.2.1.le, le_trans hcell'.2 hraw.2.1.le⟩
  have hpL : cfzp040CarrierCellNaturalLeft W c n < p := by
    have hp_pos_real : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hprime.pos
    apply (Nat.floor_lt' hprime.ne_zero).mpr
    simpa [cfzp040CarrierCellExpLeft, Real.exp_log hp_pos_real] using
      (Real.exp_lt_exp.mpr hraw.2.1)
  have hpR : p ≤ cfzp040CarrierCellNaturalRight W c n := by
    have hp_pos_real : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hprime.pos
    apply (Nat.le_floor_iff' hprime.ne_zero).mpr
    simpa [cfzp040CarrierCellExpRight, Real.exp_log hp_pos_real] using
      (Real.exp_le_exp.mpr hraw.2.2)
  have hright : (p, 0) ∈ pascalPrimePowerPairSupportUpTo
      (cfzp040CarrierCellNaturalRight W c n) := by
    rw [mem_pascalPrimePowerPairSupportUpTo_iff]
    refine ⟨mem_pascalPrimeCoordinateSupportUpTo_iff.mpr ⟨hprime, hpR⟩, ?_, ?_⟩
    · omega
    · simpa using hpR
  have hleft : (p, 0) ∉ pascalPrimePowerPairSupportUpTo
      (cfzp040CarrierCellNaturalLeft W c n) := by
    intro h
    have hmem := mem_pascalPrimePowerPairSupportUpTo_iff.mp h
    have hp_le_left : p ≤ cfzp040CarrierCellNaturalLeft W c n :=
      (mem_pascalPrimeCoordinateSupportUpTo_iff.mp hmem.1).2
    exact (Nat.not_lt_of_ge hp_le_left) hpL
  have hblock : (p, 0) ∈ cfzp024PrimePowerPairBlockSupport
      (cfzp040CarrierCellNaturalLeft W c n)
      (cfzp040CarrierCellNaturalRight W c n) :=
    Finset.mem_sdiff.mpr ⟨hright, hleft⟩
  have haxis : (p, 0) ∈ cfzp034PrimeAxisPairBlockSupport
      (cfzp040CarrierCellNaturalLeft W c n)
      (cfzp040CarrierCellNaturalRight W c n) :=
    Finset.mem_filter.mpr ⟨hblock, rfl⟩
  exact Finset.mem_filter.mpr ⟨haxis, hEligible⟩

private theorem cfzp048_eligible_pair_mem_raw_prime
    {ε : ℝ} (_hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    {pk : ℕ × ℕ}
    (_hcell : max (3 * ε) 1 ≤ cfzp039CarrierCellLeft W c n)
    (hpk : pk ∈ cfzp039PrimeAxisCarrierCellPairSupport ε W c n
      (cfzp040CarrierCellNaturalLeft W c n)
      (cfzp040CarrierCellNaturalRight W c n)) :
    pk.1 ∈ cfzp040RawPrimeCarrierCellSupport W c n ∧ pk.2 = 0 := by
  classical
  have houter := Finset.mem_filter.mp hpk
  have hcellmem := houter.2
  have hpair := houter.1
  have hpair' : pk ∈ cfzp034PrimeAxisPairBlockSupport
      (cfzp040CarrierCellNaturalLeft W c n)
      (cfzp040CarrierCellNaturalRight W c n) ∧
      Cfzp034PrimeAxisMassEligible ε pk.1 := by
    simpa only [cfzp034EligiblePrimeAxisPairBlockSupport,
      Finset.mem_filter] using hpair
  have hzero : pk.2 = 0 := (Finset.mem_filter.mp hpair'.1).2
  have hright := (Finset.mem_sdiff.mp
    (Finset.mem_filter.mp hpair'.1).1).1
  have hcoord := mem_pascalPrimeCoordinateSupportUpTo_iff.mp
    (mem_pascalPrimePowerPairSupportUpTo_iff.mp hright).1
  have hraw : pk.1 ∈ cfzp040RawPrimeCarrierCellSupport W c n := by
    apply (cfzp040RawPrimeCarrierCellSupport_mem_iff hcoord.1).mpr
    exact ⟨hcoord.1, hcellmem.1, hcellmem.2⟩
  exact ⟨hraw, hzero⟩

private theorem cfzp048_raw_prime_image_eq_carrier_support
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hcell : max (3 * ε) 1 ≤ cfzp039CarrierCellLeft W c n) :
    (cfzp040RawPrimeCarrierCellSupport W c n).image (fun p => (p, 0)) =
      cfzp039PrimeAxisCarrierCellPairSupport ε W c n
        (cfzp040CarrierCellNaturalLeft W c n)
        (cfzp040CarrierCellNaturalRight W c n) := by
  classical
  ext pk
  constructor
  · intro hpk
    rcases Finset.mem_image.mp hpk with ⟨p, hp, rfl⟩
    have hpair := cfzp048_raw_prime_mem_eligible_pair hε W c n p hcell hp
    have hraw := (cfzp040RawPrimeCarrierCellSupport_mem_iff
      ((Finset.mem_filter.mp hp).2)).mp hp
    exact Finset.mem_filter.mpr ⟨hpair,
      ⟨hraw.2.1, hraw.2.2⟩⟩
  · intro hpk
    obtain ⟨hraw, hzero⟩ := cfzp048_eligible_pair_mem_raw_prime hε W c n hcell hpk
    exact Finset.mem_image.mpr ⟨pk.1, hraw, Prod.ext rfl hzero.symm⟩

private theorem cfzp048PrimeRemainderSumIoc_eq_rawCellSum
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) :
    cfzp048PrimeRemainderSumIoc W
        (cfzp040CarrierCellExpLeft W c n)
        (cfzp040CarrierCellExpRight W c n) =
      cfzp048PrimeRemainderRawCellSum W c n := by
  classical
  unfold cfzp048PrimeRemainderSumIoc cfzp048PrimeRemainderRawCellSum
    cfzp040RawPrimeCarrierCellSupport
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hprime : Nat.Prime p
  · simp only [hprime, if_true,
      cfzp040PrimeIndicator_eq_one_of_prime, mul_one]
  · simp [hprime, cfzp040PrimeIndicator_eq_zero_of_not_prime]

/-- The 039 remainder debt is exactly `K` times the raw prime remainder sum. -/
theorem cfzp048PrimeAxisRemainderCellDebt_eq_constant_mul_primeRemainderSum
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hLate : cfzp044RadialLateThreshold ε W c ≤
      cfzp039CarrierCellLeft W c n) :
    cfzp039PrimeAxisRemainderCellDebt ε W c n
        (cfzp040CarrierCellNaturalLeft W c n)
        (cfzp040CarrierCellNaturalRight W c n) =
      cfzp036PrimeAxisRemainderConstant ε W *
        cfzp048PrimeRemainderSumIoc W
          (cfzp040CarrierCellExpLeft W c n)
          (cfzp040CarrierCellExpRight W c n) := by
  classical
  let A := cfzp040CarrierCellNaturalLeft W c n
  let B := cfzp040CarrierCellNaturalRight W c n
  have hcell := cfzp044_eligibilityThreshold_le_of_radialLate hLate
  have himage := cfzp048_raw_prime_image_eq_carrier_support hε W c n hcell
  have hinj : Set.InjOn (fun p : ℕ => (p, 0))
      (cfzp040RawPrimeCarrierCellSupport W c n : Set ℕ) := by
    intro p hp q hq heq
    exact congrArg Prod.fst heq
  rw [cfzp048PrimeRemainderSumIoc_eq_rawCellSum]
  unfold cfzp039PrimeAxisRemainderCellDebt
    cfzp039PrimeAxisRemainderDebtOn
  rw [← himage, Finset.sum_image hinj]
  unfold cfzp048PrimeRemainderRawCellSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hprime := (Finset.mem_filter.mp hp).2
  rw [cfzp048PrimeAxisRemainderTestFunction_natPrime W hprime]
  ring

end DkMath.RH.CFBRCProjection
