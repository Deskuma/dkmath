/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.RH.CFBRC.CosmicFormulaZetaPrimeAxisExactCarrierRemainderSignedMomentAudit
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CosmicFormulaZetaPrimeAxisFiniteAbelPrimeCountingDiscrepancyAudit"

/-!
# CFZP-040: finite Abel and prime-counting discrepancy

This module connects the finite prime-axis carrier sum to Mathlib's finite
Abel summation theorem.  The prime-counting error is kept as a named finite
functional; no prime-distribution asymptotic or infinite sum is introduced.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.NumberTheory
open MeasureTheory
open Set

/-! ## Gate A: the x-axis carrier test function -/

/-- The leading prime-axis carrier viewed as a function of the real x-axis. -/
noncomputable def cfzp040PrimeAxisCarrierTestFunction
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (x : ℝ) : ℝ :=
  Real.exp (-(W.rectangle.σ) * Real.log x) *
    cfzp036PrimeAxisLeadingPeriodicCarrier ε W (Real.log x)

theorem cfzp040PrimeAxisCarrierTestFunction_natPrime
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) {p : ℕ}
    (_hp : Nat.Prime p) :
    cfzp040PrimeAxisCarrierTestFunction ε W (p : ℝ) =
      cfzp034PrimeAxisSigmaWeight W p *
        cfzp036PrimeAxisLeadingPeriodicCarrier ε W (Real.log (p : ℝ)) := by
  rfl

/-- Derivative of the coordinate-level leading carrier. -/
noncomputable def cfzp040LeadingCarrierDerivative
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (u : ℝ) : ℝ :=
  (W.rectangle.T / ε) *
    (cfzp036LeadingSinCoeffNumerator ε W * Real.cos (W.rectangle.T * u) -
      cfzp036LeadingCosCoeffNumerator ε W * Real.sin (W.rectangle.T * u))

theorem cfzp040LeadingCarrier_hasDerivAt
    {ε u : ℝ} (hε : ε ≠ 0)
    (W : PascalCenteredXiResidueTransportWindow) :
    HasDerivAt (fun v : ℝ => cfzp036PrimeAxisLeadingPeriodicCarrier ε W v)
      (cfzp040LeadingCarrierDerivative ε W u) u := by
  have hsin : HasDerivAt (fun v : ℝ => Real.sin (W.rectangle.T * v))
      (W.rectangle.T * Real.cos (W.rectangle.T * u)) u := by
    simpa [Function.comp_def, id_eq, mul_comm, mul_left_comm, mul_assoc] using
      (Real.hasDerivAt_sin (W.rectangle.T * u)).comp u
        ((hasDerivAt_id u).const_mul W.rectangle.T)
  have hcos : HasDerivAt (fun v : ℝ => Real.cos (W.rectangle.T * v))
      (-W.rectangle.T * Real.sin (W.rectangle.T * u)) u := by
    simpa [Function.comp_def, id_eq, mul_comm, mul_left_comm, mul_assoc] using
      (Real.hasDerivAt_cos (W.rectangle.T * u)).comp u
        ((hasDerivAt_id u).const_mul W.rectangle.T)
  have hsum : HasDerivAt
      ((fun v : ℝ =>
        cfzp036LeadingSinCoeffNumerator ε W * Real.sin (W.rectangle.T * v)) +
        (fun v : ℝ =>
          cfzp036LeadingCosCoeffNumerator ε W * Real.cos (W.rectangle.T * v)))
      (cfzp036LeadingSinCoeffNumerator ε W *
          (W.rectangle.T * Real.cos (W.rectangle.T * u)) +
        cfzp036LeadingCosCoeffNumerator ε W *
          (-W.rectangle.T * Real.sin (W.rectangle.T * u))) u := by
    simpa only [Pi.add_apply, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
      (hsin.const_mul (cfzp036LeadingSinCoeffNumerator ε W)).add
        (hcos.const_mul (cfzp036LeadingCosCoeffNumerator ε W))
  have hdiv := hsum.div_const ε
  have hdiv' :
      HasDerivAt (fun v : ℝ => cfzp036PrimeAxisLeadingPeriodicCarrier ε W v)
        ((cfzp036LeadingSinCoeffNumerator ε W *
            (W.rectangle.T * Real.cos (W.rectangle.T * u)) +
          cfzp036LeadingCosCoeffNumerator ε W *
            (-W.rectangle.T * Real.sin (W.rectangle.T * u))) / ε) u :=
    hdiv.congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun v =>
        cfzp036PrimeAxisLeadingPeriodicCarrier_eq_sin_cos_pair
          (ε := ε) (u := v) hε W))
  apply hdiv'.congr_deriv
  unfold cfzp040LeadingCarrierDerivative
  field_simp [hε]
  ring

theorem cfzp040PrimeAxisCarrierTestFunction_hasDerivAt
    {ε x : ℝ} (hε : ε ≠ 0) (hx : 0 < x)
    (W : PascalCenteredXiResidueTransportWindow) :
    HasDerivAt (cfzp040PrimeAxisCarrierTestFunction ε W)
      (Real.exp (-(W.rectangle.σ) * Real.log x) / x *
        (-W.rectangle.σ *
            cfzp036PrimeAxisLeadingPeriodicCarrier ε W (Real.log x) +
          cfzp040LeadingCarrierDerivative ε W (Real.log x))) x := by
  have hlog : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx.ne'
  have hinner : HasDerivAt (fun y : ℝ => -(W.rectangle.σ) * Real.log y)
      (-(W.rectangle.σ) * x⁻¹) x := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      hlog.const_mul (-(W.rectangle.σ))
  have hexp := (Real.hasDerivAt_exp
    (-(W.rectangle.σ) * Real.log x)).comp x hinner
  have hcarrier := cfzp040LeadingCarrier_hasDerivAt
    (ε := ε) (u := Real.log x) hε W
  have hcarrier' := hcarrier.comp x hlog
  have hprod := hexp.mul hcarrier'
  have hprod' : HasDerivAt (cfzp040PrimeAxisCarrierTestFunction ε W)
      (Real.exp (-(W.rectangle.σ) * Real.log x) *
          (-(W.rectangle.σ) * x⁻¹) *
            cfzp036PrimeAxisLeadingPeriodicCarrier ε W (Real.log x) +
        Real.exp (-(W.rectangle.σ) * Real.log x) *
          (cfzp040LeadingCarrierDerivative ε W (Real.log x) * x⁻¹)) x :=
    hprod.congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun y => by
        simp [cfzp040PrimeAxisCarrierTestFunction, Function.comp_def]))
  apply hprod'.congr_deriv
  ring_nf

/-! ## Gate B: prime indicator and its cumulative count -/

/-- The real-valued indicator of the natural prime predicate. -/
def cfzp040PrimeIndicator (n : ℕ) : ℝ :=
  if Nat.Prime n then 1 else 0

@[simp] theorem cfzp040PrimeIndicator_eq_zero_of_not_prime
    {n : ℕ} (hn : ¬ Nat.Prime n) : cfzp040PrimeIndicator n = 0 := by
  simp [cfzp040PrimeIndicator, hn]

@[simp] theorem cfzp040PrimeIndicator_eq_one_of_prime
    {n : ℕ} (hn : Nat.Prime n) : cfzp040PrimeIndicator n = 1 := by
  simp [cfzp040PrimeIndicator, hn]

theorem cfzp040_sum_primeIndicator_eq_primeCounting (n : ℕ) :
    (∑ k ∈ Finset.Icc 0 n, cfzp040PrimeIndicator k) =
      (Nat.primeCounting n : ℝ) := by
  classical
  change (∑ k ∈ Finset.Icc 0 n,
    if Nat.Prime k then (1 : ℝ) else 0) = _
  rw [Finset.sum_boole]
  rw [← Nat.primesLE_eq_filter_Icc_zero]
  exact_mod_cast Nat.primesLE_card_eq_primeCounting n

/-! ## Gate C: finite real-endpoint Abel bridge -/

/-- The finite prime carrier sum on a real `Ioc` interval. -/
noncomputable def cfzp040PrimeCarrierSumIoc
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (a b : ℝ) : ℝ :=
  ∑ k ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊,
    cfzp040PrimeAxisCarrierTestFunction ε W (k : ℝ) *
      cfzp040PrimeIndicator k

theorem cfzp040PrimeCarrierSumIoc_eq_abel
    {ε a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (W : PascalCenteredXiResidueTransportWindow)
    (hf_diff : ∀ t ∈ Set.Icc a b,
      DifferentiableAt ℝ (cfzp040PrimeAxisCarrierTestFunction ε W) t)
    (hf_int : IntegrableOn
      (deriv (cfzp040PrimeAxisCarrierTestFunction ε W)) (Set.Icc a b)) :
    cfzp040PrimeCarrierSumIoc ε W a b =
      cfzp040PrimeAxisCarrierTestFunction ε W b *
          (Nat.primeCounting ⌊b⌋₊ : ℝ) -
        cfzp040PrimeAxisCarrierTestFunction ε W a *
          (Nat.primeCounting ⌊a⌋₊ : ℝ) -
        ∫ t in Set.Ioc a b,
          deriv (cfzp040PrimeAxisCarrierTestFunction ε W) t *
            (Nat.primeCounting ⌊t⌋₊ : ℝ) := by
  classical
  unfold cfzp040PrimeCarrierSumIoc
  have habel := sum_mul_eq_sub_sub_integral_mul
    (fun n : ℕ => cfzp040PrimeIndicator n)
    (f := cfzp040PrimeAxisCarrierTestFunction ε W)
    ha hab hf_diff hf_int
  rw [habel]
  simp_rw [cfzp040_sum_primeIndicator_eq_primeCounting]

/-! ## Gate D: exponential endpoints and raw prime support -/

/-- The x-axis left endpoint of a translated carrier cell. -/
noncomputable def cfzp040CarrierCellExpLeft
    (W : PascalCenteredXiResidueTransportWindow) (c : ℝ) (n : ℕ) : ℝ :=
  Real.exp (cfzp039CarrierCellLeft W c n)

/-- The x-axis right endpoint of a translated carrier cell. -/
noncomputable def cfzp040CarrierCellExpRight
    (W : PascalCenteredXiResidueTransportWindow) (c : ℝ) (n : ℕ) : ℝ :=
  Real.exp (cfzp039CarrierCellRight W c n)

theorem cfzp040CarrierCellExpLeft_pos
    (W : PascalCenteredXiResidueTransportWindow) (c : ℝ) (n : ℕ) :
    0 < cfzp040CarrierCellExpLeft W c n := by
  exact Real.exp_pos _

theorem cfzp040CarrierCellExpLeft_lt_right
    (W : PascalCenteredXiResidueTransportWindow) (c : ℝ) (n : ℕ) :
    cfzp040CarrierCellExpLeft W c n < cfzp040CarrierCellExpRight W c n := by
  apply Real.exp_lt_exp.mpr
  unfold cfzp039CarrierCellLeft cfzp039CarrierCellRight
  have hP := cfzp036PrimeAxisCarrierPeriod_pos W
  norm_num [Nat.cast_add]
  nlinarith

theorem cfzp040_log_carrierCellExpLeft
    (W : PascalCenteredXiResidueTransportWindow) (c : ℝ) (n : ℕ) :
    Real.log (cfzp040CarrierCellExpLeft W c n) =
      cfzp039CarrierCellLeft W c n := by
  unfold cfzp040CarrierCellExpLeft
  exact Real.log_exp _

theorem cfzp040_log_carrierCellExpRight
    (W : PascalCenteredXiResidueTransportWindow) (c : ℝ) (n : ℕ) :
    Real.log (cfzp040CarrierCellExpRight W c n) =
      cfzp039CarrierCellRight W c n := by
  unfold cfzp040CarrierCellExpRight
  exact Real.log_exp _

/-- Natural left endpoint used to turn a real cell into a finite block. -/
noncomputable def cfzp040CarrierCellNaturalLeft
    (W : PascalCenteredXiResidueTransportWindow) (c : ℝ) (n : ℕ) : ℕ :=
  ⌊cfzp040CarrierCellExpLeft W c n⌋₊

/-- Natural right endpoint used to turn a real cell into a finite block. -/
noncomputable def cfzp040CarrierCellNaturalRight
    (W : PascalCenteredXiResidueTransportWindow) (c : ℝ) (n : ℕ) : ℕ :=
  ⌊cfzp040CarrierCellExpRight W c n⌋₊

/-- All primes in the finite exponential carrier cell. -/
def cfzp040RawPrimeCarrierCellSupport
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) : Finset ℕ :=
  (Finset.Ioc (cfzp040CarrierCellNaturalLeft W c n)
      (cfzp040CarrierCellNaturalRight W c n)).filter Nat.Prime

theorem cfzp040RawPrimeCarrierCellSupport_mem_iff
    {W : PascalCenteredXiResidueTransportWindow} {c : ℝ} {n p : ℕ}
    (hp : Nat.Prime p) :
    p ∈ cfzp040RawPrimeCarrierCellSupport W c n ↔
      Nat.Prime p ∧
        cfzp039CarrierCellLeft W c n < Real.log (p : ℝ) ∧
          Real.log (p : ℝ) ≤ cfzp039CarrierCellRight W c n := by
  have hp0 : p ≠ 0 := hp.ne_zero
  have hL0 : 0 < cfzp040CarrierCellExpLeft W c n :=
    cfzp040CarrierCellExpLeft_pos W c n
  have hR0 : 0 < cfzp040CarrierCellExpRight W c n :=
    cfzp040CarrierCellExpLeft_pos W c n |>.trans
      (cfzp040CarrierCellExpLeft_lt_right W c n)
  unfold cfzp040RawPrimeCarrierCellSupport
  simp only [Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨hfloorL, hfloorR⟩, _⟩
    have hp_pos_real : (0 : ℝ) < (p : ℝ) := by
      exact_mod_cast hp.pos
    have hL : cfzp040CarrierCellExpLeft W c n < (p : ℝ) := by
      apply (Nat.floor_lt' hp0).mp
      simpa [cfzp040CarrierCellNaturalLeft] using hfloorL
    have hR : (p : ℝ) ≤ cfzp040CarrierCellExpRight W c n := by
      apply (Nat.le_floor_iff' hp0).mp
      simpa [cfzp040CarrierCellNaturalRight] using hfloorR
    have hLp : cfzp039CarrierCellLeft W c n < Real.log (p : ℝ) := by
      apply Real.exp_lt_exp.mp
      simpa [cfzp040CarrierCellExpLeft, Real.exp_log hp_pos_real] using hL
    have hRp : Real.log (p : ℝ) ≤ cfzp039CarrierCellRight W c n := by
      apply Real.exp_le_exp.mp
      simpa [cfzp040CarrierCellExpRight, Real.exp_log hp_pos_real] using hR
    exact ⟨hp, hLp, hRp⟩
  · rintro ⟨_hp, hLp, hRp⟩
    have hp_pos_real : (0 : ℝ) < (p : ℝ) := by
      exact_mod_cast hp.pos
    have hL : cfzp040CarrierCellExpLeft W c n < (p : ℝ) := by
      have h := Real.exp_lt_exp.mpr hLp
      simpa [cfzp040CarrierCellExpLeft, Real.exp_log hp_pos_real] using h
    have hR : (p : ℝ) ≤ cfzp040CarrierCellExpRight W c n := by
      have h := Real.exp_le_exp.mpr hRp
      simpa [cfzp040CarrierCellExpRight, Real.exp_log hp_pos_real] using h
    refine ⟨?_, hp⟩
    constructor
    · apply (Nat.floor_lt' hp0).mpr
      simpa [cfzp040CarrierCellNaturalLeft] using hL
    · apply (Nat.le_floor_iff' hp0).mpr
      simpa [cfzp040CarrierCellNaturalRight] using hR

/-- Raw leading-carrier mass over all primes in one exponential cell. -/
noncomputable def cfzp040RawPrimeCarrierCellMass
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) : ℝ :=
  ∑ p ∈ cfzp040RawPrimeCarrierCellSupport W c n,
    cfzp034PrimeAxisSigmaWeight W p *
      cfzp036PrimeAxisLeadingPeriodicCarrier ε W (Real.log (p : ℝ))

/-! ## Gate E: raw-cell to CFZP-039 finite-block adapter -/

private theorem cfzp040_raw_prime_mem_block
    {ε : ℝ} (_hε : 0 < ε)
    {W : PascalCenteredXiResidueTransportWindow} {c : ℝ} {n p : ℕ}
    (hcell : max (3 * ε) 1 ≤ cfzp039CarrierCellLeft W c n)
    (hp : p ∈ cfzp040RawPrimeCarrierCellSupport W c n) :
    (p, 0) ∈ cfzp024PrimePowerPairBlockSupport
      (cfzp040CarrierCellNaturalLeft W c n)
      (cfzp040CarrierCellNaturalRight W c n) := by
  classical
  have hprime := (Finset.mem_filter.mp hp).2
  have hraw := (cfzp040RawPrimeCarrierCellSupport_mem_iff hprime).mp hp
  have hL : cfzp039CarrierCellLeft W c n < Real.log (p : ℝ) := hraw.2.1
  have hR : Real.log (p : ℝ) ≤ cfzp039CarrierCellRight W c n := hraw.2.2
  have hcell' : 3 * ε ≤ cfzp039CarrierCellLeft W c n ∧
      1 ≤ cfzp039CarrierCellLeft W c n := (max_le_iff.mp hcell)
  have hlog1 : 1 ≤ Real.log (p : ℝ) := le_trans hcell'.2 hL.le
  have hlog3 : 3 * ε ≤ Real.log (p : ℝ) := le_trans hcell'.1 hL.le
  have hEligible : Cfzp034PrimeAxisMassEligible ε p := ⟨hlog3, hlog1⟩
  have hpL : cfzp040CarrierCellNaturalLeft W c n < p := by
    have hp_pos_real : (0 : ℝ) < (p : ℝ) := by
      exact_mod_cast hprime.pos
    apply (Nat.floor_lt' hprime.ne_zero).mpr
    have h := (Real.exp_lt_exp.mpr hL)
    simpa [cfzp040CarrierCellExpLeft, Real.exp_log hp_pos_real] using h
  have hpR : p ≤ cfzp040CarrierCellNaturalRight W c n := by
    have hp_pos_real : (0 : ℝ) < (p : ℝ) := by
      exact_mod_cast hprime.pos
    apply (Nat.le_floor_iff' hprime.ne_zero).mpr
    have h := (Real.exp_le_exp.mpr hR)
    simpa [cfzp040CarrierCellExpRight, Real.exp_log hp_pos_real] using h
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
  exact Finset.mem_sdiff.mpr ⟨hright, hleft⟩

theorem cfzp040RawPrimeCarrierCellMass_eq_cfzp039CellMass
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (c : ℝ) (n : ℕ)
    (hcell : max (3 * ε) 1 ≤ cfzp039CarrierCellLeft W c n) :
    cfzp040RawPrimeCarrierCellMass ε W c n =
      cfzp039PrimeAxisLeadingCarrierCellMass ε W c n
        (cfzp040CarrierCellNaturalLeft W c n)
        (cfzp040CarrierCellNaturalRight W c n) := by
  classical
  unfold cfzp040RawPrimeCarrierCellMass
    cfzp039PrimeAxisLeadingCarrierCellMass
    cfzp039PrimeAxisLeadingCarrierMassOn
  let A := cfzp040CarrierCellNaturalLeft W c n
  let B := cfzp040CarrierCellNaturalRight W c n
  have himage :
      (cfzp040RawPrimeCarrierCellSupport W c n).image (fun p => (p, 0)) =
        cfzp039PrimeAxisCarrierCellPairSupport ε W c n A B := by
    ext pk
    constructor
    · intro hpk
      rcases Finset.mem_image.mp hpk with ⟨p, hp, rfl⟩
      have hblock := cfzp040_raw_prime_mem_block hε hcell hp
      have hraw := (cfzp040RawPrimeCarrierCellSupport_mem_iff
        ((Finset.mem_filter.mp hp).2)).mp hp
      have hEligible : Cfzp034PrimeAxisMassEligible ε p := by
        have hcell' : 3 * ε ≤ cfzp039CarrierCellLeft W c n ∧
            1 ≤ cfzp039CarrierCellLeft W c n := max_le_iff.mp hcell
        exact ⟨le_trans hcell'.1 hraw.2.1.le,
          le_trans hcell'.2 hraw.2.1.le⟩
      have haxis : (p, 0) ∈ cfzp034PrimeAxisPairBlockSupport A B := by
        exact Finset.mem_filter.mpr ⟨hblock, rfl⟩
      have hpair : (p, 0) ∈ cfzp034EligiblePrimeAxisPairBlockSupport ε A B := by
        exact Finset.mem_filter.mpr ⟨haxis, hEligible⟩
      have hcellmem :
          cfzp039CarrierCellLeft W c n < Real.log (p : ℝ) ∧
            Real.log (p : ℝ) ≤ cfzp039CarrierCellRight W c n :=
        ⟨hraw.2.1, hraw.2.2⟩
      exact Finset.mem_filter.mpr ⟨hpair, hcellmem⟩
    · intro hpk
      have houter := Finset.mem_filter.mp hpk
      have hcellmem := houter.2
      have hpair := houter.1
      have hpair' : pk ∈ cfzp034PrimeAxisPairBlockSupport A B ∧
          Cfzp034PrimeAxisMassEligible ε pk.1 := by
        simpa only [cfzp034EligiblePrimeAxisPairBlockSupport,
          Finset.mem_filter] using hpair
      have haxis := hpair'.1
      have hblock := (Finset.mem_filter.mp haxis).1
      have hzero : pk.2 = 0 := by
        exact (Finset.mem_filter.mp haxis).2
      have hright : pk ∈ pascalPrimePowerPairSupportUpTo B := by
        exact (Finset.mem_sdiff.mp hblock).1
      have hcoord := mem_pascalPrimeCoordinateSupportUpTo_iff.mp
        (mem_pascalPrimePowerPairSupportUpTo_iff.mp hright).1
      have hraw : pk.1 ∈ cfzp040RawPrimeCarrierCellSupport W c n := by
        apply (cfzp040RawPrimeCarrierCellSupport_mem_iff hcoord.1).mpr
        exact ⟨hcoord.1, hcellmem.1, hcellmem.2⟩
      refine Finset.mem_image.mpr ⟨pk.1, hraw, ?_⟩
      exact Prod.ext rfl hzero.symm
  rw [← himage]
  have hinj : Set.InjOn (fun p : ℕ => (p, 0))
      (cfzp040RawPrimeCarrierCellSupport W c n : Set ℕ) := by
    intro p hp q hq heq
    exact congrArg Prod.fst heq
  rw [Finset.sum_image hinj]

/-! ## Gate F: exact smooth/discrepancy decomposition -/

/-- A finite elementary smooth model for the prime-counting function. -/
noncomputable def cfzp040PrimeCountingSmoothModel (x : ℝ) : ℝ :=
  x / Real.log x

/-- The exact finite discrepancy left after subtracting the smooth model. -/
noncomputable def cfzp040PrimeCountingDiscrepancy (x : ℝ) : ℝ :=
  (Nat.primeCounting ⌊x⌋₊ : ℝ) - cfzp040PrimeCountingSmoothModel x

/-- The smooth contribution to the finite Abel identity. -/
noncomputable def cfzp040SmoothAbelCarrierModel
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (a b : ℝ) : ℝ :=
  cfzp040PrimeAxisCarrierTestFunction ε W b *
      cfzp040PrimeCountingSmoothModel b -
    cfzp040PrimeAxisCarrierTestFunction ε W a *
      cfzp040PrimeCountingSmoothModel a -
    ∫ t in Set.Ioc a b,
      deriv (cfzp040PrimeAxisCarrierTestFunction ε W) t *
        cfzp040PrimeCountingSmoothModel t

/-- The exact finite prime-counting discrepancy functional. -/
noncomputable def cfzp040PrimeCountingDiscrepancyFunctional
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (a b : ℝ) : ℝ :=
  cfzp040PrimeAxisCarrierTestFunction ε W b *
      cfzp040PrimeCountingDiscrepancy b -
    cfzp040PrimeAxisCarrierTestFunction ε W a *
      cfzp040PrimeCountingDiscrepancy a -
    ∫ t in Set.Ioc a b,
      deriv (cfzp040PrimeAxisCarrierTestFunction ε W) t *
        cfzp040PrimeCountingDiscrepancy t

theorem cfzp040PrimeCounting_eq_smooth_add_discrepancy (x : ℝ) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) =
      cfzp040PrimeCountingSmoothModel x +
        cfzp040PrimeCountingDiscrepancy x := by
  unfold cfzp040PrimeCountingDiscrepancy
  ring

/-- The actual finite prime carrier is exactly smooth Abel plus discrepancy. -/
theorem cfzp040PrimeCarrierSumIoc_eq_smooth_add_discrepancy
    {ε a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (W : PascalCenteredXiResidueTransportWindow)
    (hf_diff : ∀ t ∈ Set.Icc a b,
      DifferentiableAt ℝ (cfzp040PrimeAxisCarrierTestFunction ε W) t)
    (hf_int : IntegrableOn
      (deriv (cfzp040PrimeAxisCarrierTestFunction ε W)) (Set.Icc a b))
    (hM_int : IntegrableOn
      (fun t => deriv (cfzp040PrimeAxisCarrierTestFunction ε W) t *
        cfzp040PrimeCountingSmoothModel t) (Set.Ioc a b))
    (hD_int : IntegrableOn
      (fun t => deriv (cfzp040PrimeAxisCarrierTestFunction ε W) t *
        cfzp040PrimeCountingDiscrepancy t) (Set.Ioc a b)) :
    cfzp040PrimeCarrierSumIoc ε W a b =
      cfzp040SmoothAbelCarrierModel ε W a b +
        cfzp040PrimeCountingDiscrepancyFunctional ε W a b := by
  have habel := cfzp040PrimeCarrierSumIoc_eq_abel
    ha hab W hf_diff hf_int
  have hsplit :
      (fun t => deriv (cfzp040PrimeAxisCarrierTestFunction ε W) t *
          (Nat.primeCounting ⌊t⌋₊ : ℝ)) =
        (fun t => deriv (cfzp040PrimeAxisCarrierTestFunction ε W) t *
            cfzp040PrimeCountingSmoothModel t) +
          (fun t => deriv (cfzp040PrimeAxisCarrierTestFunction ε W) t *
            cfzp040PrimeCountingDiscrepancy t) := by
    funext t
    rw [cfzp040PrimeCounting_eq_smooth_add_discrepancy]
    simp only [Pi.add_apply]
    ring
  have hint :
      (∫ t in Set.Ioc a b,
          deriv (cfzp040PrimeAxisCarrierTestFunction ε W) t *
            (Nat.primeCounting ⌊t⌋₊ : ℝ)) =
        (∫ t in Set.Ioc a b,
            deriv (cfzp040PrimeAxisCarrierTestFunction ε W) t *
              cfzp040PrimeCountingSmoothModel t) +
          (∫ t in Set.Ioc a b,
            deriv (cfzp040PrimeAxisCarrierTestFunction ε W) t *
              cfzp040PrimeCountingDiscrepancy t) := by
    rw [hsplit]
    exact integral_add hM_int hD_int
  rw [habel]
  unfold cfzp040SmoothAbelCarrierModel
    cfzp040PrimeCountingDiscrepancyFunctional
  rw [cfzp040PrimeCounting_eq_smooth_add_discrepancy b,
    cfzp040PrimeCounting_eq_smooth_add_discrepancy a]
  rw [hint]
  ring

/-! ## Gate I: discrepancy-provider interfaces -/

/-- A pointwise finite-interval bound for the named discrepancy. -/
def Cfzp040PrimeCountingDiscrepancyBoundOn
    (a b D : ℝ) : Prop :=
  ∀ x ∈ Set.Icc a b,
    |cfzp040PrimeCountingDiscrepancy x| ≤ D

/-- A relative finite-interval bound, kept separate from any PNT theorem. -/
def Cfzp040PrimeCountingRelativeDiscrepancyBoundOn
    (a b δ : ℝ) : Prop :=
  ∀ x ∈ Set.Icc a b,
    |cfzp040PrimeCountingDiscrepancy x| ≤
      δ * cfzp040PrimeCountingSmoothModel x

/-! ## Explicit open boundary -/

/-!
The remaining statements record exactly which analytic inputs are not supplied
by the finite Abel bridge.  In particular, none of these constructors asserts
a prime-distribution estimate.
-/
inductive Cfzp040PrimeAxisFiniteAbelPrimeCountingDiscrepancyGap : Prop
  | noPrimeCountingDiscrepancyDecayProvider
  | noPrimeCountingRelativeErrorProvider
  | noSmoothAbelModelIntegralReduction
  | noLogCoordinateDensityIntegralAdapter
  | noCarrierCellAsymptoticDominanceProvider
  | noExceptionalPrimeAxisResidualElimination
  | noHigherPrimePowerResidualElimination

end DkMath.RH.CFBRCProjection
