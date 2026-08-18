/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.CosmicFormulaZetaBranchFreePrimePowerSignCellAudit
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CosmicFormulaZetaNegativeFrequencyProfileDerivativeAudit"

/-!
# CFZP-006X: negative-frequency profile derivative audit

The negative-frequency boundary profile is differentiated on the positive
real half-line.  Its derivative is reduced to an explicit trigonometric core,
then used only for conditional local monotonicity and centered event-sign
adapters.  No global monotonicity, universal event sign, ledger conclusion,
contact reach, convergence, zeta-zero, or RH conclusion is supplied here.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.Analysis
open DkMath.NumberTheory
open DkMath.NumberTheory.PrimitiveSet
open Filter
open MeasureTheory
open Set
open scoped ComplexConjugate Interval Topology

/-! ## A. Exact derivative core and profile derivative -/

noncomputable def cfzpNegativeFrequencyBoundaryProfileDerivativeSinCoeff
    (a T u : ℝ) : ℝ :=
  u ^ 2 * (T ^ 2 - a ^ 2) - 2 * (a * u + 1)

noncomputable def cfzpNegativeFrequencyBoundaryProfileDerivativeCore
    (a T u : ℝ) : ℝ :=
  cfzpNegativeFrequencyBoundaryProfileDerivativeSinCoeff a T u *
      Real.sin (u * T) +
    2 * T * u * (a * u + 1) * Real.cos (u * T)

theorem cfzpNegativeFrequencyBoundaryProfile_hasDerivAt
    {a T u : ℝ} (hu : u ≠ 0) :
    HasDerivAt
      (fun x : ℝ => cfzpNegativeFrequencyBoundaryProfile a T x)
      (Real.exp (-a * u) / u ^ 3 *
        cfzpNegativeFrequencyBoundaryProfileDerivativeCore a T u) u := by
  unfold cfzpNegativeFrequencyBoundaryProfile
  have hE : HasDerivAt (fun x : ℝ => Real.exp (-a * x))
      (-a * Real.exp (-a * u)) u := by
    simpa [Function.comp_def, mul_comm, mul_left_comm, mul_assoc] using
      (Real.hasDerivAt_exp (-a * u)).comp u
        ((hasDerivAt_id u).const_mul (-a))
  have hsin : HasDerivAt (fun x : ℝ => Real.sin (x * T))
      (T * Real.cos (u * T)) u := by
    simpa [Function.comp_def, id_eq, mul_comm, mul_left_comm, mul_assoc] using
      (Real.hasDerivAt_sin (u * T)).comp u
        ((hasDerivAt_id u).mul_const T)
  have hcos : HasDerivAt (fun x : ℝ => Real.cos (x * T))
      (-T * Real.sin (u * T)) u := by
    simpa [Function.comp_def, id_eq, mul_comm, mul_left_comm, mul_assoc] using
      (Real.hasDerivAt_cos (u * T)).comp u
        ((hasDerivAt_id u).mul_const T)
  have hcoef : HasDerivAt (fun x : ℝ => a * x + 1) a u := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      ((hasDerivAt_id u).const_mul a).add_const 1
  have hxt : HasDerivAt (fun x : ℝ => x * T) T u := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (hasDerivAt_id u).mul_const T
  have hfirst := hcoef.mul hsin
  have hsecond := hxt.mul hcos
  have hcore0 := hfirst.sub hsecond
  have hcore : HasDerivAt
      (fun x : ℝ => (a * x + 1) * Real.sin (x * T) -
        x * T * Real.cos (x * T))
      ((a * u + 1) * (T * Real.cos (u * T)) +
          a * Real.sin (u * T) -
          (T * Real.cos (u * T) +
          (u * T) * (-T * Real.sin (u * T)))) u := by
    have hcore1 : HasDerivAt
        (fun x : ℝ => (a * x + 1) * Real.sin (x * T) -
          x * T * Real.cos (x * T))
        (a * Real.sin (u * T) +
          (a * u + 1) * (T * Real.cos (u * T)) -
          (T * Real.cos (u * T) +
            u * T * (-T * Real.sin (u * T)))) u := by
      apply hcore0.congr_of_eventuallyEq
      filter_upwards [] with x
      rfl
    exact hcore1.congr_deriv (by ring)
  have hden0 := (hasDerivAt_id u).pow 2
  have hden : HasDerivAt (fun x : ℝ => x ^ 2) (2 * u) u := by
    have hden1 : HasDerivAt (fun x : ℝ => x ^ 2)
        (↑2 * u ^ (2 - 1) * 1) u := by
      apply hden0.congr_of_eventuallyEq
      filter_upwards [] with x
      rfl
    exact hden1.congr_deriv (by norm_num)
  have hfactor := hE.div hden (pow_ne_zero 2 hu)
  have hprofile := hfactor.mul hcore
  have hprofile' : HasDerivAt
      (fun x : ℝ => Real.exp (-a * x) / x ^ 2 *
        ((a * x + 1) * Real.sin (x * T) -
          x * T * Real.cos (x * T)))
      (((-a * Real.exp (-a * u) * u ^ 2 - Real.exp (-a * u) * (2 * u)) /
          (u ^ 2) ^ 2) *
        ((a * u + 1) * Real.sin (u * T) - u * T * Real.cos (u * T)) +
        (Real.exp (-a * u) / u ^ 2) *
          ((a * u + 1) * (T * Real.cos (u * T)) +
            a * Real.sin (u * T) -
    (T * Real.cos (u * T) +
              (u * T) * (-T * Real.sin (u * T))))) u := by
    have hprofile1 : HasDerivAt
        (fun x : ℝ => Real.exp (-a * x) / x ^ 2 *
          ((a * x + 1) * Real.sin (x * T) -
            x * T * Real.cos (x * T)))
        (((-a * Real.exp (-a * u) * u ^ 2 - Real.exp (-a * u) * (2 * u)) /
            (u ^ 2) ^ 2) *
          ((a * u + 1) * Real.sin (u * T) - u * T * Real.cos (u * T)) +
          (Real.exp (-a * u) / u ^ 2) *
            ((a * u + 1) * (T * Real.cos (u * T)) +
              a * Real.sin (u * T) -
              (T * Real.cos (u * T) +
                (u * T) * (-T * Real.sin (u * T))))) u := by
      apply hprofile.congr_of_eventuallyEq
      filter_upwards [] with x
      rfl
    exact hprofile1.congr_deriv (by ring)
  unfold cfzpNegativeFrequencyBoundaryCore
  apply hprofile'.congr_deriv
  field_simp [hu]
  unfold cfzpNegativeFrequencyBoundaryProfileDerivativeCore
    cfzpNegativeFrequencyBoundaryProfileDerivativeSinCoeff
  ring

theorem cfzpNegativeFrequencyBoundaryProfile_deriv
    {a T u : ℝ} (hu : u ≠ 0) :
    deriv (fun x : ℝ => cfzpNegativeFrequencyBoundaryProfile a T x) u =
      Real.exp (-a * u) / u ^ 3 *
        cfzpNegativeFrequencyBoundaryProfileDerivativeCore a T u := by
  exact (cfzpNegativeFrequencyBoundaryProfile_hasDerivAt hu).deriv

/-! ## B. Derivative sign reduction -/

theorem cfzpNegativeFrequencyBoundaryProfile_deriv_prefactor_pos
    {a u : ℝ} (hu : 0 < u) :
    0 < Real.exp (-a * u) / u ^ 3 := by
  exact div_pos (Real.exp_pos _) (by positivity)

theorem cfzpNegativeFrequencyBoundaryProfile_deriv_eq_zero_iff_derivativeCore_eq_zero
    {a T u : ℝ} (hu : 0 < u) :
    deriv (fun x : ℝ => cfzpNegativeFrequencyBoundaryProfile a T x) u = 0 ↔
      cfzpNegativeFrequencyBoundaryProfileDerivativeCore a T u = 0 := by
  rw [cfzpNegativeFrequencyBoundaryProfile_deriv hu.ne']
  have hp := cfzpNegativeFrequencyBoundaryProfile_deriv_prefactor_pos (a := a) hu
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left hp.ne'
  · intro h
    rw [h, mul_zero]

theorem cfzpNegativeFrequencyBoundaryProfile_deriv_pos_iff_derivativeCore_pos
    {a T u : ℝ} (hu : 0 < u) :
    0 < deriv (fun x : ℝ => cfzpNegativeFrequencyBoundaryProfile a T x) u ↔
      0 < cfzpNegativeFrequencyBoundaryProfileDerivativeCore a T u := by
  rw [cfzpNegativeFrequencyBoundaryProfile_deriv hu.ne']
  have hp := cfzpNegativeFrequencyBoundaryProfile_deriv_prefactor_pos (a := a) hu
  constructor
  · intro h
    rcases (mul_pos_iff.mp h) with hcase | hcase
    · exact hcase.2
    · exact False.elim ((not_lt_of_ge hp.le) hcase.1)
  · intro h
    exact mul_pos hp h

theorem cfzpNegativeFrequencyBoundaryProfile_deriv_neg_iff_derivativeCore_neg
    {a T u : ℝ} (hu : 0 < u) :
    deriv (fun x : ℝ => cfzpNegativeFrequencyBoundaryProfile a T x) u < 0 ↔
      cfzpNegativeFrequencyBoundaryProfileDerivativeCore a T u < 0 := by
  rw [cfzpNegativeFrequencyBoundaryProfile_deriv hu.ne']
  have hp := cfzpNegativeFrequencyBoundaryProfile_deriv_prefactor_pos (a := a) hu
  constructor
  · intro h
    rcases (mul_neg_iff.mp h) with hcase | hcase
    · exact hcase.2
    · exact False.elim ((not_lt_of_ge hp.le) hcase.1)
  · intro h
    exact mul_neg_of_pos_of_neg hp h

theorem cfzpNegativeFrequencyBoundaryProfile_deriv_nonneg_iff_derivativeCore_nonneg
    {a T u : ℝ} (hu : 0 < u) :
    0 ≤ deriv (fun x : ℝ => cfzpNegativeFrequencyBoundaryProfile a T x) u ↔
      0 ≤ cfzpNegativeFrequencyBoundaryProfileDerivativeCore a T u := by
  rw [cfzpNegativeFrequencyBoundaryProfile_deriv hu.ne']
  have hp := cfzpNegativeFrequencyBoundaryProfile_deriv_prefactor_pos (a := a) hu
  constructor
  · intro h
    by_contra hcore
    have hcore' : cfzpNegativeFrequencyBoundaryProfileDerivativeCore a T u < 0 :=
      lt_of_not_ge hcore
    exact (not_lt_of_ge h) (mul_neg_of_pos_of_neg hp hcore')
  · intro h
    exact mul_nonneg hp.le h

theorem cfzpNegativeFrequencyBoundaryProfile_deriv_nonpos_iff_derivativeCore_nonpos
    {a T u : ℝ} (hu : 0 < u) :
    deriv (fun x : ℝ => cfzpNegativeFrequencyBoundaryProfile a T x) u ≤ 0 ↔
      cfzpNegativeFrequencyBoundaryProfileDerivativeCore a T u ≤ 0 := by
  rw [cfzpNegativeFrequencyBoundaryProfile_deriv hu.ne']
  have hp := cfzpNegativeFrequencyBoundaryProfile_deriv_prefactor_pos (a := a) hu
  constructor
  · intro h
    by_contra hcore
    have hcore' : 0 < cfzpNegativeFrequencyBoundaryProfileDerivativeCore a T u :=
      lt_of_not_ge hcore
    exact (not_lt_of_ge h) (mul_pos hp hcore')
  · intro h
    exact mul_nonpos_of_nonneg_of_nonpos hp.le h

/-! ## C. Conditional derivative-core sign cells -/

theorem cfzpNegativeFrequencyBoundaryProfileDerivativeCore_cosCoefficient_pos
    {a T u : ℝ} (ha : 0 ≤ a) (hT : 0 < T) (hu : 0 < u) :
    0 < 2 * T * u * (a * u + 1) := by
  have hcoef : 0 < a * u + 1 := by
    have : 0 ≤ a * u := mul_nonneg ha hu.le
    linarith
  exact mul_pos (mul_pos (mul_pos (by norm_num) hT) hu) hcoef

theorem cfzpNegativeFrequencyBoundaryProfileDerivativeCore_nonpos_of_sinCoeff_nonneg_sin_nonpos_cos_nonpos
    {a T u : ℝ} (ha : 0 ≤ a) (hT : 0 < T) (hu : 0 < u)
    (hA : 0 ≤ cfzpNegativeFrequencyBoundaryProfileDerivativeSinCoeff a T u)
    (hsin : Real.sin (u * T) ≤ 0) (hcos : Real.cos (u * T) ≤ 0) :
    cfzpNegativeFrequencyBoundaryProfileDerivativeCore a T u ≤ 0 := by
  have hfirst :
      cfzpNegativeFrequencyBoundaryProfileDerivativeSinCoeff a T u *
          Real.sin (u * T) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hA hsin
  have hsecond :
      2 * T * u * (a * u + 1) * Real.cos (u * T) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos
      (cfzpNegativeFrequencyBoundaryProfileDerivativeCore_cosCoefficient_pos
        ha hT hu).le hcos
  unfold cfzpNegativeFrequencyBoundaryProfileDerivativeCore
  exact add_nonpos hfirst hsecond

theorem cfzpNegativeFrequencyBoundaryProfileDerivativeCore_nonneg_of_sinCoeff_nonpos_sin_nonpos_cos_nonneg
    {a T u : ℝ} (ha : 0 ≤ a) (hT : 0 < T) (hu : 0 < u)
    (hA : cfzpNegativeFrequencyBoundaryProfileDerivativeSinCoeff a T u ≤ 0)
    (hsin : Real.sin (u * T) ≤ 0) (hcos : 0 ≤ Real.cos (u * T)) :
    0 ≤ cfzpNegativeFrequencyBoundaryProfileDerivativeCore a T u := by
  have hfirst : 0 ≤
      cfzpNegativeFrequencyBoundaryProfileDerivativeSinCoeff a T u *
          Real.sin (u * T) :=
    mul_nonneg_of_nonpos_of_nonpos hA hsin
  have hsecond : 0 ≤
      2 * T * u * (a * u + 1) * Real.cos (u * T) :=
    mul_nonneg (cfzpNegativeFrequencyBoundaryProfileDerivativeCore_cosCoefficient_pos
      ha hT hu).le hcos
  unfold cfzpNegativeFrequencyBoundaryProfileDerivativeCore
  exact add_nonneg hfirst hsecond

theorem cfzpNegativeFrequencyBoundaryProfileDerivativeSinCoeff_neg_of_T_le_a
    {a T u : ℝ} (ha : 0 ≤ a) (hT : 0 ≤ T) (hu : 0 < u)
    (hTa : T ≤ a) :
    cfzpNegativeFrequencyBoundaryProfileDerivativeSinCoeff a T u < 0 := by
  have hsq : T ^ 2 - a ^ 2 ≤ 0 := by
    nlinarith
  have hfirst : u ^ 2 * (T ^ 2 - a ^ 2) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sq_nonneg u) hsq
  have hcoef : 0 < a * u + 1 := by
    have : 0 ≤ a * u := mul_nonneg ha hu.le
    linarith
  unfold cfzpNegativeFrequencyBoundaryProfileDerivativeSinCoeff
  nlinarith

/-! ## D. Conditional local monotonicity -/

theorem cfzpNegativeFrequencyBoundaryProfile_antitoneOn_Icc_of_derivativeCore_nonpos
    {a T l r : ℝ} (hl : 0 < l) (_hlr : l < r)
    (hcore : ∀ u ∈ Set.Ioo l r,
      cfzpNegativeFrequencyBoundaryProfileDerivativeCore a T u ≤ 0) :
    AntitoneOn (fun u : ℝ => cfzpNegativeFrequencyBoundaryProfile a T u)
      (Set.Icc l r) := by
  apply antitoneOn_of_deriv_nonpos (D := Set.Icc l r) (convex_Icc l r)
  · intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le hl hx.1
    exact ((cfzpNegativeFrequencyBoundaryProfile_hasDerivAt hxpos.ne').continuousAt).continuousWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    have hxpos : 0 < x := lt_trans hl hx.1
    exact ((cfzpNegativeFrequencyBoundaryProfile_hasDerivAt hxpos.ne').differentiableAt).differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    have hxpos : 0 < x := lt_trans hl hx.1
    rw [cfzpNegativeFrequencyBoundaryProfile_deriv hxpos.ne']
    exact mul_nonpos_of_nonneg_of_nonpos
      (cfzpNegativeFrequencyBoundaryProfile_deriv_prefactor_pos hxpos).le
      (hcore x hx)

theorem cfzpNegativeFrequencyBoundaryProfile_monotoneOn_Icc_of_derivativeCore_nonneg
    {a T l r : ℝ} (hl : 0 < l) (_hlr : l < r)
    (hcore : ∀ u ∈ Set.Ioo l r,
      0 ≤ cfzpNegativeFrequencyBoundaryProfileDerivativeCore a T u) :
    MonotoneOn (fun u : ℝ => cfzpNegativeFrequencyBoundaryProfile a T u)
      (Set.Icc l r) := by
  apply monotoneOn_of_deriv_nonneg (D := Set.Icc l r) (convex_Icc l r)
  · intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le hl hx.1
    exact ((cfzpNegativeFrequencyBoundaryProfile_hasDerivAt hxpos.ne').continuousAt).continuousWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    have hxpos : 0 < x := lt_trans hl hx.1
    exact ((cfzpNegativeFrequencyBoundaryProfile_hasDerivAt hxpos.ne').differentiableAt).differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    have hxpos : 0 < x := lt_trans hl hx.1
    rw [cfzpNegativeFrequencyBoundaryProfile_deriv hxpos.ne']
    exact mul_nonneg (cfzpNegativeFrequencyBoundaryProfile_deriv_prefactor_pos hxpos).le
      (hcore x hx)

/-! ## E. Prime-power centered-interval event sign adapters -/

theorem cfzpPrimePowerBranchFreeTrigEvent_nonneg_of_derivativeCore_nonpos_on_centeredInterval
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {p j : ℕ} (hp : Nat.Prime p) (hj : 0 < j)
    (hcore : ∀ u ∈ Set.Ioo
        (cfzpPrimePowerPhaseMagnitudeLeft ε p j)
        (cfzpPrimePowerPhaseMagnitudeRight ε p j),
      cfzpNegativeFrequencyBoundaryProfileDerivativeCore
        (cfzpModePhaseAbscissa W) W.rectangle.T u ≤ 0) :
    0 ≤ cfzpPrimePowerBranchFreeTrigEvent ε W p j := by
  have hmag := cfzpPrimePowerPhaseMagnitudes_pos_of_epsilon_lt_log_two
    hε hε2 hp hj
  have hlt := cfzpPrimePowerPhaseMagnitude_left_lt_right hε p j
  have hmono := cfzpNegativeFrequencyBoundaryProfile_antitoneOn_Icc_of_derivativeCore_nonpos
    hmag.1 hlt hcore
  have horder := hmono (show cfzpPrimePowerPhaseMagnitudeLeft ε p j ∈
      Set.Icc (cfzpPrimePowerPhaseMagnitudeLeft ε p j)
        (cfzpPrimePowerPhaseMagnitudeRight ε p j) by
          exact ⟨le_rfl, hlt.le⟩)
    (show cfzpPrimePowerPhaseMagnitudeRight ε p j ∈
      Set.Icc (cfzpPrimePowerPhaseMagnitudeLeft ε p j)
        (cfzpPrimePowerPhaseMagnitudeRight ε p j) by
          exact ⟨hlt.le, le_rfl⟩)
    hlt.le
  exact (cfzpPrimePowerBranchFreeTrigEvent_nonneg_iff_centeredProfile_ge
    hε hε2 W hp hj).mpr horder

theorem cfzpPrimePowerBranchFreeTrigEvent_nonpos_of_derivativeCore_nonneg_on_centeredInterval
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {p j : ℕ} (hp : Nat.Prime p) (hj : 0 < j)
    (hcore : ∀ u ∈ Set.Ioo
        (cfzpPrimePowerPhaseMagnitudeLeft ε p j)
        (cfzpPrimePowerPhaseMagnitudeRight ε p j),
      0 ≤ cfzpNegativeFrequencyBoundaryProfileDerivativeCore
        (cfzpModePhaseAbscissa W) W.rectangle.T u) :
    cfzpPrimePowerBranchFreeTrigEvent ε W p j ≤ 0 := by
  have hmag := cfzpPrimePowerPhaseMagnitudes_pos_of_epsilon_lt_log_two
    hε hε2 hp hj
  have hlt := cfzpPrimePowerPhaseMagnitude_left_lt_right hε p j
  have hmono := cfzpNegativeFrequencyBoundaryProfile_monotoneOn_Icc_of_derivativeCore_nonneg
    hmag.1 hlt hcore
  have horder := hmono (show cfzpPrimePowerPhaseMagnitudeLeft ε p j ∈
      Set.Icc (cfzpPrimePowerPhaseMagnitudeLeft ε p j)
        (cfzpPrimePowerPhaseMagnitudeRight ε p j) by
          exact ⟨le_rfl, hlt.le⟩)
    (show cfzpPrimePowerPhaseMagnitudeRight ε p j ∈
      Set.Icc (cfzpPrimePowerPhaseMagnitudeLeft ε p j)
        (cfzpPrimePowerPhaseMagnitudeRight ε p j) by
          exact ⟨hlt.le, le_rfl⟩)
    hlt.le
  exact (cfzpPrimePowerBranchFreeTrigEvent_nonpos_iff_centeredProfile_le
    hε hε2 W hp hj).mpr horder

/-! ## F. Explicit frontier -/

inductive CfzpPrimePowerCenteredDerivativeCellCoverageGap : Prop
  | noIndependentPrimePowerCenteredIntervalDerivativeSignCellProvider

end DkMath.RH.CFBRCProjection
