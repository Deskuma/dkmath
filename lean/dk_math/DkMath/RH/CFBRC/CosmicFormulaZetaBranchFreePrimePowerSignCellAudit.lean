/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.CosmicFormulaZetaSafeFrequencyTrigonometricPhaseBoundaryAudit
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CosmicFormulaZetaBranchFreePrimePowerSignCellAudit"

/-!
# CFZP-006W: branch-free prime-power sign cells

The safe-frequency prime-power event is rewritten as a positive scale times
a centered displacement of a real negative-frequency profile.  The profile's
local trigonometric sign cells are recorded conditionally; no universal
profile ordering, event sign, ledger monotonicity, contact reach, convergence,
zeta-zero, or RH conclusion is supplied here.
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

/-! ## A. Negative-frequency magnitude profile -/

noncomputable def cfzpNegativeFrequencyBoundaryCore
    (a u T : ℝ) : ℝ :=
  (a * u + 1) * Real.sin (u * T) - u * T * Real.cos (u * T)

noncomputable def cfzpNegativeFrequencyBoundaryProfile
    (a T u : ℝ) : ℝ :=
  Real.exp (-a * u) / u ^ 2 *
    cfzpNegativeFrequencyBoundaryCore a u T

theorem cfzpPhasePrimitiveNonzeroBoundary_neg_eq_negativeFrequencyProfile
    {a u T : ℝ} (hu : u ≠ 0) :
    cfzpPhasePrimitiveNonzeroBoundary a (-u) T =
      cfzpNegativeFrequencyBoundaryProfile a T u := by
  unfold cfzpPhasePrimitiveNonzeroBoundary
    cfzpNegativeFrequencyBoundaryProfile cfzpNegativeFrequencyBoundaryCore
  have harg : -u * T = -(u * T) := by ring
  rw [harg, Real.cos_neg, Real.sin_neg]
  have hexp : a * -u = -a * u := by ring
  rw [hexp]
  field_simp [hu]
  ring

/-! ## B. Profile/core sign classification -/

theorem cfzpNegativeFrequencyBoundaryProfile_prefactor_pos
    {a u : ℝ} (hu : 0 < u) :
    0 < Real.exp (-a * u) / u ^ 2 := by
  exact div_pos (Real.exp_pos _) (sq_pos_of_pos hu)

theorem cfzpNegativeFrequencyBoundaryProfile_eq_zero_iff_core_eq_zero
    {a T u : ℝ} (hu : 0 < u) :
    cfzpNegativeFrequencyBoundaryProfile a T u = 0 ↔
      cfzpNegativeFrequencyBoundaryCore a u T = 0 := by
  have hp := cfzpNegativeFrequencyBoundaryProfile_prefactor_pos (a := a) hu
  rw [cfzpNegativeFrequencyBoundaryProfile]
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left hp.ne'
  · intro h
    rw [h, mul_zero]

theorem cfzpNegativeFrequencyBoundaryProfile_pos_iff_core_pos
    {a T u : ℝ} (hu : 0 < u) :
    0 < cfzpNegativeFrequencyBoundaryProfile a T u ↔
      0 < cfzpNegativeFrequencyBoundaryCore a u T := by
  have hp := cfzpNegativeFrequencyBoundaryProfile_prefactor_pos (a := a) hu
  rw [cfzpNegativeFrequencyBoundaryProfile]
  constructor
  · intro h
    rcases (mul_pos_iff.mp h) with hcase | hcase
    · exact hcase.2
    · exact False.elim ((not_lt_of_ge hp.le) hcase.1)
  · intro h
    exact mul_pos hp h

theorem cfzpNegativeFrequencyBoundaryProfile_neg_iff_core_neg
    {a T u : ℝ} (hu : 0 < u) :
    cfzpNegativeFrequencyBoundaryProfile a T u < 0 ↔
      cfzpNegativeFrequencyBoundaryCore a u T < 0 := by
  have hp := cfzpNegativeFrequencyBoundaryProfile_prefactor_pos (a := a) hu
  rw [cfzpNegativeFrequencyBoundaryProfile]
  constructor
  · intro h
    rcases (mul_neg_iff.mp h) with hcase | hcase
    · exact hcase.2
    · exact False.elim ((not_lt_of_ge hp.le) hcase.1)
  · intro h
    exact mul_neg_of_pos_of_neg hp h

theorem cfzpNegativeFrequencyBoundaryProfile_nonneg_iff_core_nonneg
    {a T u : ℝ} (hu : 0 < u) :
    0 ≤ cfzpNegativeFrequencyBoundaryProfile a T u ↔
      0 ≤ cfzpNegativeFrequencyBoundaryCore a u T := by
  have hp := cfzpNegativeFrequencyBoundaryProfile_prefactor_pos (a := a) hu
  rw [cfzpNegativeFrequencyBoundaryProfile]
  constructor
  · intro h
    by_contra hcore
    have hcore' : cfzpNegativeFrequencyBoundaryCore a u T < 0 :=
      lt_of_not_ge hcore
    exact (not_lt_of_ge h) (mul_neg_of_pos_of_neg hp hcore')
  · intro h
    exact mul_nonneg hp.le h

theorem cfzpNegativeFrequencyBoundaryProfile_nonpos_iff_core_nonpos
    {a T u : ℝ} (hu : 0 < u) :
    cfzpNegativeFrequencyBoundaryProfile a T u ≤ 0 ↔
      cfzpNegativeFrequencyBoundaryCore a u T ≤ 0 := by
  have hp := cfzpNegativeFrequencyBoundaryProfile_prefactor_pos (a := a) hu
  rw [cfzpNegativeFrequencyBoundaryProfile]
  constructor
  · intro h
    by_contra hcore
    have hcore' : 0 < cfzpNegativeFrequencyBoundaryCore a u T :=
      lt_of_not_ge hcore
    exact (not_lt_of_ge h) (mul_pos hp hcore')
  · intro h
    exact mul_nonpos_of_nonneg_of_nonpos hp.le h

/-! ## C. Prime-power centered coordinates -/

noncomputable def cfzpPrimePowerPhaseCenter
    (p j : ℕ) : ℝ :=
  (j : ℝ) * Real.log (p : ℝ)

noncomputable def cfzpPrimePowerPhaseMagnitudeLeft
    (ε : ℝ) (p j : ℕ) : ℝ :=
  cfzpPrimePowerPhaseCenter p j - ε

noncomputable def cfzpPrimePowerPhaseMagnitudeRight
    (ε : ℝ) (p j : ℕ) : ℝ :=
  cfzpPrimePowerPhaseCenter p j + ε

theorem cfzpPrimePowerPhaseMagnitudes_pos_of_epsilon_lt_log_two
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    {p j : ℕ} (hp : Nat.Prime p) (hj : 0 < j) :
    0 < cfzpPrimePowerPhaseMagnitudeLeft ε p j ∧
      0 < cfzpPrimePowerPhaseMagnitudeRight ε p j := by
  have hneg := cfzpPrimePowerPhaseFrequencies_negative_of_epsilon_lt_log_two
    hε hε2 hp hj
  have hplus := cfzpModePhaseFrequencyPlus_eq_of_eq_prime_pow
    (ε := ε) hp hj
  have hfreqplus : ε - (j : ℝ) * Real.log (p : ℝ) < 0 := by
    rw [← hplus]
    exact hneg.1
  have hleft : 0 < cfzpPrimePowerPhaseMagnitudeLeft ε p j := by
    rw [cfzpPrimePowerPhaseMagnitudeLeft, cfzpPrimePowerPhaseCenter]
    linarith
  have hright : 0 < cfzpPrimePowerPhaseMagnitudeRight ε p j := by
    rw [cfzpPrimePowerPhaseMagnitudeRight, cfzpPrimePowerPhaseCenter]
    linarith [hleft, hε]
  exact ⟨hleft, hright⟩

theorem cfzpPrimePowerPhaseMagnitude_left_lt_right
    {ε : ℝ} (hε : 0 < ε) (p j : ℕ) :
    cfzpPrimePowerPhaseMagnitudeLeft ε p j <
      cfzpPrimePowerPhaseMagnitudeRight ε p j := by
  rw [cfzpPrimePowerPhaseMagnitudeLeft, cfzpPrimePowerPhaseMagnitudeRight]
  linarith

theorem cfzpPrimePowerPhaseFrequencies_eq_neg_magnitudes
    {ε : ℝ} {p j : ℕ} (hp : Nat.Prime p) (hj : 0 < j) :
    cfzpModePhaseFrequencyPlus ε (p ^ j) =
        -cfzpPrimePowerPhaseMagnitudeLeft ε p j ∧
      cfzpModePhaseFrequencyMinus ε (p ^ j) =
        -cfzpPrimePowerPhaseMagnitudeRight ε p j := by
  have hplus := cfzpModePhaseFrequencyPlus_eq_of_eq_prime_pow
    (ε := ε) hp hj
  have hminus := cfzpModePhaseFrequencyMinus_eq_of_eq_prime_pow
    (ε := ε) hp hj
  constructor
  · rw [hplus, cfzpPrimePowerPhaseMagnitudeLeft, cfzpPrimePowerPhaseCenter]
    ring
  · rw [hminus, cfzpPrimePowerPhaseMagnitudeRight, cfzpPrimePowerPhaseCenter]
    ring

/-! ## D. Positive event scale and centered displacement -/

noncomputable def cfzpPrimePowerEventPositiveScale
    (ε : ℝ) (p j : ℕ) : ℝ :=
  2 * Real.log (p : ℝ) *
    ((2 * ε)⁻¹ * cfzpModeCriticalScale (p ^ j))

theorem cfzpPrimePowerEventPositiveScale_pos
    {ε : ℝ} (hε : 0 < ε)
    {p j : ℕ} (hp : Nat.Prime p) (_hj : 0 < j) :
    0 < cfzpPrimePowerEventPositiveScale ε p j := by
  have hlog : 0 < Real.log (p : ℝ) := by
    apply Real.log_pos
    exact_mod_cast hp.one_lt
  have hscale : 0 < (2 * ε)⁻¹ * cfzpModeCriticalScale (p ^ j) := by
    exact mul_pos (inv_pos.mpr (mul_pos (by norm_num) hε))
      (cfzpModeCriticalScale_pos (p ^ j))
  exact mul_pos (mul_pos (by norm_num) hlog) hscale

theorem cfzpPrimePowerBranchFreeTrigEvent_eq_positiveScale_mul_centeredProfileDifference
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {p j : ℕ} (hp : Nat.Prime p) (hj : 0 < j) :
    cfzpPrimePowerBranchFreeTrigEvent ε W p j =
      cfzpPrimePowerEventPositiveScale ε p j *
        (cfzpNegativeFrequencyBoundaryProfile
            (cfzpModePhaseAbscissa W) W.rectangle.T
            (cfzpPrimePowerPhaseMagnitudeLeft ε p j) -
          cfzpNegativeFrequencyBoundaryProfile
            (cfzpModePhaseAbscissa W) W.rectangle.T
            (cfzpPrimePowerPhaseMagnitudeRight ε p j)) := by
  have hmag := cfzpPrimePowerPhaseMagnitudes_pos_of_epsilon_lt_log_two
    hε hε2 hp hj
  have hplus := cfzpModePhaseFrequencyPlus_eq_of_eq_prime_pow
    (ε := ε) hp hj
  have hminus := cfzpModePhaseFrequencyMinus_eq_of_eq_prime_pow
    (ε := ε) hp hj
  have hfreq := cfzpPrimePowerPhaseFrequencies_eq_neg_magnitudes (ε := ε) hp hj
  have hleft :
      ε - (j : ℝ) * Real.log (p : ℝ) =
        -cfzpPrimePowerPhaseMagnitudeLeft ε p j := by
    calc
      ε - (j : ℝ) * Real.log (p : ℝ) =
          cfzpModePhaseFrequencyPlus ε (p ^ j) := hplus.symm
      _ = -cfzpPrimePowerPhaseMagnitudeLeft ε p j := hfreq.1
  have hright :
      -ε - (j : ℝ) * Real.log (p : ℝ) =
        -cfzpPrimePowerPhaseMagnitudeRight ε p j := by
    calc
      -ε - (j : ℝ) * Real.log (p : ℝ) =
          cfzpModePhaseFrequencyMinus ε (p ^ j) := hminus.symm
      _ = -cfzpPrimePowerPhaseMagnitudeRight ε p j := hfreq.2
  unfold cfzpPrimePowerBranchFreeTrigEvent cfzpPrimePowerEventPositiveScale
  rw [hleft, hright,
    cfzpPhasePrimitiveNonzeroBoundary_neg_eq_negativeFrequencyProfile
      hmag.1.ne',
    cfzpPhasePrimitiveNonzeroBoundary_neg_eq_negativeFrequencyProfile
      hmag.2.ne']
  ring

/-! ## E. Event sign and centered-profile order -/

theorem cfzpPrimePowerBranchFreeTrigEvent_eq_zero_iff_centeredProfile_eq
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {p j : ℕ} (hp : Nat.Prime p) (hj : 0 < j) :
    cfzpPrimePowerBranchFreeTrigEvent ε W p j = 0 ↔
      cfzpNegativeFrequencyBoundaryProfile
          (cfzpModePhaseAbscissa W) W.rectangle.T
          (cfzpPrimePowerPhaseMagnitudeLeft ε p j) =
        cfzpNegativeFrequencyBoundaryProfile
          (cfzpModePhaseAbscissa W) W.rectangle.T
          (cfzpPrimePowerPhaseMagnitudeRight ε p j) := by
  rw [cfzpPrimePowerBranchFreeTrigEvent_eq_positiveScale_mul_centeredProfileDifference
    hε hε2 W hp hj]
  have hs := cfzpPrimePowerEventPositiveScale_pos hε hp hj
  constructor
  · intro h
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hs.ne')
  · intro h
    rw [sub_eq_zero.mpr h, mul_zero]

theorem cfzpPrimePowerBranchFreeTrigEvent_pos_iff_centeredProfile_gt
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {p j : ℕ} (hp : Nat.Prime p) (hj : 0 < j) :
    0 < cfzpPrimePowerBranchFreeTrigEvent ε W p j ↔
      cfzpNegativeFrequencyBoundaryProfile
          (cfzpModePhaseAbscissa W) W.rectangle.T
          (cfzpPrimePowerPhaseMagnitudeRight ε p j) <
        cfzpNegativeFrequencyBoundaryProfile
          (cfzpModePhaseAbscissa W) W.rectangle.T
          (cfzpPrimePowerPhaseMagnitudeLeft ε p j) := by
  rw [cfzpPrimePowerBranchFreeTrigEvent_eq_positiveScale_mul_centeredProfileDifference
    hε hε2 W hp hj]
  have hs := cfzpPrimePowerEventPositiveScale_pos hε hp hj
  constructor
  · intro h
    rcases (mul_pos_iff.mp h) with hcase | hcase
    · exact sub_pos.mp hcase.2
    · exact False.elim ((not_lt_of_ge hs.le) hcase.1)
  · intro h
    exact mul_pos hs (sub_pos.mpr h)

theorem cfzpPrimePowerBranchFreeTrigEvent_neg_iff_centeredProfile_lt
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {p j : ℕ} (hp : Nat.Prime p) (hj : 0 < j) :
    cfzpPrimePowerBranchFreeTrigEvent ε W p j < 0 ↔
      cfzpNegativeFrequencyBoundaryProfile
          (cfzpModePhaseAbscissa W) W.rectangle.T
          (cfzpPrimePowerPhaseMagnitudeLeft ε p j) <
        cfzpNegativeFrequencyBoundaryProfile
          (cfzpModePhaseAbscissa W) W.rectangle.T
          (cfzpPrimePowerPhaseMagnitudeRight ε p j) := by
  rw [cfzpPrimePowerBranchFreeTrigEvent_eq_positiveScale_mul_centeredProfileDifference
    hε hε2 W hp hj]
  have hs := cfzpPrimePowerEventPositiveScale_pos hε hp hj
  constructor
  · intro h
    rcases (mul_neg_iff.mp h) with hcase | hcase
    · exact sub_neg.mp hcase.2
    · exact False.elim ((not_lt_of_ge hs.le) hcase.1)
  · intro h
    exact mul_neg_of_pos_of_neg hs (sub_neg.mpr h)

theorem cfzpPrimePowerBranchFreeTrigEvent_nonneg_iff_centeredProfile_ge
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {p j : ℕ} (hp : Nat.Prime p) (hj : 0 < j) :
    0 ≤ cfzpPrimePowerBranchFreeTrigEvent ε W p j ↔
      cfzpNegativeFrequencyBoundaryProfile
          (cfzpModePhaseAbscissa W) W.rectangle.T
          (cfzpPrimePowerPhaseMagnitudeRight ε p j) ≤
        cfzpNegativeFrequencyBoundaryProfile
          (cfzpModePhaseAbscissa W) W.rectangle.T
          (cfzpPrimePowerPhaseMagnitudeLeft ε p j) := by
  rw [cfzpPrimePowerBranchFreeTrigEvent_eq_positiveScale_mul_centeredProfileDifference
    hε hε2 W hp hj]
  have hs := cfzpPrimePowerEventPositiveScale_pos hε hp hj
  constructor
  · intro h
    by_contra hnot
    have hdiff :
        cfzpNegativeFrequencyBoundaryProfile
            (cfzpModePhaseAbscissa W) W.rectangle.T
            (cfzpPrimePowerPhaseMagnitudeLeft ε p j) -
          cfzpNegativeFrequencyBoundaryProfile
            (cfzpModePhaseAbscissa W) W.rectangle.T
            (cfzpPrimePowerPhaseMagnitudeRight ε p j) < 0 := by
      linarith
    exact (not_lt_of_ge h) (mul_neg_of_pos_of_neg hs hdiff)
  · intro h
    exact mul_nonneg hs.le (sub_nonneg.mpr h)

theorem cfzpPrimePowerBranchFreeTrigEvent_nonpos_iff_centeredProfile_le
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {p j : ℕ} (hp : Nat.Prime p) (hj : 0 < j) :
    cfzpPrimePowerBranchFreeTrigEvent ε W p j ≤ 0 ↔
      cfzpNegativeFrequencyBoundaryProfile
          (cfzpModePhaseAbscissa W) W.rectangle.T
          (cfzpPrimePowerPhaseMagnitudeLeft ε p j) ≤
        cfzpNegativeFrequencyBoundaryProfile
          (cfzpModePhaseAbscissa W) W.rectangle.T
          (cfzpPrimePowerPhaseMagnitudeRight ε p j) := by
  rw [cfzpPrimePowerBranchFreeTrigEvent_eq_positiveScale_mul_centeredProfileDifference
    hε hε2 W hp hj]
  have hs := cfzpPrimePowerEventPositiveScale_pos hε hp hj
  constructor
  · intro h
    by_contra hnot
    have hdiff : 0 <
        cfzpNegativeFrequencyBoundaryProfile
            (cfzpModePhaseAbscissa W) W.rectangle.T
            (cfzpPrimePowerPhaseMagnitudeLeft ε p j) -
          cfzpNegativeFrequencyBoundaryProfile
            (cfzpModePhaseAbscissa W) W.rectangle.T
            (cfzpPrimePowerPhaseMagnitudeRight ε p j) := by
      linarith
    exact (not_lt_of_ge h) (mul_pos hs hdiff)
  · intro h
    exact mul_nonpos_of_nonneg_of_nonpos hs.le (sub_nonpos.mpr h)

/-! ## F. Local trigonometric sign cells -/

theorem cfzpNegativeFrequencyBoundaryCore_nonneg_of_sin_nonneg_cos_nonpos
    {a u T : ℝ} (ha : 0 ≤ a) (hu : 0 < u) (hT : 0 ≤ T)
    (hsin : 0 ≤ Real.sin (u * T)) (hcos : Real.cos (u * T) ≤ 0) :
    0 ≤ cfzpNegativeFrequencyBoundaryCore a u T := by
  have hau : 0 ≤ a * u := mul_nonneg ha hu.le
  have hcoef : 0 ≤ a * u + 1 := by linarith
  have hfirst : 0 ≤ (a * u + 1) * Real.sin (u * T) :=
    mul_nonneg hcoef hsin
  have hut : 0 ≤ u * T := mul_nonneg hu.le hT
  have hsecond : u * T * Real.cos (u * T) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hut hcos
  unfold cfzpNegativeFrequencyBoundaryCore
  linarith

theorem cfzpNegativeFrequencyBoundaryProfile_nonneg_of_sin_nonneg_cos_nonpos
    {a u T : ℝ} (ha : 0 ≤ a) (hu : 0 < u) (hT : 0 ≤ T)
    (hsin : 0 ≤ Real.sin (u * T)) (hcos : Real.cos (u * T) ≤ 0) :
    0 ≤ cfzpNegativeFrequencyBoundaryProfile a T u := by
  exact (cfzpNegativeFrequencyBoundaryProfile_nonneg_iff_core_nonneg hu).mpr
    (cfzpNegativeFrequencyBoundaryCore_nonneg_of_sin_nonneg_cos_nonpos
      ha hu hT hsin hcos)

theorem cfzpNegativeFrequencyBoundaryCore_nonpos_of_sin_nonpos_cos_nonneg
    {a u T : ℝ} (ha : 0 ≤ a) (hu : 0 < u) (hT : 0 ≤ T)
    (hsin : Real.sin (u * T) ≤ 0) (hcos : 0 ≤ Real.cos (u * T)) :
    cfzpNegativeFrequencyBoundaryCore a u T ≤ 0 := by
  have hau : 0 ≤ a * u := mul_nonneg ha hu.le
  have hcoef : 0 ≤ a * u + 1 := by linarith
  have hfirst : (a * u + 1) * Real.sin (u * T) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hcoef hsin
  have hut : 0 ≤ u * T := mul_nonneg hu.le hT
  have hsecond : 0 ≤ u * T * Real.cos (u * T) :=
    mul_nonneg hut hcos
  unfold cfzpNegativeFrequencyBoundaryCore
  linarith

theorem cfzpNegativeFrequencyBoundaryProfile_nonpos_of_sin_nonpos_cos_nonneg
    {a u T : ℝ} (ha : 0 ≤ a) (hu : 0 < u) (hT : 0 ≤ T)
    (hsin : Real.sin (u * T) ≤ 0) (hcos : 0 ≤ Real.cos (u * T)) :
    cfzpNegativeFrequencyBoundaryProfile a T u ≤ 0 := by
  exact (cfzpNegativeFrequencyBoundaryProfile_nonpos_iff_core_nonpos hu).mpr
    (cfzpNegativeFrequencyBoundaryCore_nonpos_of_sin_nonpos_cos_nonneg
      ha hu hT hsin hcos)

/-! ## G. Explicit frontier -/

inductive CfzpPrimePowerBoundaryProfileMonotonicityGap : Prop
  | noIndependentSafeFrequencyBoundaryProfileMonotonicityProvider

end DkMath.RH.CFBRCProjection
