/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.CosmicFormulaZetaCriticalLineGammaRPhaseCarrierAudit
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CosmicFormulaZetaCriticalLineProjectivePhaseNormalizationAudit"

/-!
# CFZP-008: projective doubled-phase normalization on the critical line

At a nonzero critical-line zeta value, the normalized zeta carrier splits as
the real Hardy sign times the conjugate of the normalized `Gammaℝ` carrier.
Squaring removes that sign and gives the branch-free projective normalization
corresponding to the historical OOL doubled-phase convention.

This file does not introduce a complex-argument branch, a global logarithm branch, a
continuous real angle lift, or a zero-jump counting theorem.  It also does not
close the CFZP-006 source-projection backlog.
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

/-! ## A. Critical-line zeta unit carrier -/

noncomputable def cfzpCriticalLineZetaUnitCarrier (t : ℝ) : ℂ :=
  riemannZeta (cfzpCriticalLinePoint t) /
    (‖riemannZeta (cfzpCriticalLinePoint t)‖ : ℂ)

theorem cfzpCriticalLineZetaUnitCarrier_denominator_ne_zero
    (t : ℝ) (hzeta : riemannZeta (cfzpCriticalLinePoint t) ≠ 0) :
    (‖riemannZeta (cfzpCriticalLinePoint t)‖ : ℂ) ≠ 0 := by
  have hnorm : ‖riemannZeta (cfzpCriticalLinePoint t)‖ ≠ 0 :=
    (norm_pos_iff.mpr hzeta).ne'
  exact Complex.ofReal_ne_zero.mpr hnorm

theorem cfzpCriticalLineZetaUnitCarrier_norm
    (t : ℝ) (hzeta : riemannZeta (cfzpCriticalLinePoint t) ≠ 0) :
    ‖cfzpCriticalLineZetaUnitCarrier t‖ = 1 := by
  unfold cfzpCriticalLineZetaUnitCarrier
  rw [norm_div]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_norm]
  exact div_self (ne_of_gt (norm_pos_iff.mpr hzeta))

theorem cfzpCriticalLineZetaUnitCarrier_ne_zero
    (t : ℝ) (hzeta : riemannZeta (cfzpCriticalLinePoint t) ≠ 0) :
    cfzpCriticalLineZetaUnitCarrier t ≠ 0 := by
  intro h
  have hnorm := congrArg norm h
  rw [cfzpCriticalLineZetaUnitCarrier_norm t hzeta] at hnorm
  norm_num at hnorm

/-! ## B. Hardy real sign carrier -/

noncomputable def cfzpRiemannSiegelHardySignCarrier (t : ℝ) : ℝ :=
  cfzpRiemannSiegelHardyReal t /
    |cfzpRiemannSiegelHardyReal t|

theorem cfzpRiemannSiegelHardyReal_ne_zero_of_riemannZeta_ne_zero
    (t : ℝ) (hzeta : riemannZeta (cfzpCriticalLinePoint t) ≠ 0) :
    cfzpRiemannSiegelHardyReal t ≠ 0 := by
  intro hHardy
  apply hzeta
  apply (cfzpRiemannSiegelHardyCarrier_eq_zero_iff_riemannZeta_eq_zero t).mp
  rw [cfzpRiemannSiegelHardyCarrier_eq_ofReal, hHardy]
  simp

theorem cfzpRiemannSiegelHardySignCarrier_sq
    (t : ℝ) (hHardy : cfzpRiemannSiegelHardyReal t ≠ 0) :
    cfzpRiemannSiegelHardySignCarrier t ^ 2 = 1 := by
  unfold cfzpRiemannSiegelHardySignCarrier
  rw [div_pow, sq_abs]
  field_simp [abs_ne_zero.mpr hHardy]

theorem cfzpRiemannSiegelHardySignCarrier_eq_one_or_neg_one
    (t : ℝ) (hHardy : cfzpRiemannSiegelHardyReal t ≠ 0) :
    cfzpRiemannSiegelHardySignCarrier t = 1 ∨
      cfzpRiemannSiegelHardySignCarrier t = -1 := by
  exact (sq_eq_one_iff).mp (cfzpRiemannSiegelHardySignCarrier_sq t hHardy)

theorem cfzpRiemannSiegelHardySignCarrier_abs
    (t : ℝ) (hHardy : cfzpRiemannSiegelHardyReal t ≠ 0) :
    |cfzpRiemannSiegelHardySignCarrier t| = 1 := by
  unfold cfzpRiemannSiegelHardySignCarrier
  rw [abs_div, abs_of_nonneg (abs_nonneg _)]
  exact div_self (abs_ne_zero.mpr hHardy)

theorem cfzpRiemannSiegelHardySignCarrier_sq_of_riemannZeta_ne_zero
    (t : ℝ) (hzeta : riemannZeta (cfzpCriticalLinePoint t) ≠ 0) :
    cfzpRiemannSiegelHardySignCarrier t ^ 2 = 1 :=
  cfzpRiemannSiegelHardySignCarrier_sq t
    (cfzpRiemannSiegelHardyReal_ne_zero_of_riemannZeta_ne_zero t hzeta)

/-! ## C. Exact smooth/sign decomposition -/

theorem cfzpCriticalLineUnitCarrier_conj_mul_self (t : ℝ) :
    starRingEnd ℂ (cfzpRiemannSiegelUnitCarrier t) *
        cfzpRiemannSiegelUnitCarrier t = 1 := by
  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq,
    cfzpRiemannSiegelUnitCarrier_norm]
  norm_num

theorem cfzpCriticalLineZeta_eq_hardyReal_mul_conj_unitCarrier
    (t : ℝ) :
    riemannZeta (cfzpCriticalLinePoint t) =
      (cfzpRiemannSiegelHardyReal t : ℂ) *
        starRingEnd ℂ (cfzpRiemannSiegelUnitCarrier t) := by
  have hHardy :
      cfzpRiemannSiegelUnitCarrier t *
          riemannZeta (cfzpCriticalLinePoint t) =
        (cfzpRiemannSiegelHardyReal t : ℂ) := by
    simpa [cfzpRiemannSiegelHardyCarrier] using
      (cfzpRiemannSiegelHardyCarrier_eq_ofReal t)
  calc
    riemannZeta (cfzpCriticalLinePoint t) =
        1 * riemannZeta (cfzpCriticalLinePoint t) := by simp
    _ = (starRingEnd ℂ (cfzpRiemannSiegelUnitCarrier t) *
          cfzpRiemannSiegelUnitCarrier t) *
          riemannZeta (cfzpCriticalLinePoint t) := by
      rw [cfzpCriticalLineUnitCarrier_conj_mul_self]
    _ = starRingEnd ℂ (cfzpRiemannSiegelUnitCarrier t) *
          (cfzpRiemannSiegelUnitCarrier t *
            riemannZeta (cfzpCriticalLinePoint t)) := by ring
    _ = starRingEnd ℂ (cfzpRiemannSiegelUnitCarrier t) *
          (cfzpRiemannSiegelHardyReal t : ℂ) := by rw [hHardy]
    _ = (cfzpRiemannSiegelHardyReal t : ℂ) *
          starRingEnd ℂ (cfzpRiemannSiegelUnitCarrier t) := by ring

theorem cfzpCriticalLineZeta_norm_eq_abs_hardyReal
    (t : ℝ) :
    ‖riemannZeta (cfzpCriticalLinePoint t)‖ =
      |cfzpRiemannSiegelHardyReal t| := by
  rw [cfzpCriticalLineZeta_eq_hardyReal_mul_conj_unitCarrier,
    norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_conj, cfzpRiemannSiegelUnitCarrier_norm]
  simp

theorem cfzpCriticalLineZetaUnitCarrier_eq_hardySign_mul_conj_riemannSiegelUnitCarrier
    (t : ℝ) (hzeta : riemannZeta (cfzpCriticalLinePoint t) ≠ 0) :
    cfzpCriticalLineZetaUnitCarrier t =
      (cfzpRiemannSiegelHardySignCarrier t : ℂ) *
        starRingEnd ℂ (cfzpRiemannSiegelUnitCarrier t) := by
  have hHardy := cfzpRiemannSiegelHardyReal_ne_zero_of_riemannZeta_ne_zero t hzeta
  have habs : |cfzpRiemannSiegelHardyReal t| ≠ 0 := abs_ne_zero.mpr hHardy
  unfold cfzpCriticalLineZetaUnitCarrier
  rw [cfzpCriticalLineZeta_norm_eq_abs_hardyReal,
    cfzpCriticalLineZeta_eq_hardyReal_mul_conj_unitCarrier]
  unfold cfzpRiemannSiegelHardySignCarrier
  rw [Complex.ofReal_div]
  field_simp [habs]

/-! ## D. Projective doubled-phase carrier -/

noncomputable def cfzpOOLCriticalLineProjectiveDoubledPhaseCarrier (t : ℝ) : ℂ :=
  cfzpCriticalLineZetaUnitCarrier t ^ 2

noncomputable def cfzpRiemannSiegelSmoothProjectiveDoubledPhaseCarrier (t : ℝ) : ℂ :=
  (starRingEnd ℂ (cfzpRiemannSiegelUnitCarrier t)) ^ 2

theorem cfzpOOLCriticalLineProjectiveDoubledPhaseCarrier_eq_smooth
    (t : ℝ) (hzeta : riemannZeta (cfzpCriticalLinePoint t) ≠ 0) :
    cfzpOOLCriticalLineProjectiveDoubledPhaseCarrier t =
      cfzpRiemannSiegelSmoothProjectiveDoubledPhaseCarrier t := by
  unfold cfzpOOLCriticalLineProjectiveDoubledPhaseCarrier
    cfzpRiemannSiegelSmoothProjectiveDoubledPhaseCarrier
  rw [cfzpCriticalLineZetaUnitCarrier_eq_hardySign_mul_conj_riemannSiegelUnitCarrier
    t hzeta, mul_pow]
  have hsignC :
      (cfzpRiemannSiegelHardySignCarrier t : ℂ) ^ 2 = 1 := by
    exact_mod_cast cfzpRiemannSiegelHardySignCarrier_sq_of_riemannZeta_ne_zero
      t hzeta
  rw [hsignC]
  simp

theorem cfzpCriticalLineZetaUnitCarrier_mul_unitCarrier_sq_eq_one
    (t : ℝ) (hzeta : riemannZeta (cfzpCriticalLinePoint t) ≠ 0) :
    (cfzpCriticalLineZetaUnitCarrier t *
        cfzpRiemannSiegelUnitCarrier t) ^ 2 = 1 := by
  have hsign :=
    cfzpRiemannSiegelHardySignCarrier_sq_of_riemannZeta_ne_zero t hzeta
  have hunit := cfzpCriticalLineUnitCarrier_conj_mul_self t
  rw [cfzpCriticalLineZetaUnitCarrier_eq_hardySign_mul_conj_riemannSiegelUnitCarrier
    t hzeta]
  have hcollapse :
      ((cfzpRiemannSiegelHardySignCarrier t : ℂ) *
          starRingEnd ℂ (cfzpRiemannSiegelUnitCarrier t)) *
          cfzpRiemannSiegelUnitCarrier t =
        (cfzpRiemannSiegelHardySignCarrier t : ℂ) := by
    rw [mul_assoc, hunit, mul_one]
  rw [hcollapse]
  exact_mod_cast hsign

/-! ## E. Deliberate angle/jump frontier -/

inductive Cfzp008RealAngleLiftAndZeroJumpLedgerGap : Prop
  | noGlobalRealAngleLiftOrZeroJumpCountingIdentificationProvided

/-!
The projective carrier is exact at every nonzero critical-line point.  The
real-angle lift, unwrapped jump ledger, and any zero-counting identification
remain separate normalization problems.  The CFZP-006 common-baseline and
amplitude/source-projection backlog is not discharged here.
-/

end DkMath.RH.CFBRCProjection
