/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.CosmicFormulaZetaSourceProjectionCloseoutAudit
import DkMath.RH.CFBRC.PascalCenteredXiCompletedZetaLogDerivBridge
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CosmicFormulaZetaCriticalLineGammaRPhaseCarrierAudit"

/-!
# CFZP-007: critical-line GammaR / Riemann--Siegel phase-carrier audit

The critical-line Archimedean factor is normalized as a unit-circle carrier.
All phase statements are branch-free: no real angle lift and no global
complex-log branch is introduced.  The remaining OOL normalization and the
CFZP-006 source-alignment backlog are deliberately left open.
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

/-! ## A. Critical-line coordinates -/

noncomputable def cfzpCriticalLinePoint (t : ℝ) : ℂ :=
  criticalLineCenter + (t : ℂ) * Complex.I

@[simp] theorem cfzpCriticalLinePoint_re (t : ℝ) :
    (cfzpCriticalLinePoint t).re = (1 : ℝ) / 2 := by
  simp [cfzpCriticalLinePoint, criticalLineCenter]

@[simp] theorem cfzpCriticalLinePoint_im (t : ℝ) :
    (cfzpCriticalLinePoint t).im = t := by
  simp [cfzpCriticalLinePoint, criticalLineCenter]

theorem cfzp_one_sub_criticalLinePoint_eq_conj (t : ℝ) :
    1 - cfzpCriticalLinePoint t = starRingEnd ℂ (cfzpCriticalLinePoint t) := by
  apply Complex.ext <;> simp [cfzpCriticalLinePoint, criticalLineCenter] <;> ring

theorem cfzpCriticalLinePoint_div_two_eq_quarter_add_half_im (t : ℝ) :
    cfzpCriticalLinePoint t / 2 =
      (1 / 4 : ℂ) + (t / 2 : ℂ) * Complex.I := by
  apply Complex.ext <;> simp [cfzpCriticalLinePoint, criticalLineCenter]
  <;> ring

/-! ## B. GammaR factorization and nonvanishing -/

noncomputable def cfzpCriticalLineGammaRCarrier (t : ℝ) : ℂ :=
  Complex.Gammaℝ (cfzpCriticalLinePoint t)

theorem cfzpCriticalLineGammaRCarrier_eq_pi_cpow_mul_quarterGamma
    (t : ℝ) :
    cfzpCriticalLineGammaRCarrier t =
      (Real.pi : ℂ) ^ (-cfzpCriticalLinePoint t / 2) *
        Complex.Gamma ((1 / 4 : ℂ) + (t / 2 : ℂ) * Complex.I) := by
  unfold cfzpCriticalLineGammaRCarrier
  rw [Complex.Gammaℝ_def, cfzpCriticalLinePoint_div_two_eq_quarter_add_half_im]

theorem cfzpCriticalLineGammaRCarrier_ne_zero (t : ℝ) :
    cfzpCriticalLineGammaRCarrier t ≠ 0 := by
  apply Complex.Gammaℝ_ne_zero_of_re_pos
  rw [cfzpCriticalLinePoint_re]
  norm_num

/-! ## C. Branch-free unit carrier -/

noncomputable def cfzpRiemannSiegelUnitCarrier (t : ℝ) : ℂ :=
  cfzpCriticalLineGammaRCarrier t /
    (‖cfzpCriticalLineGammaRCarrier t‖ : ℂ)

theorem cfzpRiemannSiegelUnitCarrier_denominator_ne_zero (t : ℝ) :
    (‖cfzpCriticalLineGammaRCarrier t‖ : ℂ) ≠ 0 := by
  have hnorm : ‖cfzpCriticalLineGammaRCarrier t‖ ≠ 0 :=
    (norm_pos_iff.mpr (cfzpCriticalLineGammaRCarrier_ne_zero t)).ne'
  exact Complex.ofReal_ne_zero.mpr
    hnorm

theorem cfzpRiemannSiegelUnitCarrier_norm (t : ℝ) :
    ‖cfzpRiemannSiegelUnitCarrier t‖ = 1 := by
  unfold cfzpRiemannSiegelUnitCarrier
  rw [norm_div]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_norm]
  exact div_self (ne_of_gt
    (norm_pos_iff.mpr (cfzpCriticalLineGammaRCarrier_ne_zero t)))

theorem cfzpRiemannSiegelUnitCarrier_ne_zero (t : ℝ) :
    cfzpRiemannSiegelUnitCarrier t ≠ 0 := by
  intro h
  have hnorm := congrArg norm h
  rw [cfzpRiemannSiegelUnitCarrier_norm] at hnorm
  norm_num at hnorm

theorem cfzpRiemannSiegelUnitCarrier_conj (t : ℝ) :
    cfzpRiemannSiegelUnitCarrier (-t) =
      starRingEnd ℂ (cfzpRiemannSiegelUnitCarrier t) := by
  unfold cfzpRiemannSiegelUnitCarrier
  unfold cfzpCriticalLineGammaRCarrier
  have hGamma := pascalXiArchimedeanGammaR_conj
    (cfzpCriticalLinePoint t)
  have hpoint : cfzpCriticalLinePoint (-t) =
      starRingEnd ℂ (cfzpCriticalLinePoint t) := by
    apply Complex.ext <;> simp [cfzpCriticalLinePoint, criticalLineCenter]
  rw [hpoint, hGamma]
  simp [map_div₀]

/-! ## D. Completed-zeta reality on the critical line -/

theorem cfzpCompletedRiemannZeta_criticalLine_conj_eq (t : ℝ) :
    completedRiemannZeta (starRingEnd ℂ (cfzpCriticalLinePoint t)) =
      starRingEnd ℂ (completedRiemannZeta (cfzpCriticalLinePoint t)) := by
  let s : ℂ := cfzpCriticalLinePoint t
  have hsre : 0 < s.re := by
    dsimp [s]
    rw [cfzpCriticalLinePoint_re]
    norm_num
  have hs0 : s ≠ 0 := by
    intro hs
    have := congrArg Complex.re hs
    simp at this
    linarith
  have hcs0 : starRingEnd ℂ s ≠ 0 := by
    intro h
    apply hs0
    simpa using congrArg (starRingEnd ℂ) h
  have hGamma : Complex.Gammaℝ s ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos hsre
  have hcgamma : Complex.Gammaℝ (starRingEnd ℂ s) ≠ 0 := by
    rw [pascalXiArchimedeanGammaR_conj]
    intro hzero
    apply hGamma
    simpa using congrArg (starRingEnd ℂ) hzero
  have hz : completedRiemannZeta s =
      riemannZeta s * Complex.Gammaℝ s := by
    exact completedRiemannZeta_eq_riemannZeta_mul_Gamma_of_ne_zero hs0 hGamma
  have hzc : completedRiemannZeta (starRingEnd ℂ s) =
      riemannZeta (starRingEnd ℂ s) * Complex.Gammaℝ (starRingEnd ℂ s) := by
    exact completedRiemannZeta_eq_riemannZeta_mul_Gamma_of_ne_zero hcs0 hcgamma
  rw [hzc, riemannZeta_conj, pascalXiArchimedeanGammaR_conj, hz]
  simp

theorem cfzpCompletedRiemannZeta_criticalLine_eq_conj (t : ℝ) :
    completedRiemannZeta (cfzpCriticalLinePoint t) =
      starRingEnd ℂ (completedRiemannZeta (cfzpCriticalLinePoint t)) := by
  have hfun := completedRiemannZeta_one_sub (cfzpCriticalLinePoint t)
  calc
    completedRiemannZeta (cfzpCriticalLinePoint t) =
        completedRiemannZeta (1 - cfzpCriticalLinePoint t) := hfun.symm
    _ = completedRiemannZeta (starRingEnd ℂ (cfzpCriticalLinePoint t)) := by
      rw [cfzp_one_sub_criticalLinePoint_eq_conj]
    _ = starRingEnd ℂ (completedRiemannZeta (cfzpCriticalLinePoint t)) :=
      cfzpCompletedRiemannZeta_criticalLine_conj_eq t

theorem cfzpCompletedRiemannZeta_criticalLine_im_eq_zero (t : ℝ) :
    (completedRiemannZeta (cfzpCriticalLinePoint t)).im = 0 := by
  apply (Complex.conj_eq_iff_im).mp
  exact (cfzpCompletedRiemannZeta_criticalLine_eq_conj t).symm

/-! ## E. Hardy/Riemann--Siegel real carrier -/

noncomputable def cfzpRiemannSiegelHardyCarrier (t : ℝ) : ℂ :=
  cfzpRiemannSiegelUnitCarrier t * riemannZeta (cfzpCriticalLinePoint t)

theorem cfzpRiemannSiegelHardyCarrier_eq_completed_div_absGammaR (t : ℝ) :
    cfzpRiemannSiegelHardyCarrier t =
      completedRiemannZeta (cfzpCriticalLinePoint t) /
        (‖cfzpCriticalLineGammaRCarrier t‖ : ℂ) := by
  unfold cfzpRiemannSiegelHardyCarrier cfzpRiemannSiegelUnitCarrier
    cfzpCriticalLineGammaRCarrier
  have hGamma := cfzpCriticalLineGammaRCarrier_ne_zero t
  have hfactor := completedRiemannZeta_eq_riemannZeta_mul_Gamma_of_ne_zero
    (s := cfzpCriticalLinePoint t)
      (by
        intro h
        have h' := congrArg Complex.re h
        rw [cfzpCriticalLinePoint_re] at h'
        norm_num at h')
      hGamma
  rw [hfactor]
  field_simp [hGamma]

theorem cfzpRiemannSiegelHardyCarrier_im_eq_zero (t : ℝ) :
    (cfzpRiemannSiegelHardyCarrier t).im = 0 := by
  rw [cfzpRiemannSiegelHardyCarrier_eq_completed_div_absGammaR]
  rw [Complex.div_ofReal_im]
  simp [cfzpCompletedRiemannZeta_criticalLine_im_eq_zero]

noncomputable def cfzpRiemannSiegelHardyReal (t : ℝ) : ℝ :=
  (cfzpRiemannSiegelHardyCarrier t).re

theorem cfzpRiemannSiegelHardyCarrier_eq_ofReal (t : ℝ) :
    cfzpRiemannSiegelHardyCarrier t =
      (cfzpRiemannSiegelHardyReal t : ℂ) := by
  apply Complex.ext
  · rfl
  · exact cfzpRiemannSiegelHardyCarrier_im_eq_zero t

theorem cfzpRiemannSiegelHardyCarrier_eq_zero_iff_riemannZeta_eq_zero
    (t : ℝ) :
    cfzpRiemannSiegelHardyCarrier t = 0 ↔
      riemannZeta (cfzpCriticalLinePoint t) = 0 := by
  unfold cfzpRiemannSiegelHardyCarrier
  rw [mul_eq_zero]
  constructor
  · rintro (hUnit | hZeta)
    · exact False.elim (cfzpRiemannSiegelUnitCarrier_ne_zero t hUnit)
    · exact hZeta
  · intro hZeta
    exact Or.inr hZeta

/-! ## F. Branch-free Archimedean phase-rate surface -/

noncomputable def cfzpRiemannSiegelPhaseRate (t : ℝ) : ℝ :=
  (logDeriv Complex.Gammaℝ (cfzpCriticalLinePoint t)).re

theorem cfzpRiemannSiegelPhaseRate_eq_neg_archimedeanLogDeriv_re (t : ℝ) :
    cfzpRiemannSiegelPhaseRate t =
      -(pascalXiArchimedeanLogDeriv (cfzpCriticalLinePoint t)).re := by
  simp [cfzpRiemannSiegelPhaseRate, pascalXiArchimedeanLogDeriv]

/-! ## G. Deliberate normalization frontier -/

inductive Cfzp007ContinuousThetaAndOolNormalizationGap : Prop
  | noContinuousRealThetaLiftAndOOLPhaseNormalizationProvided

end DkMath.RH.CFBRCProjection
