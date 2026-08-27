/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.CosmicFormulaZetaCriticalLineAngularVelocityAudit
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CosmicFormulaZetaCriticalLineAngularVelocityBalanceAudit"

/-!
# CFZP-0035: critical-line completed-zeta angular balance

This module closes the completed-zeta balance left by CFZP-0034.  The
argument is local and branch-free: the completed product is real on the
critical line, its real-path derivative is therefore real, and its
nonvanishing value forces the zeta and `Gammaℝ` logarithmic rates to cancel.
No angle branch, zero count, or RH implication is introduced.
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

/-! ## A. Factorized completed-zeta product path -/

/-- The ordinary-zeta times `Gammaℝ` product along the critical line. -/
noncomputable def cfzpCriticalLineCompletedProductPath (t : ℝ) : ℂ :=
  riemannZeta (cfzpCriticalLinePoint t) *
    Complex.Gammaℝ (cfzpCriticalLinePoint t)

private theorem cfzpCriticalLinePoint_ne_zero (t : ℝ) :
    cfzpCriticalLinePoint t ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  simp at hre

/-- The product path is exactly Mathlib's completed zeta on the line. -/
theorem cfzpCriticalLineCompletedProductPath_eq_completedRiemannZeta (t : ℝ) :
    cfzpCriticalLineCompletedProductPath t =
      completedRiemannZeta (cfzpCriticalLinePoint t) := by
  unfold cfzpCriticalLineCompletedProductPath
  symm
  exact completedRiemannZeta_eq_riemannZeta_mul_Gamma_of_ne_zero
    (cfzpCriticalLinePoint_ne_zero t)
    (cfzpCriticalLineGammaRCarrier_ne_zero t)

/-! ## B. Real-path derivative of the product -/

private theorem cfzpCriticalLinePoint_hasDerivAt (t : ℝ) :
    HasDerivAt cfzpCriticalLinePoint Complex.I t := by
  change HasDerivAt
    (fun u : ℝ => criticalLineCenter + (u : ℂ) * Complex.I) Complex.I t
  have hreal : HasDerivAt (Complex.ofRealCLM : ℝ → ℂ) 1 t :=
    Complex.ofRealCLM.hasDerivAt
  have hconst : HasDerivAt (fun _ : ℝ => criticalLineCenter) 0 t :=
    hasDerivAt_const t criticalLineCenter
  have hadd := hconst.add (hreal.const_mul Complex.I)
  have hfun :
      (fun x : ℝ => criticalLineCenter) +
          (fun y : ℝ => Complex.I * Complex.ofRealCLM y) =
        (fun u : ℝ => criticalLineCenter + (u : ℂ) * Complex.I) := by
    funext u
    simp only [Pi.add_apply, Complex.ofRealCLM_apply]
    ring
  rw [hfun] at hadd
  simpa using hadd

private theorem differentiableAt_Gammaℝ_of_ne_zero
    {s : ℂ} (hGamma : Complex.Gammaℝ s ≠ 0) :
    DifferentiableAt ℂ Complex.Gammaℝ s := by
  have hi : DifferentiableAt ℂ (fun t : ℂ => (Complex.Gammaℝ t)⁻¹) s :=
    Complex.differentiable_Gammaℝ_inv.differentiableAt
  have hii := hi.inv (inv_ne_zero hGamma)
  have hfun : (fun t : ℂ => ((Complex.Gammaℝ t)⁻¹)⁻¹) =
      Complex.Gammaℝ := by
    funext t
    simp only [inv_inv]
  rw [← hfun]
  exact hii

private theorem cfzpCriticalLineGammaRPath_hasDerivAt (t : ℝ) :
    HasDerivAt
      (fun u : ℝ => Complex.Gammaℝ (cfzpCriticalLinePoint u))
      (Complex.I * deriv Complex.Gammaℝ (cfzpCriticalLinePoint t)) t := by
  have hg := (differentiableAt_Gammaℝ_of_ne_zero
    (cfzpCriticalLineGammaRCarrier_ne_zero t)).hasDerivAt
  have hgreal : HasFDerivAt Complex.Gammaℝ
      ((deriv Complex.Gammaℝ (cfzpCriticalLinePoint t)) •
        (1 : ℂ →L[ℝ] ℂ)) (cfzpCriticalLinePoint t) :=
    HasDerivAt.complexToReal_fderiv hg
  have hcomp := hgreal.comp_hasDerivAt t
    (cfzpCriticalLinePoint_hasDerivAt t)
  simpa only [Function.comp_def, smul_apply, one_apply_eq_self, smul_eq_mul,
    mul_comm] using hcomp

/-- The completed product is real-valued on the critical line. -/
theorem cfzpCriticalLineCompletedProductPath_im_eq_zero (t : ℝ) :
    (cfzpCriticalLineCompletedProductPath t).im = 0 := by
  rw [cfzpCriticalLineCompletedProductPath_eq_completedRiemannZeta]
  exact cfzpCompletedRiemannZeta_criticalLine_im_eq_zero t

/-- The real derivative of the product's imaginary part is zero. -/
theorem cfzpCriticalLineCompletedProductPath_im_deriv_eq_zero (t : ℝ) :
    deriv (fun u : ℝ =>
      (cfzpCriticalLineCompletedProductPath u).im) t = 0 := by
  have hfun : (fun u : ℝ =>
      (cfzpCriticalLineCompletedProductPath u).im) = (fun _ => 0) := by
    funext u
    exact cfzpCriticalLineCompletedProductPath_im_eq_zero u
  rw [hfun]
  simp

/-! ## C. The numerator real-part balance -/

/-- Product differentiation gives the numerator's real part as zero. -/
theorem cfzpCriticalLineCompletedProduct_rate_numerator_re_eq_zero (t : ℝ) :
    (deriv riemannZeta (cfzpCriticalLinePoint t) *
        Complex.Gammaℝ (cfzpCriticalLinePoint t) +
      riemannZeta (cfzpCriticalLinePoint t) *
        deriv Complex.Gammaℝ (cfzpCriticalLinePoint t)).re = 0 := by
  let numerator : ℂ :=
    deriv riemannZeta (cfzpCriticalLinePoint t) *
        Complex.Gammaℝ (cfzpCriticalLinePoint t) +
      riemannZeta (cfzpCriticalLinePoint t) *
        deriv Complex.Gammaℝ (cfzpCriticalLinePoint t)
  let raw : ℂ :=
    (deriv riemannZeta (cfzpCriticalLinePoint t) •
        (1 : ℂ →L[ℝ] ℂ)) Complex.I *
      Complex.Gammaℝ (cfzpCriticalLinePoint t) +
      riemannZeta (cfzpCriticalLinePoint t) *
        (Complex.I * deriv Complex.Gammaℝ (cfzpCriticalLinePoint t))
  have hpoint : cfzpCriticalLinePoint t ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
  have hz' := (differentiableAt_riemannZeta hpoint).hasDerivAt
  have hzreal : HasFDerivAt riemannZeta
      ((deriv riemannZeta (cfzpCriticalLinePoint t)) •
        (1 : ℂ →L[ℝ] ℂ)) (cfzpCriticalLinePoint t) :=
    HasDerivAt.complexToReal_fderiv hz'
  have hz := hzreal.comp_hasDerivAt t
    (cfzpCriticalLinePoint_hasDerivAt t)
  have hprod := hz.mul (cfzpCriticalLineGammaRPath_hasDerivAt t)
  have him := (hasDerivAt_const t Complex.imCLM).clm_apply hprod
  have hderiv : deriv (fun u : ℝ =>
      (cfzpCriticalLineCompletedProductPath u).im) t = raw.im := by
    simpa only [Function.comp_def, Pi.mul_apply,
      cfzpCriticalLineCompletedProductPath, raw, Complex.imCLM_apply,
      zero_apply, zero_add] using him.deriv
  have hzero := cfzpCriticalLineCompletedProductPath_im_deriv_eq_zero t
  have hrate : raw = Complex.I * numerator := by
    simp only [raw, numerator, smul_apply, one_apply_eq_self, smul_eq_mul]
    ring
  have hnum : (Complex.I * numerator).im = 0 := by
    calc
      (Complex.I * numerator).im = raw.im := by rw [hrate]
      _ = deriv (fun u : ℝ =>
          (cfzpCriticalLineCompletedProductPath u).im) t := hderiv.symm
      _ = 0 := hzero
  simpa [numerator, Complex.mul_im] using hnum

/-! ## D. Logarithmic-rate balance -/

/-- The zeta and `Gammaℝ` logarithmic rates cancel on nonzero points. -/
theorem cfzpCriticalLineZetaLogRate_add_GammaRLogRate_eq_zero
    (t : ℝ)
    (hzeta : riemannZeta (cfzpCriticalLinePoint t) ≠ 0) :
    (deriv riemannZeta (cfzpCriticalLinePoint t) /
        riemannZeta (cfzpCriticalLinePoint t)).re +
      (logDeriv Complex.Gammaℝ (cfzpCriticalLinePoint t)).re = 0 := by
  let z : ℂ := riemannZeta (cfzpCriticalLinePoint t)
  let g : ℂ := Complex.Gammaℝ (cfzpCriticalLinePoint t)
  let dz : ℂ := deriv riemannZeta (cfzpCriticalLinePoint t)
  let dg : ℂ := deriv Complex.Gammaℝ (cfzpCriticalLinePoint t)
  let numerator : ℂ := dz * g + z * dg
  have hz : z ≠ 0 := hzeta
  have hg : g ≠ 0 := cfzpCriticalLineGammaRCarrier_ne_zero t
  have hnum : numerator.re = 0 := by
    simpa [numerator, z, g, dz, dg] using
      cfzpCriticalLineCompletedProduct_rate_numerator_re_eq_zero t
  have hprod_im : (z * g).im = 0 := by
    simpa only [z, g, cfzpCriticalLineCompletedProductPath] using
      cfzpCriticalLineCompletedProductPath_im_eq_zero t
  have hprime_im : (Complex.I * numerator).im = 0 := by
    simp [Complex.mul_im, hnum]
  have hquot_im : ((Complex.I * numerator) / (z * g)).im = 0 := by
    rw [Complex.div_im]
    simp [hprod_im, hprime_im]
  have hnum_quot_re : (numerator / (z * g)).re = 0 := by
    have hquot_im' := hquot_im
    rw [mul_div_assoc] at hquot_im'
    simpa [Complex.mul_im] using hquot_im'
  have hquot : dz / z + dg / g = numerator / (z * g) := by
    field_simp [hz, hg]
    ring
  calc
    (deriv riemannZeta (cfzpCriticalLinePoint t) /
        riemannZeta (cfzpCriticalLinePoint t)).re +
        (logDeriv Complex.Gammaℝ (cfzpCriticalLinePoint t)).re =
      (dz / z + dg / g).re := by
        simp [z, g, dz, dg, logDeriv_apply]
    _ = (numerator / (z * g)).re := by rw [hquot]
    _ = 0 := hnum_quot_re

/-! ## E. Final Riemann--Siegel phase-rate balance -/

/-- Zeta angular velocity is the negative Riemann--Siegel GammaR phase rate. -/
theorem cfzpCriticalLineZetaAngularVelocity_eq_neg_riemannSiegelPhaseRate
    (t : ℝ)
    (hzeta : riemannZeta (cfzpCriticalLinePoint t) ≠ 0) :
    cfzpCriticalLineZetaAngularVelocity t =
      -cfzpRiemannSiegelPhaseRate t := by
  have hbalance := cfzpCriticalLineZetaLogRate_add_GammaRLogRate_eq_zero
    t hzeta
  rw [cfzpCriticalLineZetaAngularVelocity_eq_zetaLogDeriv_re t hzeta]
  unfold cfzpRiemannSiegelPhaseRate
  linarith

end DkMath.RH.CFBRCProjection
