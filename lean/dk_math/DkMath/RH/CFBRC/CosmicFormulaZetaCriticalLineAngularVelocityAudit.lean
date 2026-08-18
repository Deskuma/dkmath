/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.CosmicFormulaZetaCriticalLineProjectivePhaseNormalizationAudit
import DkMath.RH.CFBRC.PascalCenteredXiCompletedZetaLogDerivBridge
import DkMath.RH.CFBRC.CosmicFormulaZetaCommonBaselineAlignmentReachAudit
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CosmicFormulaZetaCriticalLineAngularVelocityAudit"

/-!
# CFZP-0034: critical-line zeta angular velocity

This module formalizes local complex angular velocity without an angle branch.
It does not introduce zero-counting, RH, or a global phase convention.
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

/-! ## A. Generic branch-free angular velocity -/

/-- The Cartesian angular velocity of a complex state and velocity. -/
noncomputable def cfzpComplexAngularVelocity (z dz : ℂ) : ℝ :=
  (starRingEnd ℂ z * dz).im / Complex.normSq z

/-- Cartesian expansion of the generic angular velocity. -/
theorem cfzpComplexAngularVelocity_eq_cartesian
    (z dz : ℂ) :
  cfzpComplexAngularVelocity z dz =
      (z.re * dz.im - z.im * dz.re) /
        (z.re ^ 2 + z.im ^ 2) := by
  simp [cfzpComplexAngularVelocity, Complex.normSq, Complex.mul_im]
  ring

/-- At a nonzero state, angular velocity is the imaginary part of `dz / z`. -/
theorem cfzpComplexAngularVelocity_eq_div_im
    {z dz : ℂ} (_hz : z ≠ 0) :
    cfzpComplexAngularVelocity z dz = (dz / z).im := by
  rw [cfzpComplexAngularVelocity_eq_cartesian, Complex.div_im]
  simp [Complex.normSq]
  ring

/-! ## B. Critical-line zeta path and its real derivatives -/

/-- The ordinary zeta path along `s(t) = 1/2 + i t`. -/
noncomputable def cfzpCriticalLineZetaPath (t : ℝ) : ℂ :=
  riemannZeta (cfzpCriticalLinePoint t)

/-- The velocity supplied by the complex chain rule on the critical line. -/
noncomputable def cfzpCriticalLineZetaComplexVelocity (t : ℝ) : ℂ :=
  Complex.I * deriv riemannZeta (cfzpCriticalLinePoint t)

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

private theorem cfzpCriticalLinePoint_ne_one (t : ℝ) :
    cfzpCriticalLinePoint t ≠ 1 := by
  intro h
  have hre := congrArg Complex.re h
  simp at hre

private theorem cfzpCriticalLineZetaPath_hasDerivAt (t : ℝ) :
    HasDerivAt cfzpCriticalLineZetaPath
      (cfzpCriticalLineZetaComplexVelocity t) t := by
  have hz := (differentiableAt_riemannZeta
    (cfzpCriticalLinePoint_ne_one t)).hasDerivAt
  have hzreal : HasFDerivAt riemannZeta
      ((deriv riemannZeta (cfzpCriticalLinePoint t)) •
        (1 : ℂ →L[ℝ] ℂ)) (cfzpCriticalLinePoint t) :=
    HasDerivAt.complexToReal_fderiv hz
  have hcomp : HasDerivAt
      (riemannZeta ∘ cfzpCriticalLinePoint)
      (((deriv riemannZeta (cfzpCriticalLinePoint t)) •
        (1 : ℂ →L[ℝ] ℂ)) Complex.I) t :=
    hzreal.comp_hasDerivAt t (cfzpCriticalLinePoint_hasDerivAt t)
  change HasDerivAt
    (fun u : ℝ => riemannZeta (cfzpCriticalLinePoint u))
    (Complex.I * deriv riemannZeta (cfzpCriticalLinePoint t)) t
  simpa only [Function.comp_def, smul_apply, one_apply_eq_self, smul_eq_mul,
    mul_comm] using hcomp

/-- The derivative of the real part of the critical-line zeta path. -/
theorem cfzpCriticalLineZeta_re_deriv (t : ℝ) :
    deriv (fun u : ℝ => (riemannZeta (cfzpCriticalLinePoint u)).re) t =
      (cfzpCriticalLineZetaComplexVelocity t).re := by
  have hreal : HasDerivAt
      (fun u : ℝ => (Complex.reCLM : ℂ → ℝ)
        (cfzpCriticalLineZetaPath u))
      ((Complex.reCLM : ℂ → ℝ)
        (cfzpCriticalLineZetaComplexVelocity t)) t :=
    by
      simpa using (hasDerivAt_const t Complex.reCLM).clm_apply
        (cfzpCriticalLineZetaPath_hasDerivAt t)
  simpa only [cfzpCriticalLineZetaPath, Complex.reCLM_apply] using hreal.deriv

/-- The derivative of the imaginary part of the critical-line zeta path. -/
theorem cfzpCriticalLineZeta_im_deriv (t : ℝ) :
    deriv (fun u : ℝ => (riemannZeta (cfzpCriticalLinePoint u)).im) t =
      (cfzpCriticalLineZetaComplexVelocity t).im := by
  have him : HasDerivAt
      (fun u : ℝ => (Complex.imCLM : ℂ → ℝ)
        (cfzpCriticalLineZetaPath u))
      ((Complex.imCLM : ℂ → ℝ)
        (cfzpCriticalLineZetaComplexVelocity t)) t :=
    by
      simpa using (hasDerivAt_const t Complex.imCLM).clm_apply
        (cfzpCriticalLineZetaPath_hasDerivAt t)
  simpa only [cfzpCriticalLineZetaPath, Complex.imCLM_apply] using him.deriv

/-! ## C. OOL Cartesian phase-velocity surface -/

/-- The branch-free angular velocity of the critical-line zeta path. -/
noncomputable def cfzpCriticalLineZetaAngularVelocity (t : ℝ) : ℝ :=
  cfzpComplexAngularVelocity
    (riemannZeta (cfzpCriticalLinePoint t))
    (cfzpCriticalLineZetaComplexVelocity t)

/-- The OOL Cartesian phase-velocity formula with actual real derivatives. -/
theorem cfzpCriticalLineZetaAngularVelocity_eq_cartesian_derivatives
    (t : ℝ) :
    cfzpCriticalLineZetaAngularVelocity t =
      ((riemannZeta (cfzpCriticalLinePoint t)).re *
          deriv (fun u : ℝ =>
            (riemannZeta (cfzpCriticalLinePoint u)).im) t -
        (riemannZeta (cfzpCriticalLinePoint t)).im *
          deriv (fun u : ℝ =>
            (riemannZeta (cfzpCriticalLinePoint u)).re) t) /
        ((riemannZeta (cfzpCriticalLinePoint t)).re ^ 2 +
          (riemannZeta (cfzpCriticalLinePoint t)).im ^ 2) := by
  unfold cfzpCriticalLineZetaAngularVelocity
  rw [cfzpComplexAngularVelocity_eq_cartesian,
    cfzpCriticalLineZeta_re_deriv, cfzpCriticalLineZeta_im_deriv]

/-! ## D. Zeta logarithmic-derivative surface -/

/-- The zeta angular velocity equals `Re (ζ' / ζ)` away from zeta zeros. -/
theorem cfzpCriticalLineZetaAngularVelocity_eq_zetaLogDeriv_re
    (t : ℝ) (hzeta : riemannZeta (cfzpCriticalLinePoint t) ≠ 0) :
    cfzpCriticalLineZetaAngularVelocity t =
      (deriv riemannZeta (cfzpCriticalLinePoint t) /
        riemannZeta (cfzpCriticalLinePoint t)).re := by
  unfold cfzpCriticalLineZetaAngularVelocity
  rw [cfzpComplexAngularVelocity_eq_div_im hzeta]
  unfold cfzpCriticalLineZetaComplexVelocity
  rw [mul_div_assoc]
  simp [Complex.mul_im]

/-- The named ordinary-zeta negative log derivative is the same observable. -/
theorem cfzpCriticalLineZetaAngularVelocity_eq_neg_ordinaryZetaNegLogDeriv_re
    (t : ℝ) (hzeta : riemannZeta (cfzpCriticalLinePoint t) ≠ 0) :
    cfzpCriticalLineZetaAngularVelocity t =
      -(pascalXiOrdinaryZetaNegLogDeriv
        (cfzpCriticalLinePoint t)).re := by
  rw [cfzpCriticalLineZetaAngularVelocity_eq_zetaLogDeriv_re t hzeta]
  unfold pascalXiOrdinaryZetaNegLogDeriv
  rw [neg_div]
  simp

/-! ## E. Completed-zeta balance frontier -/

/--
The remaining balance transports completed-zeta realness through a local
derivative and cancels the GammaR rate.  It remains a single technical
frontier rather than an additional angle or phase subdivision.
-/
inductive CfzpCriticalLineCompletedZetaAngularVelocityBalanceGap : Prop
  | noCompletedZetaRealPathDerivativeBalanceProvided

end DkMath.RH.CFBRCProjection
