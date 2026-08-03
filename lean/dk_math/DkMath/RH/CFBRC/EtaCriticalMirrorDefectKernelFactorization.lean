/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedDefectIntegral
import DkMath.RH.CFBRC.EtaCriticalMirrorWeightedTransport
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorDefectKernelFactorization"

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.RH.Weave.Analytic

/-- Continuous positive-real transport weight between `s` and its critical mirror. -/
noncomputable def etaCriticalMirrorContinuousWeight
    (s : ℂ) (x : ℝ) : ℂ :=
  (x : ℂ) ^ (((2 * centeredSigma s.re : ℝ) : ℂ))

/-- Real form of the continuous transport weight. -/
noncomputable def etaCriticalMirrorContinuousWeightR
    (s : ℂ) (x : ℝ) : ℝ :=
  x ^ (2 * centeredSigma s.re)

/-- On the positive real axis the continuous complex weight is a positive real number. -/
theorem etaCriticalMirrorContinuousWeight_eq_ofReal
    (s : ℂ) {x : ℝ} (hx : 0 < x) :
    etaCriticalMirrorContinuousWeight s x =
      (etaCriticalMirrorContinuousWeightR s x : ℂ) := by
  unfold etaCriticalMirrorContinuousWeight
  unfold etaCriticalMirrorContinuousWeightR
  exact (Complex.ofReal_cpow hx.le (2 * centeredSigma s.re)).symm

/-- The continuous transport weight is strictly positive on the positive real axis. -/
theorem etaCriticalMirrorContinuousWeightR_pos
    (s : ℂ) {x : ℝ} (hx : 0 < x) :
    0 < etaCriticalMirrorContinuousWeightR s x := by
  unfold etaCriticalMirrorContinuousWeightR
  exact Real.rpow_pos_of_pos hx _

/--
The eta-pair derivative kernel at the critical mirror is the original
oscillatory kernel multiplied by the exact continuous transport weight and by
the reflected coefficient.
-/
theorem etaPairIntegralKernel_criticalMirror_eq_weighted
    (s : ℂ) {x : ℝ} (hx : 0 < x) :
    etaPairIntegralKernel (criticalMirror s) x =
      criticalMirror s * etaCriticalMirrorContinuousWeight s x *
        (x : ℂ) ^ (-s - 1) := by
  have hbase : (x : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hx.ne'
  have hexp :
      -criticalMirror s - 1 =
        ((2 * centeredSigma s.re : ℝ) : ℂ) + (-s - 1) := by
    rw [neg_criticalMirror_eq_transportExponent_add_neg]
    ring
  unfold etaPairIntegralKernel
  unfold etaCriticalMirrorContinuousWeight
  rw [hexp, Complex.cpow_add _ _ hbase]
  ring

/-- Off-critical coefficient left after extracting the common oscillatory kernel. -/
noncomputable def etaCriticalMirrorDefectCoefficient
    (s : ℂ) (x : ℝ) : ℂ :=
  criticalMirror s * etaCriticalMirrorContinuousWeight s x - s

/--
Exact factorization of the continuous paired-defect kernel into an
`off-critical coefficient` and the common rotating kernel `x⁻ˢ⁻¹`.
-/
theorem etaCriticalMirrorDefectPairIntegralKernel_factor
    (s : ℂ) {x : ℝ} (hx : 0 < x) :
    etaCriticalMirrorDefectPairIntegralKernel s x =
      etaCriticalMirrorDefectCoefficient s x *
        (x : ℂ) ^ (-s - 1) := by
  unfold etaCriticalMirrorDefectPairIntegralKernel
  rw [etaPairIntegralKernel_criticalMirror_eq_weighted s hx]
  unfold etaCriticalMirrorDefectCoefficient
  unfold etaPairIntegralKernel
  ring

/-- Real coordinate of the off-critical coefficient. -/
theorem etaCriticalMirrorDefectCoefficient_re
    (s : ℂ) {x : ℝ} (hx : 0 < x) :
    (etaCriticalMirrorDefectCoefficient s x).re =
      (1 - s.re) * etaCriticalMirrorContinuousWeightR s x - s.re := by
  unfold etaCriticalMirrorDefectCoefficient
  rw [etaCriticalMirrorContinuousWeight_eq_ofReal s hx]
  simp [criticalMirror]

/-- Imaginary coordinate of the off-critical coefficient. -/
theorem etaCriticalMirrorDefectCoefficient_im
    (s : ℂ) {x : ℝ} (hx : 0 < x) :
    (etaCriticalMirrorDefectCoefficient s x).im =
      s.im * (etaCriticalMirrorContinuousWeightR s x - 1) := by
  unfold etaCriticalMirrorDefectCoefficient
  rw [etaCriticalMirrorContinuousWeight_eq_ofReal s hx]
  simp [criticalMirror]
  ring

/-- On the critical line the continuous defect coefficient vanishes identically. -/
theorem etaCriticalMirrorDefectCoefficient_eq_zero_of_re_eq_half
    {s : ℂ} (hre : s.re = (1 : ℝ) / 2)
    {x : ℝ} (hx : 0 < x) :
    etaCriticalMirrorDefectCoefficient s x = 0 := by
  have hcenter : centeredSigma s.re = 0 :=
    (centeredSigma_eq_zero_iff s.re).2 hre
  have hweight : etaCriticalMirrorContinuousWeight s x = 1 := by
    simp [etaCriticalMirrorContinuousWeight, hcenter]
  unfold etaCriticalMirrorDefectCoefficient
  rw [hweight]
  simp only [mul_one]
  exact (criticalMirror_eq_self_iff_re_eq_half s).2 hre |>.sub_self

/-- On the critical line the continuous paired-defect kernel vanishes pointwise. -/
theorem etaCriticalMirrorDefectPairIntegralKernel_eq_zero_of_re_eq_half
    {s : ℂ} (hre : s.re = (1 : ℝ) / 2)
    {x : ℝ} (hx : 0 < x) :
    etaCriticalMirrorDefectPairIntegralKernel s x = 0 := by
  rw [etaCriticalMirrorDefectPairIntegralKernel_factor s hx]
  rw [etaCriticalMirrorDefectCoefficient_eq_zero_of_re_eq_half hre hx]
  simp

end DkMath.RH.CFBRCProjection
