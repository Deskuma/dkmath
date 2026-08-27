/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameNormalizedDominantTailLimit
import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameSineTransportSignAudit
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameNormalizedSineTransportTermLimit"

set_option linter.style.longLine false

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology
open DkMath.RH.Weave.Analytic

/-- Adjacent-frame logarithmic increment scaled by the successor pair index. -/
noncomputable def etaPairFrameScaledLogStep
    (k : ℕ) : ℝ :=
  (((k + 1 : ℕ) : ℝ)) *
    (Real.log (etaPairFrameLeftEndpoint (k + 1)) -
      Real.log (etaPairFrameLeftEndpoint k))

/-- Elementary upper audit for the scaled adjacent-frame logarithmic step. -/
noncomputable def etaPairFrameScaledLogStepUpperAudit
    (k : ℕ) : ℝ :=
  2 * (((k + 1 : ℕ) : ℝ)) /
    etaPairFrameLeftEndpoint k

/-- The scaled logarithmic increment is at least one. -/
theorem one_le_etaPairFrameScaledLogStep
    (k : ℕ) :
    1 ≤ etaPairFrameScaledLogStep k := by
  let a : ℝ := etaPairFrameLeftEndpoint k
  let b : ℝ := etaPairFrameLeftEndpoint (k + 1)
  let q : ℝ := (((k + 1 : ℕ) : ℝ))
  have ha : 0 < a := by
    dsimp [a]
    exact etaPairFrameLeftEndpoint_pos k
  have hb : 0 < b := by
    dsimp [b]
    exact etaPairFrameLeftEndpoint_pos (k + 1)
  have hq : 0 < q := by
    dsimp [q]
    positivity
  have hstep : b = a + 2 := by
    dsimp [a, b, etaPairFrameLeftEndpoint]
    norm_num
    ring
  have hx : 0 ≤ 2 / a := by positivity
  have hlow := Real.le_log_one_add_of_nonneg hx
  have hratio : 1 + 2 / a = b / a := by
    rw [hstep]
    field_simp [ha.ne']
  have hleft : 2 * (2 / a) / (2 / a + 2) = 1 / q := by
    dsimp [a, q, etaPairFrameLeftEndpoint]
    norm_num [Nat.cast_add, Nat.cast_mul]
    field_simp
    ring
  have hlog :
      1 / q ≤ Real.log b - Real.log a := by
    rw [← Real.log_div hb.ne' ha.ne']
    rw [← hratio]
    simpa [hleft] using hlow
  calc
    1 = q * (1 / q) := by field_simp [hq.ne']
    _ ≤ q * (Real.log b - Real.log a) :=
      mul_le_mul_of_nonneg_left hlog hq.le
    _ = etaPairFrameScaledLogStep k := by
      rfl

/-- The scaled logarithmic increment is bounded by its rational audit. -/
theorem etaPairFrameScaledLogStep_le_upperAudit
    (k : ℕ) :
    etaPairFrameScaledLogStep k ≤
      etaPairFrameScaledLogStepUpperAudit k := by
  let a : ℝ := etaPairFrameLeftEndpoint k
  let b : ℝ := etaPairFrameLeftEndpoint (k + 1)
  let q : ℝ := (((k + 1 : ℕ) : ℝ))
  have ha : 0 < a := by
    dsimp [a]
    exact etaPairFrameLeftEndpoint_pos k
  have hb : 0 < b := by
    dsimp [b]
    exact etaPairFrameLeftEndpoint_pos (k + 1)
  have hq : 0 ≤ q := by
    dsimp [q]
    positivity
  have hstep : b = a + 2 := by
    dsimp [a, b, etaPairFrameLeftEndpoint]
    norm_num
    ring
  have hlog0 := Real.log_le_sub_one_of_pos (div_pos hb ha)
  have hratio : b / a - 1 = 2 / a := by
    rw [hstep]
    field_simp [ha.ne']
    ring
  have hlog : Real.log b - Real.log a ≤ 2 / a := by
    rw [← Real.log_div hb.ne' ha.ne']
    simpa [hratio] using hlog0
  unfold etaPairFrameScaledLogStep
  unfold etaPairFrameScaledLogStepUpperAudit
  change q * (Real.log b - Real.log a) ≤ 2 * q / a
  calc
    q * (Real.log b - Real.log a) ≤ q * (2 / a) :=
      mul_le_mul_of_nonneg_left hlog hq
    _ = 2 * q / a := by ring

/-- The rational upper audit tends to one. -/
theorem etaPairFrameScaledLogStepUpperAudit_tendsto_one :
    Tendsto etaPairFrameScaledLogStepUpperAudit atTop (nhds 1) := by
  have hsmall :
      Tendsto
        (fun k : ℕ =>
          (1 : ℝ) / etaPairFrameLeftEndpoint k)
        atTop (nhds 0) := by
    have h :=
      (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp
        tendsto_two_mul_add_one_atTop
    convert h using 1
    funext k
    norm_num [etaPairFrameLeftEndpoint, Function.comp_apply,
      Nat.cast_add, Nat.cast_mul]
  have hsum :
      Tendsto
        (fun k : ℕ =>
          1 + (1 : ℝ) / etaPairFrameLeftEndpoint k)
        atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add hsmall
  refine hsum.congr' (Eventually.of_forall fun k => ?_)
  unfold etaPairFrameScaledLogStepUpperAudit
  unfold etaPairFrameLeftEndpoint
  have hk : 0 < (((2 * k + 1 : ℕ) : ℝ)) := by positivity
  norm_num [Nat.cast_add, Nat.cast_mul]
  field_simp [hk.ne']
  ring

/-- The successor-index scaled adjacent logarithmic step tends to one. -/
theorem etaPairFrameScaledLogStep_tendsto_one :
    Tendsto etaPairFrameScaledLogStep atTop (nhds 1) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds
    etaPairFrameScaledLogStepUpperAudit_tendsto_one
    (Eventually.of_forall one_le_etaPairFrameScaledLogStep)
    (Eventually.of_forall etaPairFrameScaledLogStep_le_upperAudit)

/-- Adjacent-frame phase scaled by the successor pair index. -/
noncomputable def etaPairFrameScaledStepPhase
    (s : ℂ) (k : ℕ) : ℝ :=
  (((k + 1 : ℕ) : ℝ)) * etaPairFrameStepPhase s k

/-- The scaled adjacent-frame phase tends to the imaginary coordinate. -/
theorem etaPairFrameScaledStepPhase_tendsto_im
    (s : ℂ) :
    Tendsto (etaPairFrameScaledStepPhase s) atTop (nhds s.im) := by
  have h :=
    (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => s.im) atTop (nhds s.im)).mul
      etaPairFrameScaledLogStep_tendsto_one
  have h' :
      Tendsto
        (fun k : ℕ => s.im * etaPairFrameScaledLogStep k)
        atTop (nhds s.im) := by
    simpa [Function.comp_def] using h
  refine h'.congr' (Eventually.of_forall fun k => ?_)
  unfold etaPairFrameScaledStepPhase
  unfold etaPairFrameScaledLogStep
  unfold etaPairFrameStepPhase
  ring

/-- Universal identity expressing sine through the continuous sinc function. -/
theorem sin_eq_mul_sinc
    (x : ℝ) :
    Real.sin x = x * Real.sinc x := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [Real.sinc_of_ne_zero hx]
    field_simp [hx]

/-- Sine-transport coefficient scaled by the successor pair index. -/
noncomputable def etaCriticalMirrorPairedFrameScaledSineTransportCoefficient
    (s : ℂ) (k : ℕ) : ℝ :=
  (((k + 1 : ℕ) : ℝ)) *
    etaCriticalMirrorPairedFrameSineTransportCoefficient s k

/-- Exact sinc factorization of the scaled sine-transport coefficient. -/
theorem etaCriticalMirrorPairedFrameScaledSineTransportCoefficient_eq
    (s : ℂ) (k : ℕ) :
    etaCriticalMirrorPairedFrameScaledSineTransportCoefficient s k =
      s.im * etaPairFrameScaledStepPhase s k *
        Real.sinc (etaPairFrameStepPhase s k) := by
  unfold etaCriticalMirrorPairedFrameScaledSineTransportCoefficient
  unfold etaCriticalMirrorPairedFrameSineTransportCoefficient
  rw [sin_eq_mul_sinc]
  unfold etaPairFrameScaledStepPhase
  ring

/-- The scaled sine-transport coefficient tends to the square of the height. -/
theorem etaCriticalMirrorPairedFrameScaledSineTransportCoefficient_tendsto_sq
    (s : ℂ) :
    Tendsto
      (etaCriticalMirrorPairedFrameScaledSineTransportCoefficient s)
      atTop (nhds (s.im ^ 2)) := by
  have hphase := etaPairFrameScaledStepPhase_tendsto_im s
  have hstep0 := etaPairFrameStepPhase_tendsto_zero s
  have hsinc :
      Tendsto
        (fun k : ℕ => Real.sinc (etaPairFrameStepPhase s k))
        atTop (nhds 1) := by
    have h := (Real.continuous_sinc.tendsto 0).comp hstep0
    simpa [Function.comp_def] using h
  have hprod :=
    (((tendsto_const_nhds :
      Tendsto (fun _ : ℕ => s.im) atTop (nhds s.im)).mul hphase).mul hsinc)
  have hlimit :
      Tendsto
        (fun k : ℕ =>
          s.im * etaPairFrameScaledStepPhase s k *
            Real.sinc (etaPairFrameStepPhase s k))
        atTop (nhds (s.im ^ 2)) := by
    simpa [pow_two] using hprod
  convert hlimit using 1
  funext k
  exact etaCriticalMirrorPairedFrameScaledSineTransportCoefficient_eq s k

/-- Real form of the explicit normalized eta-tail constant. -/
noncomputable def etaPairIndexNormalizedTailConstantReal
    (z : ℂ) : ℝ :=
  ((1 : ℝ) / 2) * (((1 : ℝ) / 2) ^ z.re)

/-- The complex normalized-tail constant is the real embedding of its real form. -/
theorem etaPairIndexNormalizedTailConstant_eq_real
    (z : ℂ) :
    etaPairIndexNormalizedTailConstant z =
      ((etaPairIndexNormalizedTailConstantReal z : ℝ) : ℂ) := by
  unfold etaPairIndexNormalizedTailConstant
  unfold etaPairIndexNormalizedTailConstantReal
  push_cast
  ring

/-- The real normalized-tail constant is strictly positive. -/
theorem etaPairIndexNormalizedTailConstantReal_pos
    (z : ℂ) :
    0 < etaPairIndexNormalizedTailConstantReal z := by
  unfold etaPairIndexNormalizedTailConstantReal
  exact mul_pos (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _)

/-- Right-side normalized rotated defect-tail real part tends to its positive constant. -/
theorem etaCriticalMirrorRightIndexNormalizedRotatedDefectTail_re_tendsto_constant
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (hre : (1 : ℝ) / 2 < s.re) :
    Tendsto
      (fun k : ℕ =>
        (((k + 1 : ℕ) : ℝ) ^ (criticalMirror s).re) *
          (etaCriticalMirrorPairFrameRotatedDefectTail s k).re)
      atTop
      (nhds (etaPairIndexNormalizedTailConstantReal (criticalMirror s))) := by
  have hcomplex :=
    etaCriticalMirrorRightIndexNormalizedRotatedDefectTail_tendsto_constant hs hre
  have hreal :=
    (Complex.continuous_re.tendsto
      (etaPairIndexNormalizedTailConstant (criticalMirror s))).comp hcomplex
  simpa [etaPairIndexNormalizedTailConstant_eq_real, Function.comp_def] using hreal

/-- Left-side normalized rotated defect-tail real part tends to the negative constant. -/
theorem etaCriticalMirrorLeftIndexNormalizedRotatedDefectTail_re_tendsto_neg_constant
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (hre : s.re < (1 : ℝ) / 2) :
    Tendsto
      (fun k : ℕ =>
        (((k + 1 : ℕ) : ℝ) ^ s.re) *
          (etaCriticalMirrorPairFrameRotatedDefectTail s k).re)
      atTop
      (nhds (-etaPairIndexNormalizedTailConstantReal s)) := by
  have hcomplex :=
    etaCriticalMirrorLeftIndexNormalizedRotatedDefectTail_tendsto_neg_constant hs hre
  have hreal :=
    (Complex.continuous_re.tendsto
      (-etaPairIndexNormalizedTailConstant s)).comp hcomplex
  simpa [etaPairIndexNormalizedTailConstant_eq_real, Function.comp_def] using hreal

/-- Right-side normalized sine-transport term constant. -/
noncomputable def etaCriticalMirrorRightNormalizedSineTransportTermConstant
    (s : ℂ) : ℝ :=
  -(s.im ^ 2 *
    etaPairIndexNormalizedTailConstantReal (criticalMirror s))

/-- Left-side normalized sine-transport term constant. -/
noncomputable def etaCriticalMirrorLeftNormalizedSineTransportTermConstant
    (s : ℂ) : ℝ :=
  s.im ^ 2 * etaPairIndexNormalizedTailConstantReal s

/-- Exact factorization of a right-normalized sine-transport term. -/
theorem etaCriticalMirrorRightNormalizedSineTransportTerm_eq
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (k : ℕ) :
    (((k + 1 : ℕ) : ℝ) ^ ((criticalMirror s).re + 1)) *
        etaCriticalMirrorPairedFrameCorrectionSineTransportTerm s k =
      -(etaCriticalMirrorPairedFrameScaledSineTransportCoefficient s k *
        ((((k + 1 : ℕ) : ℝ) ^ (criticalMirror s).re) *
          (etaCriticalMirrorPairFrameRotatedDefectTail s k).re)) := by
  have hk : 0 < (((k + 1 : ℕ) : ℝ)) := by positivity
  rw [etaCriticalMirrorPairedFrameCorrectionSineTransportTerm_eq_neg_coefficient_mul_rotatedDefectTail_re
    hs him k]
  unfold etaCriticalMirrorPairedFrameScaledSineTransportCoefficient
  rw [Real.rpow_add hk]
  rw [Real.rpow_one]
  ring

/-- Exact factorization of a left-normalized sine-transport term. -/
theorem etaCriticalMirrorLeftNormalizedSineTransportTerm_eq
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (k : ℕ) :
    (((k + 1 : ℕ) : ℝ) ^ (s.re + 1)) *
        etaCriticalMirrorPairedFrameCorrectionSineTransportTerm s k =
      -(etaCriticalMirrorPairedFrameScaledSineTransportCoefficient s k *
        ((((k + 1 : ℕ) : ℝ) ^ s.re) *
          (etaCriticalMirrorPairFrameRotatedDefectTail s k).re)) := by
  have hk : 0 < (((k + 1 : ℕ) : ℝ)) := by positivity
  rw [etaCriticalMirrorPairedFrameCorrectionSineTransportTerm_eq_neg_coefficient_mul_rotatedDefectTail_re
    hs him k]
  unfold etaCriticalMirrorPairedFrameScaledSineTransportCoefficient
  rw [Real.rpow_add hk]
  rw [Real.rpow_one]
  ring

/-- Right of the critical line, normalized sine-transport terms have a negative explicit limit. -/
theorem etaCriticalMirrorRightNormalizedSineTransportTerm_tendsto_constant
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re) :
    Tendsto
      (fun k : ℕ =>
        (((k + 1 : ℕ) : ℝ) ^ ((criticalMirror s).re + 1)) *
          etaCriticalMirrorPairedFrameCorrectionSineTransportTerm s k)
      atTop
      (nhds (etaCriticalMirrorRightNormalizedSineTransportTermConstant s)) := by
  have hcoeff :=
    etaCriticalMirrorPairedFrameScaledSineTransportCoefficient_tendsto_sq s
  have htail :=
    etaCriticalMirrorRightIndexNormalizedRotatedDefectTail_re_tendsto_constant
      hs hre
  have hprod := (hcoeff.mul htail).neg
  refine hprod.congr' (Eventually.of_forall fun k => ?_)
  simp only
  rw [etaCriticalMirrorRightNormalizedSineTransportTerm_eq hs him k]

/-- Left of the critical line, normalized sine-transport terms have a positive explicit limit. -/
theorem etaCriticalMirrorLeftNormalizedSineTransportTerm_tendsto_constant
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2) :
    Tendsto
      (fun k : ℕ =>
        (((k + 1 : ℕ) : ℝ) ^ (s.re + 1)) *
          etaCriticalMirrorPairedFrameCorrectionSineTransportTerm s k)
      atTop
      (nhds (etaCriticalMirrorLeftNormalizedSineTransportTermConstant s)) := by
  have hcoeff :=
    etaCriticalMirrorPairedFrameScaledSineTransportCoefficient_tendsto_sq s
  have htail :=
    etaCriticalMirrorLeftIndexNormalizedRotatedDefectTail_re_tendsto_neg_constant
      hs hre
  have hprod := (hcoeff.mul htail).neg
  have hlimit :
      Tendsto
        (fun k : ℕ =>
          -(etaCriticalMirrorPairedFrameScaledSineTransportCoefficient s k *
            ((((k + 1 : ℕ) : ℝ) ^ s.re) *
              (etaCriticalMirrorPairFrameRotatedDefectTail s k).re)))
        atTop
        (nhds (etaCriticalMirrorLeftNormalizedSineTransportTermConstant s)) := by
    simpa [etaCriticalMirrorLeftNormalizedSineTransportTermConstant] using hprod
  refine hlimit.congr' (Eventually.of_forall fun k => ?_)
  simp only
  rw [etaCriticalMirrorLeftNormalizedSineTransportTerm_eq hs him k]

end DkMath.RH.CFBRCProjection
