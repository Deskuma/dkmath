/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameEtaTailEulerHalf
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameNormalizedDominantTailLimit"

set_option linter.style.longLine false

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology
open DkMath.RH.Weave.Analytic

/-- The pair-left rotation times the ordinary eta kernel separates into radial and residual factors. -/
theorem etaPairBaseRotation_mul_etaRealKernel_factor
    (z : ℂ) (k : ℕ) {x : ℝ} (hx : 0 < x) :
    etaPairBaseRotation z k * etaRealKernel z x =
      (((x ^ (-z.re) : ℝ) : ℂ)) *
        etaPairResidualRotation z k x := by
  have hx0 : (x : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hx.ne'
  unfold etaPairBaseRotation etaRealKernel
  unfold etaPairResidualRotation etaPairResidualPhase
  rw [Complex.cpow_def_of_ne_zero hx0]
  rw [Real.rpow_def_of_pos hx]
  rw [Complex.ofReal_exp]
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  rw [← Complex.ofReal_log hx.le]
  rw [← Complex.re_add_im z]
  rw [Complex.I]
  simp
  ring

/-- The first unsigned sample of the tail beginning at `k + 1` is the next pair-left kernel value. -/
theorem etaUnsignedVector_two_mul_succ_eq_etaRealKernel_nextLeft
    (z : ℂ) (k : ℕ) :
    etaUnsignedVector z (2 * (k + 1)) =
      etaRealKernel z (etaPairFrameLeftEndpoint (k + 1)) := by
  symm
  simpa [etaPairFrameLeftEndpoint] using
    etaRealKernel_nat z (2 * (k + 1))

/-- Index-to-successor-endpoint ratio used by the existing successor-index normalization. -/
noncomputable def etaPairIndexToSuccessorEndpointRatio
    (k : ℕ) : ℝ :=
  (((k + 1 : ℕ) : ℝ)) /
    etaPairFrameLeftEndpoint (k + 1)

/-- The index-to-successor-endpoint ratio tends to `1/2`. -/
theorem etaPairIndexToSuccessorEndpointRatio_tendsto_half :
    Tendsto etaPairIndexToSuccessorEndpointRatio atTop
      (nhds ((1 : ℝ) / 2)) := by
  have hsmall0 :
      Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ))
        atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat 1
  have hsmall := hsmall0.comp tendsto_nat_succ_atTop
  have hden :
      Tendsto
        (fun k : ℕ => (2 : ℝ) + (1 : ℝ) / (((k + 1 : ℕ) : ℝ)))
        atTop (nhds 2) := by
    simpa using tendsto_const_nhds.add hsmall
  have hinv := hden.inv₀ (by norm_num : (2 : ℝ) ≠ 0)
  refine hinv.congr' (Eventually.of_forall fun k => ?_)
  unfold etaPairIndexToSuccessorEndpointRatio
  unfold etaPairFrameLeftEndpoint
  have hk : 0 < (((k + 1 : ℕ) : ℝ)) := by positivity
  change
    (((k + 1 : ℕ) : ℝ)) /
        (((2 * (k + 1) + 1 : ℕ) : ℝ)) =
      ((2 : ℝ) + (1 : ℝ) / (((k + 1 : ℕ) : ℝ)))⁻¹
  norm_num [Nat.cast_add, Nat.cast_mul]
  field_simp [hk.ne']
  ring

/-- Positive-base division law for real powers. -/
private theorem div_rpow_pos
    {a b r : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (a / b) ^ r = a ^ r / b ^ r := by
  rw [div_eq_mul_inv]
  rw [Real.mul_rpow ha.le (inv_nonneg.mpr hb.le)]
  rw [Real.inv_rpow hb.le]
  rw [← div_eq_mul_inv]

/-- The real scaling product is the rpow of the index-to-endpoint ratio. -/
theorem etaPairIndexScale_mul_successorRadial_eq_ratio_rpow
    (z : ℂ) (k : ℕ) :
    (((k + 1 : ℕ) : ℝ) ^ z.re) *
        (etaPairFrameLeftEndpoint (k + 1) ^ (-z.re)) =
      etaPairIndexToSuccessorEndpointRatio k ^ z.re := by
  have hk : 0 < (((k + 1 : ℕ) : ℝ)) := by positivity
  have hL : 0 < etaPairFrameLeftEndpoint (k + 1) :=
    etaPairFrameLeftEndpoint_pos (k + 1)
  calc
    (((k + 1 : ℕ) : ℝ) ^ z.re) *
        (etaPairFrameLeftEndpoint (k + 1) ^ (-z.re)) =
      (((k + 1 : ℕ) : ℝ) ^ z.re) /
        (etaPairFrameLeftEndpoint (k + 1) ^ z.re) := by
      rw [Real.rpow_neg hL.le]
      rw [div_eq_mul_inv]
    _ = etaPairIndexToSuccessorEndpointRatio k ^ z.re := by
      unfold etaPairIndexToSuccessorEndpointRatio
      exact (div_rpow_pos hk hL).symm

/-- Adjacent pair-frame phases tend to zero. -/
theorem etaPairFrameStepPhase_tendsto_zero
    (z : ℂ) :
    Tendsto (etaPairFrameStepPhase z) atTop (nhds 0) := by
  have hspan := etaPairFrameStepSpan_tendsto_zero z
  have hneg :
      Tendsto (fun k : ℕ => -etaPairFrameStepSpan z k)
        atTop (nhds 0) := by
    simpa using hspan.neg
  exact
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      hneg hspan
      (Eventually.of_forall fun k => by
        have habs :
            |etaPairFrameStepPhase z k| ≤ etaPairFrameStepSpan z k := by
          rw [abs_etaPairFrameStepPhase]
        exact (abs_le.mp habs).1)
      (Eventually.of_forall fun k => by
        have habs :
            |etaPairFrameStepPhase z k| ≤ etaPairFrameStepSpan z k := by
          rw [abs_etaPairFrameStepPhase]
        exact (abs_le.mp habs).2)

/-- At the next pair-left endpoint, the residual phase is exactly one frame step. -/
theorem etaPairResidualPhase_nextLeft
    (z : ℂ) (k : ℕ) :
    etaPairResidualPhase z k (etaPairFrameLeftEndpoint (k + 1)) =
      etaPairFrameStepPhase z k := by
  rfl

/-- The next-left residual rotations converge to the identity. -/
theorem etaPairResidualRotation_nextLeft_tendsto_one
    (z : ℂ) :
    Tendsto
      (fun k : ℕ =>
        etaPairResidualRotation z k
          (etaPairFrameLeftEndpoint (k + 1)))
      atTop (nhds 1) := by
  have hphase := etaPairFrameStepPhase_tendsto_zero z
  have hcast :
      Tendsto
        (fun k : ℕ =>
          (((-etaPairFrameStepPhase z k : ℝ)) : ℂ))
        atTop (nhds 0) := by
    have h := (Complex.continuous_ofReal.tendsto 0).comp hphase.neg
    simpa using h
  have hinner :
      Tendsto
        (fun k : ℕ =>
          Complex.I * (((-etaPairFrameStepPhase z k : ℝ)) : ℂ))
        atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hcast
  have hexp := (Complex.continuous_exp.tendsto 0).comp hinner
  simpa [etaPairResidualRotation, etaPairResidualPhase_nextLeft] using hexp

/-- The normalized half-endpoint main term of one rotated eta tail. -/
noncomputable def etaPairIndexNormalizedRotatedEulerHalfMain
    (z : ℂ) (k : ℕ) : ℂ :=
  ((((k + 1 : ℕ) : ℝ) ^ z.re : ℝ) : ℂ) *
    (etaPairBaseRotation z k *
      (((1 : ℂ) / 2) * etaUnsignedVector z (2 * (k + 1))))

/-- The normalized rotated Euler remainder. -/
noncomputable def etaPairIndexNormalizedRotatedEulerRemainder
    (z : ℂ) (k : ℕ) : ℂ :=
  ((((k + 1 : ℕ) : ℝ) ^ z.re : ℝ) : ℂ) *
    (etaPairBaseRotation z k *
      etaPairEulerRemainderTail (k + 1) z)

/-- The normalized complete rotated eta tail. -/
noncomputable def etaPairIndexNormalizedRotatedTail
    (z : ℂ) (k : ℕ) : ℂ :=
  ((((k + 1 : ℕ) : ℝ) ^ z.re : ℝ) : ℂ) *
    (etaPairBaseRotation z k * etaPairTail (k + 1) z)

/-- The complex normalized-tail constant associated with the successor-index scale. -/
noncomputable def etaPairIndexNormalizedTailConstant
    (z : ℂ) : ℂ :=
  ((1 : ℂ) / 2) *
    ((((1 : ℝ) / 2) ^ z.re : ℝ) : ℂ)

/-- Exact factorization of the normalized half-endpoint main term. -/
theorem etaPairIndexNormalizedRotatedEulerHalfMain_eq_ratio_mul_residual
    (z : ℂ) (k : ℕ) :
    etaPairIndexNormalizedRotatedEulerHalfMain z k =
      ((1 : ℂ) / 2) *
        (((etaPairIndexToSuccessorEndpointRatio k ^ z.re : ℝ) : ℂ)) *
          etaPairResidualRotation z k
            (etaPairFrameLeftEndpoint (k + 1)) := by
  have hL : 0 < etaPairFrameLeftEndpoint (k + 1) :=
    etaPairFrameLeftEndpoint_pos (k + 1)
  unfold etaPairIndexNormalizedRotatedEulerHalfMain
  rw [etaUnsignedVector_two_mul_succ_eq_etaRealKernel_nextLeft]
  rw [etaPairBaseRotation_mul_etaRealKernel_factor z k hL]
  have hscale := etaPairIndexScale_mul_successorRadial_eq_ratio_rpow z k
  push_cast
  rw [← hscale]
  ring

/-- The normalized half-endpoint main term converges to its explicit constant. -/
theorem etaPairIndexNormalizedRotatedEulerHalfMain_tendsto_constant
    (z : ℂ) :
    Tendsto
      (etaPairIndexNormalizedRotatedEulerHalfMain z)
      atTop (nhds (etaPairIndexNormalizedTailConstant z)) := by
  have hratio :=
    etaPairIndexToSuccessorEndpointRatio_tendsto_half.rpow_const
      (Or.inl (by norm_num : ((1 : ℝ) / 2) ≠ 0))
  have hratioC :
      Tendsto
        (fun k : ℕ =>
          (((etaPairIndexToSuccessorEndpointRatio k ^ z.re : ℝ) : ℂ)))
        atTop
        (nhds (((((1 : ℝ) / 2) ^ z.re : ℝ) : ℂ))) := by
    have h := (Complex.continuous_ofReal.tendsto
      (((1 : ℝ) / 2) ^ z.re)).comp hratio
    simpa using h
  have hres := etaPairResidualRotation_nextLeft_tendsto_one z
  have hprod := (tendsto_const_nhds.mul hratioC).mul hres
  refine hprod.congr' (Eventually.of_forall fun k => ?_)
  rw [etaPairIndexNormalizedRotatedEulerHalfMain_eq_ratio_mul_residual]
  rfl

/-- Real power audit for the normalized Euler remainder. -/
noncomputable def etaPairIndexNormalizedEulerRemainderPowerAudit
    (z : ℂ) (k : ℕ) : ℝ :=
  ((‖z‖ * ‖z + 1‖ / 2) / (z.re + 1)) *
    ((((k + 1 : ℕ) : ℝ)) ^ (-1 : ℝ))

/-- The normalized Euler remainder norm is bounded by the inverse-index audit. -/
theorem norm_etaPairIndexNormalizedRotatedEulerRemainder_le_audit
    {z : ℂ} (hzre : 0 < z.re) (k : ℕ) :
    ‖etaPairIndexNormalizedRotatedEulerRemainder z k‖ ≤
      etaPairIndexNormalizedEulerRemainderPowerAudit z k := by
  have hk : 0 < (((k + 1 : ℕ) : ℝ)) := by positivity
  have hrem :=
    norm_etaPairEulerRemainderTail_le hzre (K := k + 1) (by omega)
  have hscaleNonneg :
      0 ≤ (((k + 1 : ℕ) : ℝ) ^ z.re) :=
    (Real.rpow_pos_of_pos hk _).le
  have hpow :
      (((k + 1 : ℕ) : ℝ) ^ z.re) *
          (((k + 1 : ℕ) : ℝ) ^ (-z.re - 1)) =
        (((k + 1 : ℕ) : ℝ) ^ (-1 : ℝ)) := by
    calc
      (((k + 1 : ℕ) : ℝ) ^ z.re) *
          (((k + 1 : ℕ) : ℝ) ^ (-z.re - 1)) =
        (((k + 1 : ℕ) : ℝ) ^ (z.re + (-z.re - 1))) :=
          (Real.rpow_add hk _ _).symm
      _ = (((k + 1 : ℕ) : ℝ) ^ (-1 : ℝ)) := by
        congr 1
        ring
  unfold etaPairIndexNormalizedRotatedEulerRemainder
  rw [norm_mul, norm_mul, norm_etaPairBaseRotation, one_mul]
  simp only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hscaleNonneg]
  calc
    (((k + 1 : ℕ) : ℝ) ^ z.re) *
        ‖etaPairEulerRemainderTail (k + 1) z‖ ≤
      (((k + 1 : ℕ) : ℝ) ^ z.re) *
        ((‖z‖ * ‖z + 1‖ / 2) *
          ((((k + 1 : ℕ) : ℝ) ^ (-z.re - 1)) / (z.re + 1))) :=
      mul_le_mul_of_nonneg_left hrem hscaleNonneg
    _ = etaPairIndexNormalizedEulerRemainderPowerAudit z k := by
      unfold etaPairIndexNormalizedEulerRemainderPowerAudit
      rw [← hpow]
      field_simp [show z.re + 1 ≠ 0 by linarith]
      ring

/-- The inverse-index Euler remainder audit tends to zero. -/
theorem etaPairIndexNormalizedEulerRemainderPowerAudit_tendsto_zero
    (z : ℂ) :
    Tendsto
      (etaPairIndexNormalizedEulerRemainderPowerAudit z)
      atTop (nhds 0) := by
  have hcast :
      Tendsto (fun k : ℕ => (((k + 1 : ℕ) : ℝ))) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_nat_succ_atTop
  have hinv :
      Tendsto
        (fun k : ℕ => (((k + 1 : ℕ) : ℝ) ^ (-1 : ℝ)))
        atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop zero_lt_one).comp hcast
  unfold etaPairIndexNormalizedEulerRemainderPowerAudit
  simpa using tendsto_const_nhds.mul hinv

/-- The normalized rotated Euler remainder converges to zero. -/
theorem etaPairIndexNormalizedRotatedEulerRemainder_tendsto_zero
    {z : ℂ} (hzre : 0 < z.re) :
    Tendsto
      (etaPairIndexNormalizedRotatedEulerRemainder z)
      atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hupper := etaPairIndexNormalizedEulerRemainderPowerAudit_tendsto_zero z
  exact
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hupper
      (Eventually.of_forall fun k => norm_nonneg _)
      (Eventually.of_forall fun k =>
        norm_etaPairIndexNormalizedRotatedEulerRemainder_le_audit hzre k)

/-- Exact normalized split of the complete rotated eta tail. -/
theorem etaPairIndexNormalizedRotatedTail_eq_main_add_remainder
    {z : ℂ} (hzre : 0 < z.re) (k : ℕ) :
    etaPairIndexNormalizedRotatedTail z k =
      etaPairIndexNormalizedRotatedEulerHalfMain z k +
        etaPairIndexNormalizedRotatedEulerRemainder z k := by
  unfold etaPairIndexNormalizedRotatedTail
  unfold etaPairIndexNormalizedRotatedEulerHalfMain
  unfold etaPairIndexNormalizedRotatedEulerRemainder
  rw [etaPairTail_eq_half_endpoint_add_eulerRemainderTail hzre]
  ring

/-- Every index-normalized rotated eta tail has the explicit Euler half constant. -/
theorem etaPairIndexNormalizedRotatedTail_tendsto_constant
    {z : ℂ} (hzre : 0 < z.re) :
    Tendsto
      (etaPairIndexNormalizedRotatedTail z)
      atTop (nhds (etaPairIndexNormalizedTailConstant z)) := by
  have hmain := etaPairIndexNormalizedRotatedEulerHalfMain_tendsto_constant z
  have hrem := etaPairIndexNormalizedRotatedEulerRemainder_tendsto_zero hzre
  refine (hmain.add hrem).congr' (Eventually.of_forall fun k => ?_)
  exact (etaPairIndexNormalizedRotatedTail_eq_main_add_remainder hzre k).symm

/-- The right-side normalized rotated mirror tail converges to its positive Euler constant. -/
theorem etaCriticalMirrorRightIndexNormalizedRotatedMirrorTail_tendsto_constant
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) :
    Tendsto
      (fun k : ℕ =>
        (((((k + 1 : ℕ) : ℝ)) ^ (criticalMirror s).re : ℝ) : ℂ) *
          etaCriticalMirrorPairFrameRotatedMirrorTail s k)
      atTop
      (nhds (etaPairIndexNormalizedTailConstant (criticalMirror s))) := by
  have h :=
    etaPairIndexNormalizedRotatedTail_tendsto_constant
      (criticalMirror_re_pos_of_nontrivialRiemannZetaZero hs)
  simpa [etaPairIndexNormalizedRotatedTail,
    etaCriticalMirrorPairFrameRotatedMirrorTail] using h

/-- The left-side normalized rotated original tail converges to its positive Euler constant. -/
theorem etaCriticalMirrorLeftIndexNormalizedRotatedOriginalTail_tendsto_constant
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) :
    Tendsto
      (fun k : ℕ =>
        (((((k + 1 : ℕ) : ℝ)) ^ s.re : ℝ) : ℂ) *
          etaCriticalMirrorPairFrameRotatedOriginalTail s k)
      atTop
      (nhds (etaPairIndexNormalizedTailConstant s)) := by
  have h :=
    etaPairIndexNormalizedRotatedTail_tendsto_constant
      (nontrivialRiemannZetaZero_re_pos hs)
  simpa [etaPairIndexNormalizedRotatedTail,
    etaCriticalMirrorPairFrameRotatedOriginalTail] using h

/-- Right normalized defect-minus-mirror complex remainder vanishes. -/
theorem etaCriticalMirrorRightIndexNormalizedRotatedDefectSubMirror_tendsto_zero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (hre : (1 : ℝ) / 2 < s.re) :
    Tendsto
      (fun k : ℕ =>
        (((((k + 1 : ℕ) : ℝ)) ^ (criticalMirror s).re : ℝ) : ℂ) *
          (etaCriticalMirrorPairFrameRotatedDefectTail s k -
            etaCriticalMirrorPairFrameRotatedMirrorTail s k))
      atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa [norm_mul, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg _ _)] using
    etaCriticalMirrorRightIndexNormalizedRotatedDefectSubMirror_norm_tendsto_zero
      hs hre

/-- Left normalized defect-plus-original complex remainder vanishes. -/
theorem etaCriticalMirrorLeftIndexNormalizedRotatedDefectAddOriginal_tendsto_zero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (hre : s.re < (1 : ℝ) / 2) :
    Tendsto
      (fun k : ℕ =>
        (((((k + 1 : ℕ) : ℝ)) ^ s.re : ℝ) : ℂ) *
          (etaCriticalMirrorPairFrameRotatedDefectTail s k +
            etaCriticalMirrorPairFrameRotatedOriginalTail s k))
      atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa [norm_mul, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg _ _)] using
    etaCriticalMirrorLeftIndexNormalizedRotatedDefectAddOriginal_norm_tendsto_zero
      hs hre

/-- Right of the critical line, the normalized rotated defect tail has a positive explicit limit. -/
theorem etaCriticalMirrorRightIndexNormalizedRotatedDefectTail_tendsto_constant
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (hre : (1 : ℝ) / 2 < s.re) :
    Tendsto
      (fun k : ℕ =>
        (((((k + 1 : ℕ) : ℝ)) ^ (criticalMirror s).re : ℝ) : ℂ) *
          etaCriticalMirrorPairFrameRotatedDefectTail s k)
      atTop
      (nhds (etaPairIndexNormalizedTailConstant (criticalMirror s))) := by
  have hmain :=
    etaCriticalMirrorRightIndexNormalizedRotatedMirrorTail_tendsto_constant hs
  have hrem :=
    etaCriticalMirrorRightIndexNormalizedRotatedDefectSubMirror_tendsto_zero hs hre
  refine (hmain.add hrem).congr' (Eventually.of_forall fun k => ?_)
  ring

/-- Left of the critical line, the normalized rotated defect tail has the negative explicit limit. -/
theorem etaCriticalMirrorLeftIndexNormalizedRotatedDefectTail_tendsto_neg_constant
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (hre : s.re < (1 : ℝ) / 2) :
    Tendsto
      (fun k : ℕ =>
        (((((k + 1 : ℕ) : ℝ)) ^ s.re : ℝ) : ℂ) *
          etaCriticalMirrorPairFrameRotatedDefectTail s k)
      atTop
      (nhds (-etaPairIndexNormalizedTailConstant s)) := by
  have hmain :=
    (etaCriticalMirrorLeftIndexNormalizedRotatedOriginalTail_tendsto_constant hs).neg
  have hrem :=
    etaCriticalMirrorLeftIndexNormalizedRotatedDefectAddOriginal_tendsto_zero hs hre
  refine (hmain.add hrem).congr' (Eventually.of_forall fun k => ?_)
  ring

end DkMath.RH.CFBRCProjection
