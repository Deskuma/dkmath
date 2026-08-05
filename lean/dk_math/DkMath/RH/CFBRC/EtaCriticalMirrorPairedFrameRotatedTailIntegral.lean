/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameRotatedDefectTailSplit
import DkMath.RH.CFBRC.EtaCriticalMirrorDefectKernelEventualSign
import DkMath.RH.Weave.Analytic.EtaPairIntegral
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameRotatedTailIntegral"

set_option linter.style.longLine false

noncomputable section

namespace DkMath.RH.CFBRCProjection

open MeasureTheory
open DkMath.RH.Weave.Analytic

/-- The critical mirror uses the same pair-left base rotation because it preserves `im`. -/
@[simp] theorem etaPairBaseRotation_criticalMirror
    (s : ℂ) (k : ℕ) :
    etaPairBaseRotation (criticalMirror s) k =
      etaPairBaseRotation s k := by
  unfold etaPairBaseRotation
  simp

/-- The critical mirror has the same pair-local residual phase. -/
@[simp] theorem etaPairResidualPhase_criticalMirror
    (s : ℂ) (k : ℕ) (x : ℝ) :
    etaPairResidualPhase (criticalMirror s) k x =
      etaPairResidualPhase s k x := by
  unfold etaPairResidualPhase
  simp

/-- The critical mirror has the same pair-local residual rotation. -/
@[simp] theorem etaPairResidualRotation_criticalMirror
    (s : ℂ) (k : ℕ) (x : ℝ) :
    etaPairResidualRotation (criticalMirror s) k x =
      etaPairResidualRotation s k x := by
  unfold etaPairResidualRotation
  simp

/--
A single eta integral kernel in its own pair-left frame is a positive radial
factor times the fixed coefficient and the local residual rotation.
-/
theorem etaPairBaseRotation_mul_etaPairIntegralKernel_factor
    (z : ℂ) (k : ℕ) {x : ℝ} (hx : 0 < x) :
    etaPairBaseRotation z k * etaPairIntegralKernel z x =
      ((etaPairRadialDecay z x : ℝ) : ℂ) *
        (z * etaPairResidualRotation z k x) := by
  unfold etaPairIntegralKernel
  calc
    etaPairBaseRotation z k *
          (z * (x : ℂ) ^ (-z - 1)) =
        z *
          (etaPairBaseRotation z k *
            (x : ℂ) ^ (-z - 1)) := by
      ring
    _ = z *
          (((etaPairRadialDecay z x : ℝ) : ℂ) *
            etaPairResidualRotation z k x) := by
      rw [etaPairBaseRotation_mul_cpow_eq_radial_mul_residual z k hx]
    _ = ((etaPairRadialDecay z x : ℝ) : ℂ) *
          (z * etaPairResidualRotation z k x) := by
      ring

/-- Original eta kernel factorization in the current `s` pair-left frame. -/
theorem etaPairBaseRotation_mul_originalEtaPairIntegralKernel_factor
    (s : ℂ) (k : ℕ) {x : ℝ} (hx : 0 < x) :
    etaPairBaseRotation s k * etaPairIntegralKernel s x =
      ((etaPairRadialDecay s x : ℝ) : ℂ) *
        (s * etaPairResidualRotation s k x) :=
  etaPairBaseRotation_mul_etaPairIntegralKernel_factor s k hx

/-- Mirror eta kernel factorization in the same current `s` pair-left frame. -/
theorem etaPairBaseRotation_mul_mirrorEtaPairIntegralKernel_factor
    (s : ℂ) (k : ℕ) {x : ℝ} (hx : 0 < x) :
    etaPairBaseRotation s k *
        etaPairIntegralKernel (criticalMirror s) x =
      ((etaPairRadialDecay (criticalMirror s) x : ℝ) : ℂ) *
        (criticalMirror s * etaPairResidualRotation s k x) := by
  simpa using
    (etaPairBaseRotation_mul_etaPairIntegralKernel_factor
      (criticalMirror s) k hx)

/-- Real-part form of the original single-kernel factorization. -/
theorem etaPairBaseRotation_mul_originalEtaPairIntegralKernel_re
    (s : ℂ) (k : ℕ) {x : ℝ} (hx : 0 < x) :
    (etaPairBaseRotation s k * etaPairIntegralKernel s x).re =
      etaPairRadialDecay s x *
        (s * etaPairResidualRotation s k x).re := by
  rw [etaPairBaseRotation_mul_originalEtaPairIntegralKernel_factor s k hx]
  simp

/-- Real-part form of the mirror single-kernel factorization. -/
theorem etaPairBaseRotation_mul_mirrorEtaPairIntegralKernel_re
    (s : ℂ) (k : ℕ) {x : ℝ} (hx : 0 < x) :
    (etaPairBaseRotation s k *
        etaPairIntegralKernel (criticalMirror s) x).re =
      etaPairRadialDecay (criticalMirror s) x *
        (criticalMirror s * etaPairResidualRotation s k x).re := by
  rw [etaPairBaseRotation_mul_mirrorEtaPairIntegralKernel_factor s k hx]
  simp

/-- A fixed pair-left rotation can be moved inside any single eta-pair integral. -/
theorem etaPairBaseRotation_mul_singleEtaPairTerm_eq_intervalIntegral
    {z : ℂ} (hz : z ≠ 0) (s : ℂ) (k j : ℕ) :
    etaPairBaseRotation s k * etaPairTerm z j =
      ∫ x : ℝ in
          (etaPairFrameLeftEndpoint j)..(etaPairFrameRightEndpoint j),
        etaPairBaseRotation s k * etaPairIntegralKernel z x := by
  rw [etaPairTerm_eq_intervalIntegral hz j]
  change
    etaPairBaseRotation s k *
        (∫ x : ℝ in
            (etaPairFrameLeftEndpoint j)..(etaPairFrameRightEndpoint j),
          etaPairIntegralKernel z x) = _
  rw [intervalIntegral.integral_const_mul]

/-- One original-tail interval term, all viewed in the initial pair-left frame `k`. -/
noncomputable def etaCriticalMirrorPairFrameRotatedOriginalTailIntegralTerm
    (s : ℂ) (k j : ℕ) : ℂ :=
  ∫ x : ℝ in
      (etaPairFrameLeftEndpoint (j + (k + 1)))..
        (etaPairFrameRightEndpoint (j + (k + 1))),
    etaPairBaseRotation s k * etaPairIntegralKernel s x

/-- One mirror-tail interval term, all viewed in the initial pair-left frame `k`. -/
noncomputable def etaCriticalMirrorPairFrameRotatedMirrorTailIntegralTerm
    (s : ℂ) (k j : ℕ) : ℂ :=
  ∫ x : ℝ in
      (etaPairFrameLeftEndpoint (j + (k + 1)))..
        (etaPairFrameRightEndpoint (j + (k + 1))),
    etaPairBaseRotation s k *
      etaPairIntegralKernel (criticalMirror s) x

/-- The original fixed-frame interval-term series is summable. -/
theorem summable_etaCriticalMirrorPairFrameRotatedOriginalTailIntegralTerm
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (k : ℕ) :
    Summable
      (etaCriticalMirrorPairFrameRotatedOriginalTailIntegralTerm s k) := by
  have hsum :=
    (summable_etaPairTail
      (nontrivialRiemannZetaZero_re_pos hs) (k + 1)).mul_left
        (etaPairBaseRotation s k)
  refine hsum.congr ?_
  intro j
  simpa [etaCriticalMirrorPairFrameRotatedOriginalTailIntegralTerm] using
    (etaPairBaseRotation_mul_singleEtaPairTerm_eq_intervalIntegral
      (nontrivialRiemannZetaZero_ne_zero hs) s k (j + (k + 1)))

/-- The mirror fixed-frame interval-term series is summable. -/
theorem summable_etaCriticalMirrorPairFrameRotatedMirrorTailIntegralTerm
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (k : ℕ) :
    Summable
      (etaCriticalMirrorPairFrameRotatedMirrorTailIntegralTerm s k) := by
  have hm := criticalMirror_nontrivialRiemannZetaZero hs
  have hsum :=
    (summable_etaPairTail
      (criticalMirror_re_pos_of_nontrivialRiemannZetaZero hs)
      (k + 1)).mul_left (etaPairBaseRotation s k)
  refine hsum.congr ?_
  intro j
  simpa [etaCriticalMirrorPairFrameRotatedMirrorTailIntegralTerm] using
    (etaPairBaseRotation_mul_singleEtaPairTerm_eq_intervalIntegral
      (nontrivialRiemannZetaZero_ne_zero hm) s k (j + (k + 1)))

/-- Exact infinite interval-integral representation of the rotated original tail. -/
theorem etaCriticalMirrorPairFrameRotatedOriginalTail_eq_tsum_intervalIntegral
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (k : ℕ) :
    etaCriticalMirrorPairFrameRotatedOriginalTail s k =
      ∑' j : ℕ,
        etaCriticalMirrorPairFrameRotatedOriginalTailIntegralTerm s k j := by
  have hsum :=
    summable_etaPairTail
      (nontrivialRiemannZetaZero_re_pos hs) (k + 1)
  have hfactor :
      (∑' j : ℕ,
        etaPairBaseRotation s k *
          etaPairTerm s (j + (k + 1))) =
        etaPairBaseRotation s k *
          (∑' j : ℕ, etaPairTerm s (j + (k + 1))) :=
    (hsum.hasSum.mul_left (etaPairBaseRotation s k)).tsum_eq
  unfold etaCriticalMirrorPairFrameRotatedOriginalTail etaPairTail
  calc
    etaPairBaseRotation s k *
        (∑' j : ℕ, etaPairTerm s (j + (k + 1))) =
      ∑' j : ℕ,
        etaPairBaseRotation s k *
          etaPairTerm s (j + (k + 1)) := hfactor.symm
    _ = ∑' j : ℕ,
        etaCriticalMirrorPairFrameRotatedOriginalTailIntegralTerm s k j := by
      apply tsum_congr
      intro j
      simpa [etaCriticalMirrorPairFrameRotatedOriginalTailIntegralTerm] using
        (etaPairBaseRotation_mul_singleEtaPairTerm_eq_intervalIntegral
          (nontrivialRiemannZetaZero_ne_zero hs)
          s k (j + (k + 1)))

/-- Exact infinite interval-integral representation of the rotated mirror tail. -/
theorem etaCriticalMirrorPairFrameRotatedMirrorTail_eq_tsum_intervalIntegral
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (k : ℕ) :
    etaCriticalMirrorPairFrameRotatedMirrorTail s k =
      ∑' j : ℕ,
        etaCriticalMirrorPairFrameRotatedMirrorTailIntegralTerm s k j := by
  have hm := criticalMirror_nontrivialRiemannZetaZero hs
  have hsum :=
    summable_etaPairTail
      (criticalMirror_re_pos_of_nontrivialRiemannZetaZero hs) (k + 1)
  have hfactor :
      (∑' j : ℕ,
        etaPairBaseRotation s k *
          etaPairTerm (criticalMirror s) (j + (k + 1))) =
        etaPairBaseRotation s k *
          (∑' j : ℕ,
            etaPairTerm (criticalMirror s) (j + (k + 1))) :=
    (hsum.hasSum.mul_left (etaPairBaseRotation s k)).tsum_eq
  unfold etaCriticalMirrorPairFrameRotatedMirrorTail etaPairTail
  calc
    etaPairBaseRotation s k *
        (∑' j : ℕ,
          etaPairTerm (criticalMirror s) (j + (k + 1))) =
      ∑' j : ℕ,
        etaPairBaseRotation s k *
          etaPairTerm (criticalMirror s) (j + (k + 1)) := hfactor.symm
    _ = ∑' j : ℕ,
        etaCriticalMirrorPairFrameRotatedMirrorTailIntegralTerm s k j := by
      apply tsum_congr
      intro j
      simpa [etaCriticalMirrorPairFrameRotatedMirrorTailIntegralTerm] using
        (etaPairBaseRotation_mul_singleEtaPairTerm_eq_intervalIntegral
          (nontrivialRiemannZetaZero_ne_zero hm)
          s k (j + (k + 1)))

/-- Real part of the rotated original tail is the sum of real interval terms. -/
theorem etaCriticalMirrorPairFrameRotatedOriginalTail_re_eq_tsum_intervalIntegral_re
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (k : ℕ) :
    (etaCriticalMirrorPairFrameRotatedOriginalTail s k).re =
      ∑' j : ℕ,
        (etaCriticalMirrorPairFrameRotatedOriginalTailIntegralTerm s k j).re := by
  rw [etaCriticalMirrorPairFrameRotatedOriginalTail_eq_tsum_intervalIntegral hs k]
  have hsum :=
    summable_etaCriticalMirrorPairFrameRotatedOriginalTailIntegralTerm hs k
  have hmap :=
    (hsum.hasSum.map Complex.reCLM Complex.reCLM.continuous).tsum_eq
  simpa using hmap.symm

/-- Real part of the rotated mirror tail is the sum of real interval terms. -/
theorem etaCriticalMirrorPairFrameRotatedMirrorTail_re_eq_tsum_intervalIntegral_re
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (k : ℕ) :
    (etaCriticalMirrorPairFrameRotatedMirrorTail s k).re =
      ∑' j : ℕ,
        (etaCriticalMirrorPairFrameRotatedMirrorTailIntegralTerm s k j).re := by
  rw [etaCriticalMirrorPairFrameRotatedMirrorTail_eq_tsum_intervalIntegral hs k]
  have hsum :=
    summable_etaCriticalMirrorPairFrameRotatedMirrorTailIntegralTerm hs k
  have hmap :=
    (hsum.hasSum.map Complex.reCLM Complex.reCLM.continuous).tsum_eq
  simpa using hmap.symm

end DkMath.RH.CFBRCProjection
