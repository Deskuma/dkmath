/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameRotatedDefectTailSplit

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameRotatedDefectTailSplit"

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter

example
    {z : ℂ} (hz : 0 < z.re)
    {K : ℕ} (hK : 1 ≤ K) :
    ‖etaPairTail K z‖ ≤
      ‖z‖ * (((K : ℝ) ^ (-z.re)) / z.re) :=
  norm_etaPairTail_le hz hK

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (k : ℕ) :
    etaCriticalMirrorPairFrameRotatedDefectTail s k =
      etaCriticalMirrorPairFrameRotatedMirrorTail s k -
        etaCriticalMirrorPairFrameRotatedOriginalTail s k :=
  etaCriticalMirrorPairFrameRotatedDefectTail_eq_mirror_sub_original hs k

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (k : ℕ) :
    (etaCriticalMirrorPairFrameRotatedDefectTail s k).re =
      (etaCriticalMirrorPairFrameRotatedMirrorTail s k).re -
        (etaCriticalMirrorPairFrameRotatedOriginalTail s k).re :=
  etaCriticalMirrorPairFrameRotatedDefectTail_re_eq_mirror_sub_original hs k

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (k : ℕ) :
    ‖etaCriticalMirrorPairFrameRotatedMirrorTail s k‖ ≤
      ‖criticalMirror s‖ *
        (((((k + 1 : ℕ) : ℝ)) ^ (-(criticalMirror s).re)) /
          (criticalMirror s).re) :=
  norm_etaCriticalMirrorPairFrameRotatedMirrorTail_le hs k

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (k : ℕ) :
    ‖etaCriticalMirrorPairFrameRotatedOriginalTail s k‖ ≤
      ‖s‖ *
        (((((k + 1 : ℕ) : ℝ)) ^ (-s.re)) / s.re) :=
  norm_etaCriticalMirrorPairFrameRotatedOriginalTail_le hs k

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (hre : (1 : ℝ) / 2 < s.re) :
    Tendsto
      (fun k : ℕ =>
        ((((k + 1 : ℕ) : ℝ)) ^ (criticalMirror s).re) *
          ‖etaCriticalMirrorPairFrameRotatedOriginalTail s k‖)
      atTop (nhds 0) :=
  etaCriticalMirrorRightIndexNormalizedRotatedOriginalTail_tendsto_zero
    hs hre

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (hre : s.re < (1 : ℝ) / 2) :
    Tendsto
      (fun k : ℕ =>
        ((((k + 1 : ℕ) : ℝ)) ^ s.re) *
          ‖etaCriticalMirrorPairFrameRotatedMirrorTail s k‖)
      atTop (nhds 0) :=
  etaCriticalMirrorLeftIndexNormalizedRotatedMirrorTail_tendsto_zero
    hs hre

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (hre : (1 : ℝ) / 2 < s.re) :
    Tendsto
      (fun k : ℕ =>
        ((((k + 1 : ℕ) : ℝ)) ^ (criticalMirror s).re) *
          ‖etaCriticalMirrorPairFrameRotatedDefectTail s k -
            etaCriticalMirrorPairFrameRotatedMirrorTail s k‖)
      atTop (nhds 0) :=
  etaCriticalMirrorRightIndexNormalizedRotatedDefectSubMirror_norm_tendsto_zero
    hs hre

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (hre : s.re < (1 : ℝ) / 2) :
    Tendsto
      (fun k : ℕ =>
        ((((k + 1 : ℕ) : ℝ)) ^ s.re) *
          ‖etaCriticalMirrorPairFrameRotatedDefectTail s k +
            etaCriticalMirrorPairFrameRotatedOriginalTail s k‖)
      atTop (nhds 0) :=
  etaCriticalMirrorLeftIndexNormalizedRotatedDefectAddOriginal_norm_tendsto_zero
    hs hre

end DkMath.RH.CFBRCProjection
