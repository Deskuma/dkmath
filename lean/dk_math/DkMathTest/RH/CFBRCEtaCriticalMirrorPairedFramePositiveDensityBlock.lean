/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFramePositiveDensityBlock

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFramePositiveDensityBlock"

noncomputable section

namespace DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFramePositiveDensityBlock

open Filter
open scoped Topology
open DkMath.RH.CFBRCProjection

example :
    etaPairHalfDensityBlockSchedule.density = (1 : ℝ) / 2 := by
  simp

example :
    Tendsto
      (fun K : ℕ =>
        (etaPairHalfDensityBlockSchedule.blockLength K : ℝ) /
          etaPairFrameLeftEndpoint K)
      atTop (nhds ((1 : ℝ) / 2)) :=
  etaPairHalfDensityBlockSchedule.relativeLength_tendsto_density

example (S : EtaPairPositiveDensityBlockSchedule)
    (s : ℂ) {A : ℝ}
    (hA : 2 * |s.im| * S.density < A) :
    ∀ᶠ K : ℕ in atTop,
      ∀ j : ℕ, j ≤ S.blockLength K →
        etaPairFrameBlockSpan s K j < A :=
  S.eventually_all_subblockSpan_lt_of_density_upper s hA

example (S : EtaPairPositiveDensityBlockSchedule)
    {s : ℂ} (him : s.im ≠ 0)
    (hsmall : S.SmallAngleAdmissible s) :
    ∀ᶠ K : ℕ in atTop,
      ∀ j : ℕ, j ≤ S.blockLength K →
        16 * etaCriticalMirrorDefectPairNormCoefficient s *
            etaPairFrameBlockSpan s K j <
          |s.im| :=
  S.eventually_all_subblock_sixteen_mul_normCoefficient_mul_span_lt_abs_im
    him hsmall

example (S : EtaPairPositiveDensityBlockSchedule)
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re) :
    ∀ᶠ K : ℕ in atTop,
      etaCriticalMirrorRightBlockMarginSum
          s K (S.blockLength K) <
        etaCriticalMirrorRotatedDefectProjectionTail K s :=
  S.eventually_rightBlockMarginSum_lt_rotatedDefectProjectionTail
    hs him hre

example (S : EtaPairPositiveDensityBlockSchedule)
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2) :
    ∀ᶠ K : ℕ in atTop,
      etaCriticalMirrorLeftBlockMarginSum
          s K (S.blockLength K) <
        -etaCriticalMirrorRotatedDefectProjectionTail K s :=
  S.eventually_leftBlockMarginSum_lt_neg_rotatedDefectProjectionTail
    hs him hre

end DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFramePositiveDensityBlock
