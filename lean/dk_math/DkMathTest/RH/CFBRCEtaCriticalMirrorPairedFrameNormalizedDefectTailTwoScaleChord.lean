/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameNormalizedDefectTailTwoScaleChord

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameNormalizedDefectTailTwoScaleChord"

noncomputable section

namespace DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameNormalizedDefectTailTwoScaleChord

open Filter
open scoped Topology
open DkMath.RH.CFBRCProjection

example (a : ℝ) (s : ℂ) (K N : ℕ) :
    etaCriticalMirrorIndexNormalizedDefectTailChord a s K N =
      ‖etaCriticalMirrorIndexNormalizedRotatedDefectTail a s (K + N) -
        etaPairFrameBlockRotation s K N *
          etaCriticalMirrorIndexNormalizedRotatedDefectTail a s K‖ :=
  etaCriticalMirrorIndexNormalizedDefectTailChord_eq_rotated_sub_blockRotation_mul
    a s K N

example
    (S : EtaPairPositiveDensityBlockSchedule)
    {a : ℝ} {s C : ℂ}
    (hrotated :
      Tendsto
        (etaCriticalMirrorIndexNormalizedRotatedDefectTail a s)
        atTop (nhds C)) :
    Tendsto
      (S.scheduledNormalizedDefectTailChord a s)
      atTop
      (nhds ‖C - S.scheduledBlockRotationLimit s * C‖) :=
  S.scheduledNormalizedDefectTailChord_tendsto hrotated

example
    {a : ℝ} {s C : ℂ}
    (him : s.im ≠ 0)
    (hrotated :
      Tendsto
        (etaCriticalMirrorIndexNormalizedRotatedDefectTail a s)
        atTop (nhds C))
    (hC : C ≠ 0) :
    EtaCriticalMirrorTwoScaleNormalizedDefectTailChordCertificate a s C :=
  etaCriticalMirrorTwoScaleNormalizedDefectTailChordCertificate_of_rotated_limit
    him hrotated hC

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re) :
    EtaCriticalMirrorTwoScaleNormalizedDefectTailChordCertificate
      (criticalMirror s).re s
      (etaPairIndexNormalizedTailConstant (criticalMirror s)) :=
  etaCriticalMirrorRightTwoScaleNormalizedDefectTailChordCertificate_of_zero
    hs him hre

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2) :
    EtaCriticalMirrorTwoScaleNormalizedDefectTailChordCertificate
      s.re s (-etaPairIndexNormalizedTailConstant s) :=
  etaCriticalMirrorLeftTwoScaleNormalizedDefectTailChordCertificate_of_zero
    hs him hre

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re ≠ (1 : ℝ) / 2) :
    (s.re < (1 : ℝ) / 2 ∧
      EtaCriticalMirrorTwoScaleNormalizedDefectTailChordCertificate
        s.re s (-etaPairIndexNormalizedTailConstant s)) ∨
    ((1 : ℝ) / 2 < s.re ∧
      EtaCriticalMirrorTwoScaleNormalizedDefectTailChordCertificate
        (criticalMirror s).re s
        (etaPairIndexNormalizedTailConstant (criticalMirror s))) :=
  etaCriticalMirrorOffCriticalTwoScaleNormalizedDefectTailChordCertificate_of_zero
    hs him hre

end DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameNormalizedDefectTailTwoScaleChord
