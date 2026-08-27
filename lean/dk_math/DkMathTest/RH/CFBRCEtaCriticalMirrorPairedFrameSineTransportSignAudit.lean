/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameSineTransportSignAudit

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameSineTransportSignAudit"

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology

example (k : ℕ) :
    0 <
      Real.log (etaPairFrameLeftEndpoint (k + 1)) -
        Real.log (etaPairFrameLeftEndpoint k) :=
  etaPairFrameLogStep_pos k

example {s : ℂ} (him : 0 < s.im) (k : ℕ) :
    0 < etaPairFrameStepPhase s k :=
  etaPairFrameStepPhase_pos_of_im_pos him k

example {s : ℂ} (him : s.im < 0) (k : ℕ) :
    etaPairFrameStepPhase s k < 0 :=
  etaPairFrameStepPhase_neg_of_im_neg him k

example {s : ℂ} (him : s.im ≠ 0) :
    ∀ᶠ k : ℕ in atTop,
      0 < etaCriticalMirrorPairedFrameSineTransportCoefficient s k :=
  eventually_etaCriticalMirrorPairedFrameSineTransportCoefficient_pos him

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (k : ℕ) :
    etaCriticalMirrorPairFrameTransportedDefectPartial s k =
      -etaCriticalMirrorPairFrameRotatedDefectTail s k :=
  etaCriticalMirrorPairFrameTransportedDefectPartial_eq_neg_rotatedDefectTail
    hs him k

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (k : ℕ) :
    etaCriticalMirrorPairedFrameCorrectionSineTransportTerm s k =
      -etaCriticalMirrorPairedFrameSineTransportCoefficient s k *
        (etaCriticalMirrorPairFrameRotatedDefectTail s k).re :=
  etaCriticalMirrorPairedFrameCorrectionSineTransportTerm_eq_neg_coefficient_mul_rotatedDefectTail_re
    hs him k

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) :
    ∀ᶠ k : ℕ in atTop,
      0 < (etaCriticalMirrorPairFrameRotatedDefectTail s k).re →
        etaCriticalMirrorPairedFrameCorrectionSineTransportTerm s k < 0 :=
  eventually_sineTransportTerm_neg_of_rotatedDefectTail_re_pos hs him

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) :
    ∀ᶠ k : ℕ in atTop,
      (etaCriticalMirrorPairFrameRotatedDefectTail s k).re < 0 →
        0 < etaCriticalMirrorPairedFrameCorrectionSineTransportTerm s k :=
  eventually_sineTransportTerm_pos_of_rotatedDefectTail_re_neg hs him

end DkMath.RH.CFBRCProjection
