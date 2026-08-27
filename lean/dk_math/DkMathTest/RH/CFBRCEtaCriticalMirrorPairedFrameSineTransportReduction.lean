/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameSineTransportReduction

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameSineTransportReduction"

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) :
    Summable
      (etaCriticalMirrorPairedFrameCorrectionSignedProjectionTerm s) :=
  summable_etaCriticalMirrorPairedFrameCorrectionSignedProjectionTerm
    hs him

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) :
    Summable
      (etaCriticalMirrorPairedFrameCorrectionSineTransportTerm s) :=
  summable_etaCriticalMirrorPairedFrameCorrectionSineTransportTerm
    hs him

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (K : ℕ) :
    etaCriticalMirrorPairedFrameCorrectionProjectionTail K s =
      etaCriticalMirrorPairedFrameCorrectionSineTransportTail K s +
        etaCriticalMirrorPairedFrameCorrectionCosineLossTail K s :=
  etaCriticalMirrorPairedFrameCorrectionProjectionTail_eq_sineTransportTail_add_cosineLossTail
    hs him K

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (K : ℕ) :
    etaCriticalMirrorPairedFrameCorrectionProjectionTail K s -
        etaCriticalMirrorPairedFrameCorrectionSineTransportTail K s =
      etaCriticalMirrorPairedFrameCorrectionCosineLossTail K s :=
  etaCriticalMirrorPairedFrameCorrectionProjectionTail_sub_sineTransportTail_eq_cosineLossTail
    hs him K

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re) :
    Tendsto
      (fun K : ℕ =>
        etaPairFrameLeftEndpoint K ^ (criticalMirror s).re *
            etaCriticalMirrorPairedFrameCorrectionProjectionTail (K - 1) s -
          etaPairFrameLeftEndpoint K ^ (criticalMirror s).re *
            etaCriticalMirrorPairedFrameCorrectionSineTransportTail (K - 1) s)
      atTop (nhds 0) :=
  etaCriticalMirrorRightPredecessorLeftEndpointNormalizedCorrection_sub_normalizedSineTransport_tendsto_zero
    hs him hre

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2) :
    Tendsto
      (fun K : ℕ =>
        etaPairFrameLeftEndpoint K ^ s.re *
            etaCriticalMirrorPairedFrameCorrectionProjectionTail (K - 1) s -
          etaPairFrameLeftEndpoint K ^ s.re *
            etaCriticalMirrorPairedFrameCorrectionSineTransportTail (K - 1) s)
      atTop (nhds 0) :=
  etaCriticalMirrorLeftPredecessorLeftEndpointNormalizedCorrection_sub_normalizedSineTransport_tendsto_zero
    hs him hre

end DkMath.RH.CFBRCProjection
