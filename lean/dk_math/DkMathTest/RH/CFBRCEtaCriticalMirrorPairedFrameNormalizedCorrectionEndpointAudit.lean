/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameNormalizedCorrectionEndpointAudit

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameNormalizedCorrectionEndpointAudit"

noncomputable section

namespace DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameNormalizedCorrectionEndpointAudit

open Filter
open scoped Topology
open DkMath.RH.CFBRCProjection

example :
    Tendsto
      (fun K : ℕ =>
        etaPairFrameLeftEndpoint (K + 1) / (K : ℝ))
      atTop (nhds 2) :=
  etaPairFrameLeftEndpoint_succ_div_index_tendsto_two

example (q : ℝ) :
    Tendsto
      (fun K : ℕ =>
        (etaPairFrameLeftEndpoint (K + 1) / (K : ℝ)) ^ q)
      atTop (nhds ((2 : ℝ) ^ q)) :=
  etaPairFrameLeftEndpoint_succ_div_index_rpow_tendsto q

example {s : ℂ} (hre : (1 : ℝ) / 2 < s.re) :
    Tendsto
      (fun K : ℕ =>
        etaPairFrameLeftEndpoint (K + 1) ^ (criticalMirror s).re *
          etaCriticalMirrorPairedFrameCorrectionProjectionTailPowerBound s K)
      atTop
      (nhds
        (etaCriticalMirrorRightLeftEndpointNormalizedCorrectionConstant s)) :=
  etaCriticalMirrorRightShiftedLeftEndpointNormalizedCorrectionPowerBound_tendsto hre

example {s : ℂ} (hre : s.re < (1 : ℝ) / 2) :
    Tendsto
      (fun K : ℕ =>
        etaPairFrameLeftEndpoint (K + 1) ^ s.re *
          etaCriticalMirrorPairedFrameCorrectionProjectionTailPowerBound s K)
      atTop
      (nhds
        (etaCriticalMirrorLeftLeftEndpointNormalizedCorrectionConstant s)) :=
  etaCriticalMirrorLeftShiftedLeftEndpointNormalizedCorrectionPowerBound_tendsto hre

example {s : ℂ} (hre : (1 : ℝ) / 2 < s.re) :
    Tendsto
      (fun K : ℕ =>
        etaPairFrameLeftEndpoint K ^ (criticalMirror s).re *
          etaCriticalMirrorPairedFrameCorrectionProjectionTailPowerBound
            s (K - 1))
      atTop
      (nhds
        (etaCriticalMirrorRightLeftEndpointNormalizedCorrectionConstant s)) :=
  etaCriticalMirrorRightPredecessorLeftEndpointNormalizedCorrectionPowerBound_tendsto hre

example {s : ℂ} (hre : s.re < (1 : ℝ) / 2) :
    Tendsto
      (fun K : ℕ =>
        etaPairFrameLeftEndpoint K ^ s.re *
          etaCriticalMirrorPairedFrameCorrectionProjectionTailPowerBound
            s (K - 1))
      atTop
      (nhds
        (etaCriticalMirrorLeftLeftEndpointNormalizedCorrectionConstant s)) :=
  etaCriticalMirrorLeftPredecessorLeftEndpointNormalizedCorrectionPowerBound_tendsto hre

end DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameNormalizedCorrectionEndpointAudit
