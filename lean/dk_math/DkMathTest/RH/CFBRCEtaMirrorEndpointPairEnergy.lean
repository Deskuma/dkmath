/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaMirrorEndpointPairEnergy

#print "file: DkMathTest.RH.CFBRCEtaMirrorEndpointPairEnergy"

noncomputable section

namespace DkMathTest.RH.CFBRCEtaMirrorEndpointPairEnergy

open Filter
open scoped Topology
open DkMath.RH.CFBRCProjection
open DkMath.RH.Weave.Analytic

example (N : ℕ) (s : ℂ) :
    etaMirrorEndpointBig N s + etaMirrorEndpointGap N s =
      2 * etaMirrorEndpointTotalEnergy N s := by
  exact etaMirrorEndpointBig_add_gap_eq_two_mul_totalEnergy N s

example {s : ℂ}
    (horiginal :
      Tendsto (fun N : ℕ => etaPartialEndpoint N s) atTop (nhds 0))
    (hmirror :
      Tendsto (fun N : ℕ => etaPartialEndpoint N (criticalMirror s))
        atTop (nhds 0)) :
    Tendsto (fun N : ℕ => etaMirrorEndpointGap N s) atTop (nhds 0) := by
  exact etaMirrorEndpointGap_tendsto_zero_of_endpoint_limits
    horiginal hmirror

example {s : ℂ}
    (horiginalConv : EtaPartialConvergesAt s)
    (hmirrorConv : EtaPartialConvergesAt (criticalMirror s))
    (horiginalZero : riemannZeta s = 0)
    (hmirrorZero : riemannZeta (criticalMirror s) = 0) :
    Tendsto (fun N : ℕ => etaMirrorEndpointTotalEnergy N s)
        atTop (nhds 0) ∧
      Tendsto (fun N : ℕ => etaMirrorEndpointBig N s)
        atTop (nhds 0) ∧
      Tendsto (fun N : ℕ => etaMirrorEndpointGap N s)
        atTop (nhds 0) := by
  exact etaMirrorEndpoint_pairEnergy_limits_of_riemannZeta_pair
    horiginalConv hmirrorConv horiginalZero hmirrorZero

example {s : ℂ}
    (horiginal :
      Tendsto (fun N : ℕ => etaPartialEndpoint N s) atTop (nhds 0))
    (hmirror :
      Tendsto (fun N : ℕ => etaPartialEndpoint N (criticalMirror s))
        atTop (nhds 0)) :
    EtaMirrorEndpointGapControlsUnitGapAt s ↔
      s.re = (1 : ℝ) / 2 := by
  exact etaMirrorEndpointGapControlsUnitGapAt_iff_re_eq_half
    horiginal hmirror

end DkMathTest.RH.CFBRCEtaMirrorEndpointPairEnergy
