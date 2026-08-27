import DkMath.RH.CFBRC.EtaCriticalMirrorEndpointLimits

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorEndpointLimits"

namespace DkMathTest.RH.CFBRCEtaCriticalMirrorEndpointLimits

open Filter
open scoped Topology
open DkMath.RH.CFBRCProjection

example {s : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0) :
    Tendsto (fun N : ℕ => etaPartialEndpoint N s) atTop (nhds 0) :=
  etaPartialEndpoint_tendsto_zero_of_nontrivialRiemannZetaZero hs him

example {s : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0) :
    Tendsto (fun N : ℕ => etaPartialEndpoint N (criticalMirror s))
      atTop (nhds 0) :=
  etaPartialEndpoint_criticalMirror_tendsto_zero_of_nontrivialRiemannZetaZero
    hs him

example {s : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0) :
    EtaCriticalMirrorEndpointVanishing s :=
  etaCriticalMirrorEndpointVanishing_of_nontrivialRiemannZetaZero hs him

end DkMathTest.RH.CFBRCEtaCriticalMirrorEndpointLimits
