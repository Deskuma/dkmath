import DkMath.RH.CFBRC.EtaCriticalMirrorEnergyCollapse

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorEnergyCollapse"

namespace DkMathTest.RH.CFBRCEtaCriticalMirrorEnergyCollapse

open Filter
open scoped Topology
open DkMath.RH.CFBRCProjection

example {s : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0) :
    Tendsto (fun N : ℕ => etaMirrorEndpointOuterBig N s)
      atTop (nhds 0) :=
  etaMirrorEndpointOuterBig_tendsto_zero_of_nontrivialRiemannZetaZero hs him

example {s : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0) :
    EtaCriticalMirrorEnergyCollapse s :=
  etaCriticalMirrorEnergyCollapse_of_nontrivialRiemannZetaZero hs him

end DkMathTest.RH.CFBRCEtaCriticalMirrorEnergyCollapse
