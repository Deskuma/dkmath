import DkMath.RH.CFBRC.EtaCriticalMirrorWeightedTransport

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorWeightedTransport"

namespace DkMathTest.RH.CFBRCEtaCriticalMirrorWeightedTransport

open Filter
open scoped Topology
open DkMath.RH.CFBRCProjection

example (s : ℂ) (m : ℕ) :
    etaSignedVector (criticalMirror s) m =
      etaCriticalMirrorTermWeight s m * etaSignedVector s m :=
  etaSignedVector_criticalMirror_eq_weight_mul s m

example (N : ℕ) (s : ℂ) :
    etaCriticalMirrorWeightedEndpoint N s =
      etaPartialEndpoint N (criticalMirror s) :=
  etaCriticalMirrorWeightedEndpoint_eq_mirrorEndpoint N s

example (N : ℕ) (s : ℂ) :
    etaCriticalMirrorTransportDefectEndpoint N s =
      (Finset.range N).sum fun m =>
        (etaCriticalMirrorTermWeight s m - 1) * etaSignedVector s m :=
  etaCriticalMirrorTransportDefectEndpoint_eq_sum N s

example {s : ℂ} (hre : s.re = (1 : ℝ) / 2) (N : ℕ) :
    etaCriticalMirrorWeightedEndpoint N s = etaPartialEndpoint N s :=
  etaCriticalMirrorWeightedEndpoint_eq_original_of_re_eq_half hre N

example {s : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0) :
    Tendsto (fun N : ℕ => etaCriticalMirrorWeightedEndpoint N s)
      atTop (nhds 0) :=
  etaCriticalMirrorWeightedEndpoint_tendsto_zero_of_nontrivialRiemannZetaZero
    hs him

example {s : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0) :
    Tendsto (fun N : ℕ => etaCriticalMirrorTransportDefectEndpoint N s)
      atTop (nhds 0) :=
  etaCriticalMirrorTransportDefectEndpoint_tendsto_zero_of_nontrivialRiemannZetaZero
    hs him

end DkMathTest.RH.CFBRCEtaCriticalMirrorWeightedTransport
