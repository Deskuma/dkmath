import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameCompletedZetaDominantEulerHalfRHEquivalenceAudit

open Filter
open scoped Topology

namespace DkMathTest.RH.CFBRCProjection

open DkMath.RH.CFBRCProjection

example {s : ℂ} (hcritical : s.re = (1 : ℝ) / 2) (k : ℕ) :
    etaCriticalMirrorDominantWeightedTailEulerMainCarrier k s = 0 :=
  etaCriticalMirrorDominantWeightedTailEulerMainCarrier_eq_zero_of_re_eq_half
    hcritical k

example {s : ℂ} (hcritical : s.re = (1 : ℝ) / 2) (k : ℕ) :
    etaCriticalMirrorDominantEulerHalfEndpointCarrier k s = 0 :=
  etaCriticalMirrorDominantEulerHalfEndpointCarrier_eq_zero_of_re_eq_half
    hcritical k

example (hRH : RiemannHypothesis) :
    EtaCriticalMirrorDominantEulerHalfEndpointCarrierTransverseCollapse :=
  etaCriticalMirrorDominantEulerHalfEndpointCarrierTransverseCollapse_of_riemannHypothesis
    hRH

example :
    EtaCriticalMirrorDominantEulerHalfEndpointCarrierTransverseCollapse ↔
      RiemannHypothesis :=
  etaCriticalMirrorDominantEulerHalfEndpointCarrierTransverseCollapse_iff_riemannHypothesis

end DkMathTest.RH.CFBRCProjection
