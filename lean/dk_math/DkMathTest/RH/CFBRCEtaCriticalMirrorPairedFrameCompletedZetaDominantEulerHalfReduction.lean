import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameCompletedZetaDominantEulerHalfReduction

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameCompletedZetaDominantEulerHalfReduction"

noncomputable section

namespace DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameCompletedZetaDominantEulerHalfReduction

open Filter
open scoped Topology
open DkMath.RH.CFBRCProjection

example
    (k : ℕ) (s : ℂ) :
    etaCriticalMirrorDominantWeightedTailEulerMainCarrier k s =
      etaCriticalMirrorDominantEulerHalfEndpointCarrier k s +
        etaCriticalMirrorSuppressedEulerHalfEndpointCarrier k s := by
  exact
    etaCriticalMirrorDominantWeightedTailEulerMainCarrier_eq_dominant_add_suppressed
      k s

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) :
    Tendsto
      (fun k : ℕ =>
        etaCriticalMirrorSuppressedEulerHalfEndpointCarrier k s)
      atTop (nhds 0) := by
  exact etaCriticalMirrorSuppressedEulerHalfEndpointCarrier_tendsto_zero hs

example :
    EtaCriticalMirrorWeightedTailEulerMainCarrierTransverseCollapse ↔
      EtaCriticalMirrorDominantEulerHalfEndpointCarrierTransverseCollapse := by
  exact
    etaCriticalMirrorWeightedTailEulerMainCarrierTransverseCollapse_iff_dominantHalfEndpoint

example
    (hdominant :
      EtaCriticalMirrorDominantEulerHalfEndpointCarrierTransverseCollapse) :
    RiemannHypothesis := by
  exact
    riemannHypothesis_of_dominantEulerHalfEndpointCarrierTransverseCollapse
      hdominant

end DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameCompletedZetaDominantEulerHalfReduction
