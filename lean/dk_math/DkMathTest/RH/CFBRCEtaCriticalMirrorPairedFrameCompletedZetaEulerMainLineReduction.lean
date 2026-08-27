import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameCompletedZetaEulerMainLineReduction

namespace DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameCompletedZetaEulerMainLineReduction

open DkMath.RH.CFBRCProjection
open Filter
open scoped Topology

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (k : ℕ) :
    etaCriticalMirrorNormalizedNearbyGammaZetaCarrier k s =
      completedZetaCanonicalSlopeCarrier k s := by
  exact
    etaCriticalMirrorNormalizedNearbyGammaZetaCarrier_eq_slopeCarrier_of_zero
      hs k

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) :
    Tendsto
      (fun k : ℕ =>
        complexRealLineDefect
          (completedZetaCanonicalSlopeDirection s)
          (etaCriticalMirrorNormalizedNearbyGammaZetaCarrier k s))
      atTop (nhds 0) := by
  exact etaCriticalMirrorNormalizedNearbyGammaZetaCarrier_tendsto_global_line hs

example :
    EtaCriticalMirrorWeightedTailCompletedZetaNearbyEulerMainTransverseCollapse ↔
      EtaCriticalMirrorWeightedTailEulerMainCarrierTransverseCollapse := by
  exact
    etaCriticalMirrorWeightedTailCompletedZetaNearbyEulerMainTransverseCollapse_iff_mainCarrier

example
    (hmain : EtaCriticalMirrorWeightedTailEulerMainCarrierTransverseCollapse) :
    RiemannHypothesis := by
  exact riemannHypothesis_of_weightedTailEulerMainCarrierTransverseCollapse hmain

end DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameCompletedZetaEulerMainLineReduction
