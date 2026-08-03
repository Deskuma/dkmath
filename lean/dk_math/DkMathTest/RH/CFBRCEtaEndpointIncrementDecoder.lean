import DkMath.RH.CFBRC.EtaEndpointIncrementDecoder

#print "file: DkMathTest.RH.CFBRCEtaEndpointIncrementDecoder"

namespace DkMathTest.RH.CFBRCEtaEndpointIncrementDecoder

open DkMath.RH.CFBRCProjection

example (N : ℕ) (s : ℂ) :
    etaEndpointIncrement N s = etaSignedVector s N := by
  simp

example (s : ℂ) :
    etaEndpointIncrementDecoder s = centeredSigma s.re :=
  etaEndpointIncrementDecoder_eq_centeredSigma s

example (s : ℂ) :
    etaEndpointIncrementMirrorRatio s 1 = 1 ↔
      s.re = (1 : ℝ) / 2 :=
  etaEndpointIncrementMirrorRatio_one_eq_one_iff_re_eq_half s

example :
    EtaEndpointIncrementBalancedOnNontrivialZeros ↔ RiemannHypothesis :=
  etaEndpointIncrementBalancedOnNontrivialZeros_iff_riemannHypothesis

example
    (hbalance : EtaEndpointIncrementBalancedOnNontrivialZeros)
    {d : ℕ} (hd : 0 < d) (phase : ℂ → ℝ) :
    ZeroToCFBRCBridge NontrivialRiemannZetaZero :=
  zeroToCFBRCBridge_of_endpointIncrementBalance hbalance hd phase

end DkMathTest.RH.CFBRCEtaEndpointIncrementDecoder
