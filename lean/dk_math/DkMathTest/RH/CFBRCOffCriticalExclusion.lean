import DkMath.RH.CFBRC.OffCriticalExclusion

#print "file: DkMathTest.RH.CFBRCOffCriticalExclusion"

namespace DkMathTest.RH.CFBRCOffCriticalExclusion

open DkMath.CFBRC.TrigBridge
open DkMath.RH.CFBRCProjection

example (X Θ : ℝ) :
    cfbrcR 2 X Θ = 0 ↔ X = 0 :=
  cfbrcR_two_eq_zero_iff_x_eq_zero X Θ

example (σ Θ : ℝ) :
    offCriticalCFBRC 2 σ Θ = 0 ↔ σ = (1 : ℝ) / 2 :=
  offCriticalCFBRC_two_eq_zero_iff_re_eq_half σ Θ

example
    {Zero : ℂ → Prop}
    (bridge : ZeroToCFBRCTwoBridge Zero)
    {s : ℂ}
    (hs : Zero s) :
    s.re = (1 : ℝ) / 2 :=
  re_eq_half_of_zeroToCFBRCTwoBridge bridge hs

end DkMathTest.RH.CFBRCOffCriticalExclusion
