import DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicTrivialCommonFactorPairedDeepJet

namespace DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicTrivialCommonFactorPairedDeepJetR42Scratch

open DkMath.FLT.Seven
open DkMath.FLT.Seven.SevenRealCubic
open DkMath.FLT.Seven.SevenRealCubicInt

example :
    orbitUnit01Unit * directOrbitDeepJetThetaUnit⁻¹ ^ 3 *
        directOrbitDeepJetRho⁻¹ = directOrbitDeepJetThetaUnit := by
  exact directOrbitPairedDeepJet_fixed_unit_identity

example {x : SevenRealCubicInt} (hx : eisensteinAxis ^ 6 ∣ x) :
    (49 : SevenRealCubicInt) ∣ x := by
  exact directOrbit_axis_pow_six_dvd_imp_natCast49 hx

example {x : SevenRealCubicInt} (hx : eisensteinAxis ^ 9 ∣ x) :
    (343 : SevenRealCubicInt) ∣ x := by
  exact directOrbit_axis_pow_nine_dvd_imp_natCast343 hx

end DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicTrivialCommonFactorPairedDeepJetR42Scratch
