import DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicTrivialCommonFactorPairedDeepJet

namespace DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicTrivialCommonFactorPairedDeepJetR43Scratch

open DkMath.FLT.Seven
open DkMath.FLT.Seven.SevenRealCubic
open DkMath.FLT.Seven.SevenRealCubicInt

example (A B C : ℤ) :
    thetaConstInt
        (SevenRealCubicInt.rotateEquiv (ofThetaCoordinates A B C) -
          ofThetaCoordinates A B C) = -7 * C ∧
      thetaLinearInt
        (SevenRealCubicInt.rotateEquiv (ofThetaCoordinates A B C) -
          ofThetaCoordinates A B C) = 3 * B - 21 * C ∧
      thetaSquareInt
        (SevenRealCubicInt.rotateEquiv (ofThetaCoordinates A B C) -
          ofThetaCoordinates A B C) = B - 6 * C := by
  exact directOrbitPairedDeepJet_rotate_gap_theta_coordinates A B C

example {x : SevenRealCubicInt} (hx : eisensteinAxis ^ 6 ∣ x) :
    (49 : SevenRealCubicInt) ∣ x := by
  exact directOrbit_axis_pow_six_dvd_imp_natCast49 hx

example {x : SevenRealCubicInt} (hx : eisensteinAxis ^ 9 ∣ x) :
    (343 : SevenRealCubicInt) ∣ x := by
  exact directOrbit_axis_pow_nine_dvd_imp_natCast343 hx

end DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicTrivialCommonFactorPairedDeepJetR43Scratch
