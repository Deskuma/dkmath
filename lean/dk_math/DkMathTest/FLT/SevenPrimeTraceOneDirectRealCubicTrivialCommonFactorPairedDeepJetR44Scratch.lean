import DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicTrivialCommonFactorPairedDeepJet

namespace DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicTrivialCommonFactorPairedDeepJetR44Scratch

open DkMath.FLT.Seven
open DkMath.FLT.Seven.SevenRealCubic
open DkMath.FLT.Seven.SevenRealCubicInt

#check directOrbitPairedDeepJet_source_root_sub_scalar_dvd49
#check directOrbitPairedDeepJet_source_root_pow_six_mod49_scalar
#check directOrbitPairedDeepJet_quotient_remainder_cancel_theta
#check directOrbitPairedDeepJet_z_pow_seven_square_mod49
#check directOrbitPairedDeepJet_z_square_mod_seven
#check directOrbitPairedDeepJet_inverse_square_mod_seven
#check directOrbitPairedDeepJet_v_square_mod_seven
#check directOrbitPairedDeepJet_v_projective_log_zero
#check directOrbitPairedDeepJet_v_seventh_power
#check directOrbitPairedDeepJet_49th_power_correction

example (A B C : ℤ) :
    (49 : ℤ) ∣
      thetaSquareInt ((ofThetaCoordinates A B C) ^ 7) -
        7 * (C * A ^ 6 + 3 * B ^ 2 * A ^ 5) := by
  exact thetaSquare_pow_seven_mod49_neutral A B C

example (v : SevenRealCubicIntˣ)
    (hlin : thetaLinearModSeven (v : SevenRealCubicInt) = 0)
    (hsq : thetaSquareModSeven (v : SevenRealCubicInt) = 0) :
    projectiveLog (Additive.ofMul v) = 0 := by
  exact directOrbitPairedDeepJet_v_projective_log_zero v hlin hsq

end DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicTrivialCommonFactorPairedDeepJetR44Scratch
