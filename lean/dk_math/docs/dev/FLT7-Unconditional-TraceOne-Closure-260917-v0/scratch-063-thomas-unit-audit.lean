import DkMath.FLT.Seven.SevenRealCubicThomasUnit

open DkMath.FLT.Seven
open DkMath.FLT.Seven.SevenRealCubicInt

namespace DkMath.FLT.Seven.SevenRealCubic

#print axioms thomasLambda_cubic_relation
#print axioms thomasLambda_projectiveLog
#print axioms thetaNilpotentDepth_inv
#print axioms thomas_sigma5_normalization
#print axioms thomasPlaneUnit_exists_seven_pow
#print axioms thomasPlane_seventh_root_B_dvd

example :
    projectiveLog (Additive.ofMul thomasLambdaUnit) = (0, 2) := by
  exact thomasLambda_projectiveLog

example (R S : ℤ) :
    thetaLinearInt (thomasPlaneElement R S) =
      7 * thetaSquareInt (thomasPlaneElement R S) := by
  exact thomasPlaneElement_theta_plane R S

example (R S : ℤ) (hfive : F5 R S = 1)
    (hS : (7 : ℤ) ^ 8 ∣ S) :
    projectiveLog
        (Additive.ofMul (thomasPlaneUnit R S hfive)) = 0 := by
  exact thomasPlaneUnit_projectiveLog_zero hfive hS

end DkMath.FLT.Seven.SevenRealCubic
