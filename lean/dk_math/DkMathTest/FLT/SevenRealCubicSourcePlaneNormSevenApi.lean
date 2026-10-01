/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.FLT.Seven

#print "file: DkMathTest.FLT.SevenRealCubicSourcePlaneNormSevenApi"

open DkMath.FLT.Seven
open DkMath.FLT.Seven.SevenRealCubic
open DkMath.FLT.Seven.SevenRealCubicInt

#check sourcePlaneNormSevenAxis
#check sourcePlaneNormSevenAxis_eq_two_sub_three_alpha
#check sourcePlaneNormSevenAxis_norm
#check sourcePlaneNormSevenAxis_isSourcePlane
#check sourcePlaneNormSevenAxis_thetaSquare_mul
#check norm_linearSource
#check linearSource_neg_three_one_eq_eisensteinAxis
#check linearSource_one_two_eq_ramifiedAxis
#check linearSource_two_neg_three_eq_sourcePlaneNormSevenAxis
#check sourcePlaneNormSevenAxis_mul_Y1_eq_eisensteinAxis
#check sourcePlaneNormSevenAxis_mul_Y2_eq_ramifiedAxis
#check sourcePlaneNormSevenY1_projectiveLog
#check sourcePlaneNormSevenY2_projectiveLog
#check sourcePlaneNormSevenY0_projectiveLog
#check directOrbitTrivialCommonFactorSharpenedPacket_correction_line
#check directOrbitTrivialCommonFactorSharpenedPacket_source_plane_landing

example : norm sourcePlaneNormSevenAxis = -7 := by
  exact sourcePlaneNormSevenAxis_norm

example :
    thetaSquareInt
        (sourcePlaneNormSevenAxis * ofThetaCoordinates 9 14 3) = 0 := by
  rw [sourcePlaneNormSevenAxis_thetaSquare_mul]
  norm_num

example :
    projectiveLog (Additive.ofMul sourcePlaneNormSevenY1Unit) = (0, 5) := by
  exact sourcePlaneNormSevenY1_projectiveLog

example :
    projectiveLog (Additive.ofMul sourcePlaneNormSevenY2Unit) = (0, 1) := by
  exact sourcePlaneNormSevenY2_projectiveLog
