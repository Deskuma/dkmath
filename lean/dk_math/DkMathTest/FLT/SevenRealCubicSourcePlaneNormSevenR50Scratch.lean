/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.FLT.Seven.SevenRealCubicSourcePlaneNormSeven

#print "file: DkMathTest.FLT.SevenRealCubicSourcePlaneNormSevenR50Scratch"

open DkMath.FLT.Seven
open DkMath.FLT.Seven.SevenRealCubic
open DkMath.FLT.Seven.SevenRealCubicInt

#check sourcePlaneNormSevenAxis
#check sourcePlaneNormSevenAxis_thetaSquare_mul_of
#check norm_linearSource
#check sourcePlaneNormSevenAxis_mul_Y0_eq
#check sourcePlaneNormSevenAxis_mul_Y1_eq_eisensteinAxis
#check sourcePlaneNormSevenAxis_mul_Y2_eq_ramifiedAxis
#check directOrbitTrivialCommonFactorSharpenedPacket_correction_line
#check directOrbitTrivialCommonFactorSharpenedPacket_source_plane_landing

example : norm (linearSource (-3) 1) = -7 := by
  exact norm_linearSource_neg_three_one

example : norm (linearSource 1 2) = -7 := by
  exact norm_linearSource_one_two

example : norm (linearSource 2 (-3)) = -7 := by
  exact norm_linearSource_two_neg_three
