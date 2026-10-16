/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRealCubicThetaCoordinates

#print "file: DkMath.FLT.Seven.SevenRealCubicThetaSeventhPower"

namespace DkMath.FLT.Seven.SevenRealCubicInt

def seventhThetaLinearBFactor (A B C : ℤ) : ℤ :=
  A^6 - 84*A^5*C - 70*A^4*B^2 + 1365*A^4*B*C - 6615*A^4*C^2 +
  455*A^3*B^3 - 8820*A^3*B^2*C + 57330*A^3*B*C^2 -
  156800*A^3*C^3 - 1323*A^2*B^4 + 28665*A^2*B^3*C -
  235200*A^2*B^2*C^2 + 936390*A^2*B*C^3 - 1831620*A^2*C^4 +
  1911*A*B^5 - 47040*A*B^4*C + 468195*A*B^3*C^2 -
  2442160*A*B^2*C^3 + 7089810*A*B*C^4 - 10905342*A*C^5 -
  1120*B^6 + 31213*B^5*C - 366324*B^4*C^2 + 2363270*B^3*C^3 -
  9087785*B^2*C^4 + 20881497*B*C^5 - 26586273*C^6

def seventhThetaLinearCFactor (A C : ℤ) : ℤ :=
  39*A^5 + 1365*A^4*C + 22295*A^3*C^2 + 202566*A^2*C^3 +
  994357*A*C^4 + 2068976*C^5

def seventhThetaLinearQuotient (A B C : ℤ) : ℤ :=
  B * seventhThetaLinearBFactor A B C +
    7 * C^2 * seventhThetaLinearCFactor A C

def seventhThetaSquareBFactor (A B : ℤ) : ℤ :=
  3*A^5 - 35*A^4*B + 175*A^3*B^2 - 462*A^2*B^3 +
  637*A*B^4 - 364*B^5

def seventhThetaSquareCFactor (A B C : ℤ) : ℤ :=
  A^6 - 42*A^5*B + 105*A^5*C + 525*A^4*B^2 - 2310*A^4*B*C +
  3185*A^4*C^2 - 3080*A^3*B^3 + 19110*A^3*B^2*C -
  50960*A^3*B*C^2 + 49980*A^3*C^3 + 9555*A^2*B^4 -
  76440*A^2*B^3*C + 299880*A^2*B^2*C^2 -
  581385*A^2*B*C^3 + 447615*A^2*C^4 - 15288*A*B^5 +
  149940*A*B^4*C - 775180*A*B^3*C^2 + 2238075*A*B^2*C^3 -
  3430686*A*B*C^4 + 2184910*A*C^5 + 9996*B^6 -
  116277*B^5*C + 746025*B^4*C^2 - 2858905*B^3*C^3 +
  6554730*B^2*C^4 - 8333871*B*C^5 + 4535832*C^6

def seventhThetaSquareQuotient (A B C : ℤ) : ℤ :=
  C * seventhThetaSquareCFactor A B C +
    B^2 * seventhThetaSquareBFactor A B

/-- 七乗の逐次展開を避け、二乗・四乗を共有するための有限座標恒等式。 -/
private theorem theta_pow_two (A B C : ℤ) :
    (ofThetaCoordinates A B C) ^ 2 = ⟨A^2 - 6*A*B + 18*A*C + 9*B^2 - 56*B*C + 91*C^2,
      2*A*B - 12*A*C - 6*B^2 + 56*B*C - 119*C^2,
      2*A*C + B^2 - 14*B*C + 35*C^2⟩ := by
  ext <;> norm_num [pow_two, ofThetaCoordinates, eisensteinAxis_sq_coordinates] <;> ring

/-- 正規化済みの二乗座標から四乗を計算し、七乗の式膨張を抑える。 -/
private theorem theta_pow_four (A B C : ℤ) :
    (ofThetaCoordinates A B C) ^ 4 = ⟨A^4 - 12*A^3*B + 36*A^3*C + 54*A^2*B^2 - 336*A^2*B*C +
      546*A^2*C^2 - 112*A*B^3 + 1092*A*B^2*C - 3696*A*B*C^2 + 4312*A*C^3 + 91*B^4 - 1232*B^3*C +
      6468*B^2*C^2 - 15484*B*C^3 + 14161*C^4,
      4*A^3*B - 24*A^3*C - 36*A^2*B^2 + 336*A^2*B*C - 714*A^2*C^2 + 112*A*B^3 - 1428*A*B^2*C +
      5796*A*B*C^2 - 7644*A*C^3 - 119*B^4 + 1932*B^3*C - 11466*B^2*C^2 + 29792*B*C^3 - 28763*C^4,
      4*A^3*C + 6*A^2*B^2 - 84*A^2*B*C + 210*A^2*C^2 - 28*A*B^3 + 420*A*B^2*C - 1848*A*B*C^2 +
      2548*A*C^3 + 35*B^4 - 616*B^3*C + 3822*B^2*C^2 - 10192*B*C^3 + 9996*C^4⟩ := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, theta_pow_two]
  ext <;> norm_num [pow_two] <;> ring

set_option maxHeartbeats 1200000 in
-- 分割後も七次の整数係数多項式の正規化には既定値を超える計算量が必要。
set_option maxRecDepth 100000 in
theorem thetaLinear_pow_seven (A B C : ℤ) :
    thetaLinearInt ((ofThetaCoordinates A B C) ^ 7) =
      7 * seventhThetaLinearQuotient A B C := by
  have hp : (ofThetaCoordinates A B C)^7 =
      (ofThetaCoordinates A B C)^4 * (ofThetaCoordinates A B C)^2 *
        ofThetaCoordinates A B C := by ring
  rw [hp, theta_pow_four, theta_pow_two]
  norm_num [thetaLinearInt, ofThetaCoordinates, eisensteinAxis_sq_coordinates,
    seventhThetaLinearQuotient, seventhThetaLinearBFactor, seventhThetaLinearCFactor]
  ring

set_option maxHeartbeats 1200000 in
-- 二次座標も七次多項式の全係数をカーネルで検証するため上限を増やす。
set_option maxRecDepth 100000 in
theorem thetaSquare_pow_seven (A B C : ℤ) :
    thetaSquareInt ((ofThetaCoordinates A B C) ^ 7) =
      7 * seventhThetaSquareQuotient A B C := by
  have hp : (ofThetaCoordinates A B C)^7 =
      (ofThetaCoordinates A B C)^4 * (ofThetaCoordinates A B C)^2 *
        ofThetaCoordinates A B C := by ring
  rw [hp, theta_pow_four, theta_pow_two]
  norm_num [thetaSquareInt, ofThetaCoordinates, eisensteinAxis_sq_coordinates,
    seventhThetaSquareQuotient, seventhThetaSquareBFactor, seventhThetaSquareCFactor]
  ring

theorem seventhThetaLinearBFactor_modSeven (A B C : ℤ) :
    (seventhThetaLinearBFactor A B C : ZMod 7) = (A : ZMod 7)^6 := by
  have h :
      seventhThetaLinearBFactor A B C = A^6 + 7 *
        (-12*A^5*C - 10*A^4*B^2 + 195*A^4*B*C - 945*A^4*C^2 +
        65*A^3*B^3 - 1260*A^3*B^2*C + 8190*A^3*B*C^2 -
        22400*A^3*C^3 - 189*A^2*B^4 + 4095*A^2*B^3*C -
        33600*A^2*B^2*C^2 + 133770*A^2*B*C^3 - 261660*A^2*C^4 +
        273*A*B^5 - 6720*A*B^4*C + 66885*A*B^3*C^2 -
        348880*A*B^2*C^3 + 1012830*A*B*C^4 - 1557906*A*C^5 -
        160*B^6 + 4459*B^5*C - 52332*B^4*C^2 + 337610*B^3*C^3 -
        1298255*B^2*C^4 + 2983071*B*C^5 - 3798039*C^6) := by
    simp [seventhThetaLinearBFactor]
    ring
  rw [h]
  push_cast
  rw [show (7 : ZMod 7) = 0 by decide, zero_mul, add_zero]

theorem seventhThetaLinearCFactor_modSeven (A C : ℤ) :
    (seventhThetaLinearCFactor A C : ZMod 7) =
      -3 * (A : ZMod 7)^5 := by
  have h : seventhThetaLinearCFactor A C = -3*A^5 + 7 *
      (6*A^5 + 195*A^4*C + 3185*A^3*C^2 + 28938*A^2*C^3 +
        142051*A*C^4 + 295568*C^5) := by
    simp [seventhThetaLinearCFactor]
    ring
  rw [h]
  push_cast
  rw [show (7 : ZMod 7) = 0 by decide, zero_mul, add_zero]

theorem seventhThetaSquareCFactor_modSeven (A B C : ℤ) :
    (seventhThetaSquareCFactor A B C : ZMod 7) = (A : ZMod 7)^6 := by
  have h : seventhThetaSquareCFactor A B C = A^6 + 7 *
      (-6*A^5*B + 15*A^5*C + 75*A^4*B^2 - 330*A^4*B*C +
      455*A^4*C^2 - 440*A^3*B^3 + 2730*A^3*B^2*C -
      7280*A^3*B*C^2 + 7140*A^3*C^3 + 1365*A^2*B^4 -
      10920*A^2*B^3*C + 42840*A^2*B^2*C^2 - 83055*A^2*B*C^3 +
      63945*A^2*C^4 - 2184*A*B^5 + 21420*A*B^4*C -
      110740*A*B^3*C^2 + 319725*A*B^2*C^3 - 490098*A*B*C^4 +
      312130*A*C^5 + 1428*B^6 - 16611*B^5*C +
      106575*B^4*C^2 - 408415*B^3*C^3 + 936390*B^2*C^4 -
      1190553*B*C^5 + 647976*C^6) := by
    simp [seventhThetaSquareCFactor]
    ring
  rw [h]
  push_cast
  rw [show (7 : ZMod 7) = 0 by decide, zero_mul, add_zero]

theorem seventhThetaSquareBFactor_modSeven (A B : ℤ) :
    (seventhThetaSquareBFactor A B : ZMod 7) =
      3 * (A : ZMod 7)^5 := by
  have h : seventhThetaSquareBFactor A B = 3*A^5 + 7 *
      (-5*A^4*B + 25*A^3*B^2 - 66*A^2*B^3 +
        91*A*B^4 - 52*B^5) := by
    simp [seventhThetaSquareBFactor]
    ring
  rw [h]
  push_cast
  rw [show (7 : ZMod 7) = 0 by decide, zero_mul, add_zero]


end DkMath.FLT.Seven.SevenRealCubicInt
