/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.GaugeLandingCalibration

#print "file: DkMathTest.FLT.GaugeLandingCalibration"

namespace DkMathTest.FLT.GaugeLandingCalibration

open DkMath.FLT
open DkMath.FLT.Two
open DkMath.NumberTheory.Gauge

def p345 : PrimitiveSquareSolution :=
  { x := 3
    y := 4
    z := 5
    hx := by norm_num
    hy := by norm_num
    hz := by norm_num
    hEq := by norm_num
    hcop := by norm_num }

example : PositiveAdditiveLanding 2 3 4 := by
  exact primitiveSquareSolution_positiveAdditiveLanding p345

example :
    PositiveAdditiveLanding 2 p345.x p345.y ∧
      (PrimitiveSquareLandingGaugeSplit p345.x p345.y p345.z ∨
        PrimitiveSquareLandingGaugeSplit p345.y p345.x p345.z) := by
  exact primitiveSquareSolution_landing_and_oriented_gauge_split p345

example (x y : ℕ) : ¬ PositiveAdditiveLanding 3 x y :=
  not_positiveAdditiveLanding_three x y

example (x y : ℕ) : ¬ PositiveAdditiveLanding 5 x y :=
  not_positiveAdditiveLanding_five x y

example : ¬ PositiveAdditiveLanding 3 3 4 := by
  exact not_positiveAdditiveLanding_three 3 4

example : ¬ PositiveAdditiveLanding 5 3 4 := by
  exact not_positiveAdditiveLanding_five 3 4

example : PrimeExponentGauge 7 :=
  primeExponentGauge_seven_boundary

example : PrimeExponentGauge 7 ∧
    DkMath.NumberTheory.Gauge.PrimeExponentGauge 7 := by
  exact ⟨primeExponentGauge_seven_boundary, primeExponentGauge_seven_boundary⟩

end DkMathTest.FLT.GaugeLandingCalibration
