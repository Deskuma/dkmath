/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Two.GaugeCalibration

#print "file: DkMathTest.FLT.Two.GaugeCalibration"

namespace DkMathTest.FLT.Two.GaugeCalibration

open DkMath.FLT.Two
open DkMath.CosmicFormula.PowerGapBeam

def p435 : PrimitiveSquareSolution :=
  { x := 4
    y := 3
    z := 5
    hx := by norm_num
    hy := by norm_num
    hz := by norm_num
    hEq := by norm_num
    hcop := by norm_num }

def p51213 : PrimitiveSquareSolution :=
  { x := 12
    y := 5
    z := 13
    hx := by norm_num
    hy := by norm_num
    hz := by norm_num
    hEq := by norm_num
    hcop := by norm_num }

def p345 : PrimitiveSquareSolution :=
  { x := 3
    y := 4
    z := 5
    hx := by norm_num
    hy := by norm_num
    hz := by norm_num
    hEq := by norm_num
    hcop := by norm_num }

example : Nat.gcd (p435.z - p435.y) (p435.z + p435.y) = 2 := by
  exact primitiveSquareSolution_gap_beam_gcd_eq_two p435 (by norm_num [p435])
    (by norm_num [p435])

example : Nat.gcd (p51213.z - p51213.y) (p51213.z + p51213.y) = 2 := by
  exact primitiveSquareSolution_gap_beam_gcd_eq_two p51213 (by norm_num [p51213])
    (by norm_num [p51213])

example :
    powerGap (3 : ℤ) 5 = 2 ∧ powerBeam 2 (3 : ℤ) 5 = 8 := by
  norm_num [powerGap, powerBeam]

example :
    powerGap (5 : ℤ) 13 = 8 ∧ powerBeam 2 (5 : ℤ) 13 = 18 := by
  norm_num [powerGap, powerBeam]

example :
    (4 : ℤ) ^ 2 = powerGap (3 : ℤ) 5 * powerBeam 2 (3 : ℤ) 5 := by
  exact primitiveSquareSolution_gap_beam_sq p435 (by norm_num [p435])
    (by norm_num [p435])

example :
    (12 : ℤ) ^ 2 = powerGap (5 : ℤ) 13 * powerBeam 2 (5 : ℤ) 13 := by
  exact primitiveSquareSolution_gap_beam_sq p51213 (by norm_num [p51213])
    (by norm_num [p51213])

example : PrimitiveSquareLandingGaugeSplit 4 3 5 := by
  refine ⟨1, 4, 2, 1, 2, ?_⟩
  norm_num [PrimitiveSquareLandingGaugeSplit]

example : PrimitiveSquareLandingGaugeSplit 12 5 13 := by
  refine ⟨4, 9, 6, 2, 3, ?_⟩
  norm_num [PrimitiveSquareLandingGaugeSplit]

example : PrimitiveSquareLandingGaugeSplit p435.x p435.y p435.z := by
  exact primitiveSquareSolution_gauge_split p435 (by norm_num [p435])
    (by norm_num [p435])

example : PrimitiveSquareLandingGaugeSplit p51213.x p51213.y p51213.z := by
  exact primitiveSquareSolution_gauge_split p51213 (by norm_num [p51213])
    (by norm_num [p51213])

example :
    PrimitiveSquareLandingGaugeSplit p345.y p345.x p345.z := by
  exact primitiveSquareSolution_oriented_gauge_split p345 |>.resolve_left (by
    intro h
    rcases h with ⟨A, B, X, r, s, hx, hy, hz, hgap, hbeam, hcop, hx', hbody,
      hA, hB, hgap', hbeam'⟩
    norm_num [p345] at hx)

example :
    ((4 : ℕ) / 2) ^ 2 = 1 * 4 ∧
      ((12 : ℕ) / 2) ^ 2 = 4 * 9 := by
  norm_num

end DkMathTest.FLT.Two.GaugeCalibration
