/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Gauge

#print "file: DkMathTest.NumberTheory.Gauge.Dyadic"

namespace DkMathTest.NumberTheory.Gauge.Dyadic

open DkMath.NumberTheory.Gauge
open DkMath.CosmicFormula.PowerGapBeam

example (x u : ℤ) : scaledMidpointDefect 2 x u = 0 :=
  scaledMidpointDefect_two x u

example (x u : ℤ) : scaledMidpointDefect 3 x u = u ^ 3 :=
  scaledMidpointDefect_three x u

example (x u : ℤ) :
    scaledMidpointDefect 4 x u = 4 * u ^ 3 * (2 * x + u) :=
  scaledMidpointDefect_four x u

example : scaledMidpointDefect 3 (1 : ℤ) 1 = 1 := by
  norm_num [scaledMidpointDefect]

example : scaledMidpointDefect 4 (1 : ℤ) 1 = 12 := by
  norm_num [scaledMidpointDefect]

example (x u : ℚ) :
    (x + u) ^ 2 - x ^ 2 = 2 * u * (x + u / 2) :=
  midpointSquareIdentity x u

example :
    ((3 : ℚ) + 4) ^ 2 - 3 ^ 2 = 2 * 4 * (3 + 4 / 2) := by
  norm_num

example (x u : ℤ) : powerGap x (x + u) = u :=
  powerGap_self_add x u

example (x u : ℤ) : powerBeam 2 x (x + u) = 2 * x + u :=
  powerBeam_two_self_add x u

example (x u : ℤ) :
    (x + u) ^ 2 - x ^ 2 = u * (2 * x + u) :=
  midpointSquareDifference_eq_increment_beam x u

example :
    ((3 : ℝ) + 4) ^ 2 - 3 ^ 2 =
      2 * 4 * (3 + DkMath.CosmicFormula.HalfUnitZeroConjugate.halfUnit 4) := by
  exact midpointSquareIdentity_real_halfUnit 3 4

end DkMathTest.NumberTheory.Gauge.Dyadic
