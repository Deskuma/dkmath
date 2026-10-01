/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Gauge.Landing
import DkMath.FLT.Two.GaugeCalibration
import DkMath.FLT.Three
import DkMath.FLT.Five
import DkMath.FLT.Prime.PrimeGaugeBridge

#print "file: DkMath.FLT.GaugeLandingCalibration"

/-!
# FLT-side landing calibration

This module connects the neutral landing predicates to the completed
exponent-two, exponent-three, exponent-five, and prime-gauge APIs.  It does
not feed any FLT-specific result back into the public NumberTheory.Gauge
facade and it does not claim terminal additive non-landing at exponent seven.
-/

namespace DkMath.FLT

open DkMath.NumberTheory.Gauge
open DkMath.FLT.Two

/-! ## Exponent two -/

/-- A primitive positive square solution is a positive additive landing. -/
theorem primitiveSquareSolution_positiveAdditiveLanding
    (P : PrimitiveSquareSolution) :
    PositiveAdditiveLanding 2 P.x P.y :=
  ⟨P.z, P.hx, P.hy, P.hz, P.hEq⟩

/-- The exponent-two landing and the existing oriented gauge split coexist. -/
theorem primitiveSquareSolution_landing_and_oriented_gauge_split
    (P : PrimitiveSquareSolution) :
    PositiveAdditiveLanding 2 P.x P.y ∧
      (PrimitiveSquareLandingGaugeSplit P.x P.y P.z ∨
        PrimitiveSquareLandingGaugeSplit P.y P.x P.z) :=
  ⟨primitiveSquareSolution_positiveAdditiveLanding P,
    primitiveSquareSolution_oriented_gauge_split P⟩

/-! ## Completed positive non-landing endpoints -/

/-- The completed exponent-three endpoint excludes every positive landing. -/
theorem not_positiveAdditiveLanding_three (x y : ℕ) :
    ¬ PositiveAdditiveLanding 3 x y := by
  intro h
  rcases h with ⟨z, hx, hy, hz, hEq⟩
  exact DkMath.FLT.Three.fermatThree_no_positive_solution x y z hx hy hz hEq

/-- The completed exponent-five endpoint excludes every positive landing. -/
theorem not_positiveAdditiveLanding_five (x y : ℕ) :
    ¬ PositiveAdditiveLanding 5 x y := by
  intro h
  rcases h with ⟨z, hx, hy, hz, hEq⟩
  apply DkMath.FLT.Five.fermatFive_no_positive_solution x y z hx hy hz
  exact hEq

/-! ## Exponent seven boundary -/

/-- The p=7 exponent gauge is available; this is not an additive theorem. -/
theorem primeExponentGauge_seven_boundary :
    PrimeExponentGauge 7 :=
  primeExponentGauge_of_prime (by norm_num)

end DkMath.FLT

#print axioms DkMath.FLT.primitiveSquareSolution_positiveAdditiveLanding
#print axioms DkMath.FLT.primitiveSquareSolution_landing_and_oriented_gauge_split
#print axioms DkMath.FLT.not_positiveAdditiveLanding_three
#print axioms DkMath.FLT.not_positiveAdditiveLanding_five
#print axioms DkMath.FLT.primeExponentGauge_seven_boundary
