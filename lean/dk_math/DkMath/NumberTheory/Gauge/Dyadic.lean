/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CosmicFormula.HalfUnitZeroConjugate
import DkMath.CosmicFormula.PowerGapBeam

#print "file: DkMath.NumberTheory.Gauge.Dyadic"

/-!
# Dyadic midpoint gauge

This module records the division-free midpoint defect attached to the
endpoint pair `x` and `x + u`.  It is deliberately a small low-degree
calibration layer: it does not assert an FLT statement or introduce a
general exponent hierarchy.
-/

namespace DkMath.NumberTheory.Gauge

/-! ## Division-free scaled defect -/

/-- The division-free scaled midpoint defect for exponent `d`. -/
def scaledMidpointDefect {R : Type*} [CommRing R]
    (d : ℕ) (x u : R) : R :=
  (2 : R) ^ (d - 1) * ((x + u) ^ d - x ^ d)
    - (d : R) * u * (2 * x + u) ^ (d - 1)

/-- The quadratic midpoint defect vanishes identically. -/
theorem scaledMidpointDefect_two {R : Type*} [CommRing R] (x u : R) :
    scaledMidpointDefect 2 x u = 0 := by
  unfold scaledMidpointDefect
  ring

/-- The cubic midpoint defect is the unit cube. -/
theorem scaledMidpointDefect_three {R : Type*} [CommRing R] (x u : R) :
    scaledMidpointDefect 3 x u = u ^ 3 := by
  unfold scaledMidpointDefect
  ring

/-- The quartic midpoint defect is the displayed cubic correction. -/
theorem scaledMidpointDefect_four {R : Type*} [CommRing R] (x u : R) :
    scaledMidpointDefect 4 x u = 4 * u ^ 3 * (2 * x + u) := by
  unfold scaledMidpointDefect
  ring

/-! ## Half-unit square identity -/

/-- The midpoint square identity over a characteristic-zero field. -/
theorem midpointSquareIdentity {K : Type*} [Field K] [CharZero K]
    (x u : K) :
    (x + u) ^ 2 - x ^ 2 = 2 * u * (x + u / 2) := by
  ring

/-- The same identity expressed using the existing real half-unit API. -/
theorem midpointSquareIdentity_real_halfUnit (x u : ℝ) :
    (x + u) ^ 2 - x ^ 2 =
      2 * u * (x + DkMath.CosmicFormula.HalfUnitZeroConjugate.halfUnit u) := by
  unfold DkMath.CosmicFormula.HalfUnitZeroConjugate.halfUnit
  ring

/-! ## Thin PowerGapBeam endpoint bridges -/

open DkMath.CosmicFormula.PowerGapBeam

/-- The gap of the endpoints `x` and `x + u` is `u`. -/
theorem powerGap_self_add {R : Type*} [CommRing R] (x u : R) :
    powerGap x (x + u) = u := by
  rw [powerGap_eq_sub]
  ring

/-- The quadratic beam of the endpoints `x` and `x + u` is `2 * x + u`. -/
theorem powerBeam_two_self_add {R : Type*} [CommRing R] (x u : R) :
    powerBeam 2 x (x + u) = 2 * x + u := by
  rw [powerBeam_two]
  ring

/-- The existing gap-beam factorization at the midpoint endpoints. -/
theorem midpointSquareDifference_eq_gap_mul_beam {R : Type*} [CommRing R]
    (x u : R) :
    (x + u) ^ 2 - x ^ 2 =
      powerGap x (x + u) * powerBeam 2 x (x + u) := by
  exact pow_sub_pow_eq_gap_mul_powerBeam 2 x (x + u)

/-- The gap-beam factorization reduced to the endpoint increment. -/
theorem midpointSquareDifference_eq_increment_beam {R : Type*} [CommRing R]
    (x u : R) :
    (x + u) ^ 2 - x ^ 2 = u * (2 * x + u) := by
  calc
    (x + u) ^ 2 - x ^ 2 =
        powerGap x (x + u) * powerBeam 2 x (x + u) :=
      midpointSquareDifference_eq_gap_mul_beam x u
    _ = u * (2 * x + u) := by
      rw [powerGap_self_add, powerBeam_two_self_add]

end DkMath.NumberTheory.Gauge

#print axioms DkMath.NumberTheory.Gauge.scaledMidpointDefect_two
#print axioms DkMath.NumberTheory.Gauge.scaledMidpointDefect_three
#print axioms DkMath.NumberTheory.Gauge.scaledMidpointDefect_four
#print axioms DkMath.NumberTheory.Gauge.midpointSquareIdentity
#print axioms DkMath.NumberTheory.Gauge.midpointSquareIdentity_real_halfUnit
#print axioms DkMath.NumberTheory.Gauge.powerGap_self_add
#print axioms DkMath.NumberTheory.Gauge.powerBeam_two_self_add
#print axioms DkMath.NumberTheory.Gauge.midpointSquareDifference_eq_gap_mul_beam
#print axioms DkMath.NumberTheory.Gauge.midpointSquareDifference_eq_increment_beam
