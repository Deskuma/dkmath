/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Five.GoldenEuclidean
import DkMath.FLT.Five.SignedGoldenFifthPower

#print "file: DkMath.FLT.Five.GoldenCoprimeFactor"

namespace DkMath.FLT.Five

/-!
# Coprime factors of a fifth power

The norm-Euclidean structure supplies a gcd monoid on `GoldenInt`.  Consequently, if
`x*y=z^5` and every common divisor of `x,y` is a unit, unique factorization gives
`x=epsilon*gamma^5` for a unit `epsilon`.  This is the algebraic extraction consumed by
the finite unit-class layer; it introduces no FLT-specific assumption.
-/

/-- The explicit golden-unit predicate agrees with the standard ring predicate. -/
theorem goldenUnit_iff_isUnit {x : GoldenInt} : GoldenUnit x ↔ IsUnit x := by
  constructor
  · rintro ⟨y, hxy, _⟩
    apply isUnit_iff_exists_inv.mpr
    refine ⟨y, ?_⟩
    change goldenMul x y = goldenOne
    exact hxy
  · intro hx
    rcases isUnit_iff_exists_inv.mp hx with ⟨y, hxy⟩
    refine ⟨y, ?_, ?_⟩
    · change goldenMul x y = goldenOne
      exact hxy
    · change goldenMul y x = goldenOne
      change y * x = 1
      simpa [mul_comm] using hxy

/-- Coprime factors of a fifth power in the golden integers are fifth powers up to a unit. -/
theorem goldenCoprimeFactorOfFifthPower : GoldenCoprimeFactorOfFifthPower := by
  intro x y z hrel hpow
  letI : GCDMonoid GoldenInt := EuclideanDomain.gcdMonoid GoldenInt
  have hgcd : IsUnit (gcd x y) := by
    rw [← goldenUnit_iff_isUnit]
    apply hrel (gcd x y)
    · rw [goldenDivides_iff_dvd]
      exact gcd_dvd_left x y
    · rw [goldenDivides_iff_dvd]
      exact gcd_dvd_right x y
  obtain ⟨gamma, u, hu⟩ :=
    exists_associated_pow_of_mul_eq_pow hgcd (by simpa using hpow)
  refine ⟨(u : GoldenInt), gamma, goldenUnit_iff_isUnit.mpr u.isUnit, ?_⟩
  simpa [golden_mul_eq, golden_pow_eq, mul_comm] using hu.symm

/-- Every ramifier-stripped FLT5 packet therefore factors as a unit times a fifth power. -/
theorem signedGoldenFifthPowerUpToUnitCore : SignedGoldenFifthPowerUpToUnitCore :=
  signedGoldenFifthPowerUpToUnitCore_of_coprimeFactor
    goldenCoprimeFactorOfFifthPower

end DkMath.FLT.Five
