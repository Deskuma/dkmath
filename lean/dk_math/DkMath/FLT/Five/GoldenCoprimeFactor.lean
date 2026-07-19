/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Five.GoldenEuclidean
import DkMath.FLT.Five.SignedGoldenFifthPower

#print "file: DkMath.FLT.Five.GoldenCoprimeFactor"

namespace DkMath.FLT.Five

/-- The explicit golden-unit predicate agrees with the standard ring predicate. -/
theorem goldenUnit_iff_isUnit {x : GoldenInt} : GoldenUnit x ↔ IsUnit x := by
  constructor
  · rintro ⟨y, hxy, _⟩
    apply isUnit_iff_exists_inv.mpr
    exact ⟨y, by simpa using hxy⟩
  · intro hx
    rcases isUnit_iff_exists_inv.mp hx with ⟨y, hxy⟩
    refine ⟨y, by simpa using hxy, ?_⟩
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

/-- The cp-004f signed golden core now follows without an extra factorization axiom. -/
theorem signedGoldenFifthPowerUpToUnitCore : SignedGoldenFifthPowerUpToUnitCore :=
  signedGoldenFifthPowerUpToUnitCore_of_coprimeFactor
    goldenCoprimeFactorOfFifthPower

end DkMath.FLT.Five
