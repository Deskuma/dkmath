/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedFusionPermutationPrimeSupport

#print "file: DkMathTest.FLT.Seven.SevenRamifiedFusionPermutationPrimeSupport"

namespace DkMathTest.FLT.Seven
open DkMath.FLT.Seven

example {R : Type*} [CommRing R] (D q : ℕ) :
    ((q : R) + D) ^ 7 - ((q : R) - D) ^ 7 =
      2 * (D : R) * (centeredSevenSextic D q : R) :=
  centeredSevenSextic_cast_difference D q
example : Function.Injective (fun x : ZMod 11 => x ^ 7) :=
  zmod_seventh_power_injective (by decide) (by decide)
example {D q : ℕ} (hd : ¬ 13 ∣ D) : ¬ 13 ∣ centeredSevenSextic D q :=
  centeredSevenSextic_not_dvd_of_seven_power_permutation (by decide) (by decide) (by decide) hd
example {D q : ℕ} (hd : ¬ 11 ∣ D) : ¬ 11 ∣ centeredSevenSextic D q :=
  centeredSevenSextic_not_dvd_of_seven_power_permutation (by decide) (by decide) (by decide) hd
example : ¬ (NestedGNAllocationCondition 11 1 ∨ NestedRHSAllocationCondition 11 1) :=
  nestedAllocation_excluded_of_permutation_prime_support
    (ℓ := 11) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
example {c n : ℕ} (hc : c ≤ 7 ^ 3) (hn : 0 < n) :
    ¬ SixthPowerSievedNestedCondition (c * 11 ^ n) :=
  sixthPowerSieved_smallCoefficient_permutation_prime_excluded
    (by decide) (by decide) (by decide) (by decide) hc hn
example {c n : ℕ} (hc : c ≤ 7 ^ 3) (hn : 0 < n) :
    ¬ SixthPowerSievedNestedCondition (c * 13 ^ n) :=
  sixthPowerSieved_smallCoefficient_permutation_prime_excluded
    (by decide) (by decide) (by decide) (by decide) hc hn

/-- Odd primes alone do not guarantee a nonzero sextic image. -/
theorem twentyNine_countermodel :
    Nat.Prime 29 ∧ (29 : ℕ) ≠ 2 ∧ ¬ 29 ∣ (1 : ℕ) ∧
    29 ∣ centeredSevenSextic 1 5 ∧ ¬ Nat.Coprime 7 (29 - 1) := by
  decide

/-- Characteristic2 invalidates the unit-gap nonvanishing conclusion. -/
theorem two_countermodel :
    Nat.Prime 2 ∧ Nat.Coprime 7 (2 - 1) ∧ ¬ 2 ∣ (1 : ℕ) ∧
    centeredSevenSextic 1 1 = 64 ∧ 2 ∣ centeredSevenSextic 1 1 := by
  decide

/-- Modulus7 meets the polynomial criterion, but the actual receiver gap is not a unit. -/
theorem seven_gap_support_diagnostic :
    Nat.Prime 7 ∧ Nat.Coprime 7 (7 - 1) ∧ ¬ 7 ∣ (1 : ℕ) ∧
    7 ∣ (7 ^ 27 * 1 ^ 49 : ℕ) := by
  decide

#print axioms DkMath.FLT.Seven.zmod_seventh_power_injective
#print axioms DkMath.FLT.Seven.centeredSevenSextic_cast_difference
#print axioms DkMath.FLT.Seven.centeredSevenSextic_not_dvd_of_seven_power_permutation
#print axioms DkMath.FLT.Seven.nestedAllocation_excluded_of_permutation_prime_support
#print axioms DkMath.FLT.Seven.sixthPowerSieved_smallCoefficient_permutation_prime_excluded
#print axioms DkMathTest.FLT.Seven.twentyNine_countermodel
#print axioms DkMathTest.FLT.Seven.two_countermodel
#print axioms DkMathTest.FLT.Seven.seven_gap_support_diagnostic
end DkMathTest.FLT.Seven
