/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedFusionSmallCoefficientPrimeSupport
import DkMathTest.FLT.Seven.SevenRamifiedFusionCenteredThirteenSupport

#print "file: DkMathTest.FLT.Seven.SevenRamifiedFusionSmallCoefficientPrimeSupport"

namespace DkMathTest.FLT.Seven
open DkMath.FLT.Seven

example {c p n r : ℕ} (hp : Nat.Prime p) (hc : c ≤ 7 ^ 3)
    (hm : r ∈ (c * p ^ n).divisors) (hcop : Nat.Coprime r ((c * p ^ n) / r))
    (hs : 7 ^ 3 * r ^ 7 < c * p ^ n) : ¬ p ∣ r :=
  eligible_primitive_divisor_smallCoefficient_prime_not_dvd hp hc hm hcop hs
example {c p n r : ℕ} (hp : Nat.Prime p) (hc : c ≤ 7 ^ 3) (hn : 0 < n)
    (hm : r ∈ (c * p ^ n).divisors) (hcop : Nat.Coprime r ((c * p ^ n) / r))
    (hs : 7 ^ 3 * r ^ 7 < c * p ^ n) : ¬ p ∣ r ∧ p ∣ (c * p ^ n) / r :=
  eligible_smallCoefficient_prime_in_complement hp hc hn hm hcop hs

example (n : ℕ) (hn : 0 < n) : ¬ SixthPowerSievedNestedCondition (1 * 13 ^ n) :=
  sixthPowerSieved_smallCoefficient_thirteen_pow_excluded (by decide) hn
example (n : ℕ) (hn : 0 < n) : ¬ SixthPowerSievedNestedCondition (3 * 13 ^ n) :=
  sixthPowerSieved_smallCoefficient_thirteen_pow_excluded (by decide) hn
example (n : ℕ) (hn : 0 < n) : ¬ SixthPowerSievedNestedCondition (13 * 13 ^ n) :=
  sixthPowerSieved_smallCoefficient_thirteen_pow_excluded (by decide) hn
example (n : ℕ) (hn : 0 < n) : ¬ SixthPowerSievedNestedCondition (343 * 13 ^ n) :=
  sixthPowerSieved_smallCoefficient_thirteen_pow_excluded (by decide) hn
example (n : ℕ) (hn : 0 < n) : ¬ SixthPowerSievedNestedCondition (0 * 13 ^ n) :=
  sixthPowerSieved_smallCoefficient_thirteen_pow_excluded (by decide) hn

example : ¬ SixthPowerSievedNestedCondition (3 * 13 ^ 12) :=
  sixthPowerSieved_smallCoefficient_thirteen_pow_excluded (by decide) (by decide)

/-- The earlier fixed-divisor filter passage coexists with whole-core exclusion. -/
theorem priorPassage_and_coreExclusion :
    ModFortyTwoCheapAllocation (3 * 13 ^ 12) 3 ∧
    SixthPowerAllocationSieve 3 ((3 * 13 ^ 12) / 3) ∧
    ¬ SixthPowerSievedNestedCondition (3 * 13 ^ 12) :=
  ⟨allocationThree_thirteenSupport_regression.1,
    allocationThree_thirteenSupport_regression.2.1,
    sixthPowerSieved_smallCoefficient_thirteen_pow_excluded (by decide) (by decide)⟩

/-- Coefficient ownership alone cannot establish prime avoidance. -/
theorem coefficientDivisibility_countermodel :
    Nat.Prime 13 ∧ 13 ≤ (7 : ℕ) ^ 3 ∧ 13 ∣ (13 : ℕ) ∧ ¬ (¬ 13 ∣ (13 : ℕ)) := by
  decide

/-- This genuinely eligible divisor has a coefficient already divisible by13. -/
theorem coefficientThirteen_eligible_support :
    1 ∈ (13 * 13 ^ 2 : ℕ).divisors ∧
    Nat.Coprime 1 ((13 * 13 ^ 2) / 1) ∧
    7 ^ 3 * 1 ^ 7 < 13 * 13 ^ 2 ∧
    ¬ 13 ∣ (1 : ℕ) ∧ 13 ∣ (13 * 13 ^ 2) / 1 := by
  have hm : 1 ∈ (13 * 13 ^ 2 : ℕ).divisors := by decide
  have hcop : Nat.Coprime 1 ((13 * 13 ^ 2) / 1) := by decide
  have hs : 7 ^ 3 * 1 ^ 7 < 13 * 13 ^ 2 := by decide
  exact ⟨hm, hcop, hs, eligible_smallCoefficient_prime_in_complement
    (by decide) (by decide) (by decide) hm hcop hs⟩

example {p r : ℕ} (hp : Nat.Prime p) (hm : r ∈ (0 * p ^ 0).divisors)
    (hcop : Nat.Coprime r ((0 * p ^ 0) / r))
    (hs : 7 ^ 3 * r ^ 7 < 0 * p ^ 0) : ¬ p ∣ r :=
  eligible_primitive_divisor_smallCoefficient_prime_not_dvd hp (by decide) hm hcop hs

#print axioms DkMath.FLT.Seven.eligible_primitive_divisor_smallCoefficient_prime_not_dvd
#print axioms DkMath.FLT.Seven.eligible_smallCoefficient_prime_in_complement
#print axioms DkMath.FLT.Seven.sixthPowerSieved_smallCoefficient_thirteen_pow_excluded
#print axioms DkMathTest.FLT.Seven.priorPassage_and_coreExclusion
#print axioms DkMathTest.FLT.Seven.coefficientDivisibility_countermodel
#print axioms DkMathTest.FLT.Seven.coefficientThirteen_eligible_support
end DkMathTest.FLT.Seven
