/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedFusionSmallCoefficientPrimePowerOwnership

#print "file: DkMathTest.FLT.Seven.SevenRamifiedFusionSmallCoefficientPrimePowerOwnership"

namespace DkMathTest.FLT.Seven
open DkMath.FLT.Seven

example {c p n r : ℕ} (hp : Nat.Prime p) (hc : c ≤ 7 ^ 3)
    (hm : r ∈ (c * p ^ n).divisors) (hcop : Nat.Coprime r ((c * p ^ n) / r))
    (hs : 7 ^ 3 * r ^ 7 < c * p ^ n) : r ∣ c :=
  eligible_primitive_divisor_smallCoefficient_prime_pow hp hc hm hcop hs

example {p n r : ℕ} (hp : Nat.Prime p) (hm : r ∈ (0 * p ^ n).divisors)
    (hcop : Nat.Coprime r ((0 * p ^ n) / r))
    (hs : 7 ^ 3 * r ^ 7 < 0 * p ^ n) : r ∣ 0 :=
  eligible_primitive_divisor_smallCoefficient_prime_pow hp (by decide) hm hcop hs

example {c p r : ℕ} (hp : Nat.Prime p) (hc : c ≤ 7 ^ 3)
    (hm : r ∈ (c * p ^ 0).divisors) (hcop : Nat.Coprime r ((c * p ^ 0) / r))
    (hs : 7 ^ 3 * r ^ 7 < c * p ^ 0) : r ∣ c :=
  eligible_primitive_divisor_smallCoefficient_prime_pow hp hc hm hcop hs

example (n : ℕ) (hn : 0 < n) :
    ¬ SixthPowerSievedNestedCondition (3 * 13 ^ n) :=
  sixthPowerSieved_three_thirteen_pow_excluded hn
example (k : ℕ) : ¬ SixthPowerSievedNestedCondition (3 * 13 ^ (k + 1)) :=
  sixthPowerSieved_three_thirteen_power_family_excluded k
example : Function.Injective (fun k : ℕ => 3 * 13 ^ (k + 1)) :=
  threeThirteenPowerCore_injective
example : ¬ SixthPowerSievedNestedCondition (3 * 13 ^ 12) :=
  sixthPowerSieved_three_thirteen_pow_excluded (by decide)
example : ¬ SixthPowerSievedNestedCondition (3 * 13 ^ 1) :=
  sixthPowerSieved_three_thirteen_pow_excluded (by decide)

/-- Removing the coefficient bound makes the proposed ownership conclusion false. -/
theorem coefficientBound_countermodel :
    Nat.Prime 2 ∧ 2 ∈ (21953 * 2 ^ 1 : ℕ).divisors ∧
    Nat.Coprime 2 ((21953 * 2 ^ 1) / 2) ∧
    7 ^ 3 * 2 ^ 7 < 21953 * 2 ^ 1 ∧ ¬ (2 ∣ (21953 : ℕ)) := by
  decide

#print axioms DkMath.FLT.Seven.eligible_primitive_divisor_smallCoefficient_prime_pow
#print axioms DkMath.FLT.Seven.sixthPowerSieved_three_thirteen_pow_excluded
#print axioms DkMath.FLT.Seven.threeThirteenPowerCore_injective
#print axioms DkMath.FLT.Seven.sixthPowerSieved_three_thirteen_power_family_excluded
#print axioms DkMathTest.FLT.Seven.coefficientBound_countermodel
end DkMathTest.FLT.Seven
