/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedFusionPrimePowerPrimitiveExclusion
import DkMathTest.FLT.Seven.SevenRamifiedFusionThirteenPowerPrimitiveExclusion

#print "file: DkMathTest.FLT.Seven.SevenRamifiedFusionPrimePowerPrimitiveExclusion"

namespace DkMathTest.FLT.Seven
open DkMath.FLT.Seven

example {p n r : ℕ} (hp : Nat.Prime p) (hm : r ∈ (2 * p ^ n).divisors)
    (hc : Nat.Coprime r ((2 * p ^ n) / r)) (hs : 7 ^ 3 * r ^ 7 < 2 * p ^ n) :
    r = 1 ∨ r = 2 := eligible_primitive_divisor_two_prime_pow hp hm hc hs
example {p n : ℕ} (hp : Nat.Prime p) (h42 : Nat.ModEq 42 (p ^ n) 1)
    (h5 : Nat.ModEq 5 (p ^ n) 4) : ¬ SixthPowerSievedNestedCondition (2 * p ^ n) :=
  sixthPowerSieved_two_prime_pow_excluded hp h42 h5

-- Reuse only the small residue calculations from gate011; structure is generic.
example (k : ℕ) : ¬ SixthPowerSievedNestedCondition (2 * 13 ^ (6 + 4 * k)) := by
  apply sixthPowerSieved_two_prime_pow_excluded (by decide : Nat.Prime 13)
  · have h := (show Nat.ModEq 42 (13 ^ 2) 1 by decide).pow (3 + 2 * k)
    simpa only [← pow_mul, one_pow, show 2 * (3 + 2*k) = 6 + 4*k by omega] using h
  · have h := (show Nat.ModEq 5 (13 ^ 6) 4 by decide).mul
      ((show Nat.ModEq 5 (13 ^ 4) 1 by decide).pow k)
    simpa only [one_pow, mul_one, ← pow_mul, ← pow_add] using h

example : Nat.Prime 223 ∧ Nat.ModEq 42 (223 ^ 2) 1 ∧
    Nat.ModEq 5 (223 ^ 2) 4 ∧ 2 * 223 ^ 2 = (99458 : ℕ) := by norm_num [Nat.ModEq]
example : ¬ SixthPowerSievedNestedCondition 99458 :=
  sixthPowerSieved_two_prime_pow_excluded (by norm_num : Nat.Prime 223)
    (by decide : Nat.ModEq 42 (223 ^ 2) 1) (by decide : Nat.ModEq 5 (223 ^ 2) 4)
example : 2 ∈ (99458 : ℕ).divisors ∧ Nat.Coprime 2 (99458 / 2) ∧
    7 ^ 3 * 2 ^ 7 < 99458 := by
  refine ⟨?_, by decide, by decide⟩
  norm_num [Nat.mem_divisors]

-- The guard countermodel is reused, not recomputed.
example : 13 ∈ (2 * 13 ^ 10 : ℕ).divisors ∧
    7 ^ 3 * 13 ^ 7 < 2 * 13 ^ 10 ∧ ¬ (13 = 1 ∨ 13 = (2 : ℕ)) ∧
    ¬ Nat.Coprime 13 ((2 * 13 ^ 10) / 13) := coprimality_guard_countermodel

-- Multiple distinct prime bases allow a primitive factor other than one or two.
example : 3 ∈ (2 * (3 * 5 ^ 10) : ℕ).divisors ∧
    Nat.Coprime 3 ((2 * (3 * 5 ^ 10)) / 3) ∧
    7 ^ 3 * 3 ^ 7 < 2 * (3 * 5 ^ 10) ∧ ¬ (3 = 1 ∨ 3 = (2 : ℕ)) := by
  refine ⟨?_, by decide, by decide, by decide⟩
  norm_num [Nat.mem_divisors]

#print axioms DkMath.FLT.Seven.eligible_primitive_divisor_two_prime_pow
#print axioms DkMath.FLT.Seven.sixthPowerSieved_two_prime_pow_excluded
end DkMathTest.FLT.Seven
