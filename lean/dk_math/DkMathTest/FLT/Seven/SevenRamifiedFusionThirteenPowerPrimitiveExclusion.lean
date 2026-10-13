/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedFusionThirteenPowerPrimitiveExclusion

#print "file: DkMathTest.FLT.Seven.SevenRamifiedFusionThirteenPowerPrimitiveExclusion"

namespace DkMathTest.FLT.Seven
open DkMath.FLT.Seven

example (n : ℕ) {r : ℕ} (hm : r ∈ (2 * 13 ^ n).divisors)
    (hc : Nat.Coprime r ((2 * 13 ^ n) / r)) (hs : 7 ^ 3 * r ^ 7 < 2 * 13 ^ n) :
    r = 1 ∨ r = 2 := eligible_primitive_divisor_two_thirteen_pow n hm hc hs
example (k : ℕ) : ¬ SixthPowerSievedNestedCondition (2 * 13 ^ (6 + 4 * k)) :=
  sixthPowerSieved_thirteen_power_family_excluded k

/-- Natural indices give distinct core values, so this is an infinite family. -/
theorem thirteenPowerCore_injective : Function.Injective (fun k : ℕ => 2 * 13 ^ (6 + 4 * k)) := by
  intro a b h
  change 2 * 13 ^ (6 + 4 * a) = 2 * 13 ^ (6 + 4 * b) at h
  have he := Nat.pow_right_injective (by decide : 2 ≤ 13)
    (Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) h)
  omega

/-- Membership and size alone allow r=13; the primitive guard really matters. -/
theorem coprimality_guard_countermodel :
    13 ∈ (2 * 13 ^ 10 : ℕ).divisors ∧
    7 ^ 3 * 13 ^ 7 < 2 * 13 ^ 10 ∧ ¬ (13 = 1 ∨ 13 = (2 : ℕ)) ∧
    ¬ Nat.Coprime 13 ((2 * 13 ^ 10) / 13) := by
  refine ⟨?_, by decide, by decide, by decide⟩
  norm_num [Nat.mem_divisors]

example : 2 * 13 ^ (6 + 4 * 0) = (9653618 : ℕ) := by decide
example : ¬ SixthPowerSievedNestedCondition 9653618 :=
  sixthPowerSieved_thirteen_power_family_excluded 0
example : ¬ SixthPowerSievedNestedCondition (2 * 13 ^ 10) :=
  sixthPowerSieved_thirteen_power_family_excluded 1
example : ¬ SixthPowerSievedNestedCondition (2 * 13 ^ 14) :=
  sixthPowerSieved_thirteen_power_family_excluded 2

#print axioms DkMath.FLT.Seven.eligible_primitive_divisor_two_thirteen_pow
#print axioms DkMath.FLT.Seven.sixthPowerSieved_thirteen_power_family_excluded
#print axioms DkMathTest.FLT.Seven.thirteenPowerCore_injective
#print axioms DkMathTest.FLT.Seven.coprimality_guard_countermodel
end DkMathTest.FLT.Seven
