/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.Triple
import DkMath.ABC.SquareTailBasic

#print "file: DkMath.ABC.SquareTailGapIdentity"

namespace DkMath.ABC

/-- In a coprime additive triple, the left coordinate is coprime to the sum. -/
theorem Triple.coprime_a_c (T : Triple) :
    Nat.Coprime T.a T.c := by
  rw [← T.hsum]
  simpa [Nat.add_comm] using
    (Nat.coprime_add_self_right).2 T.hcop

/-- In a coprime additive triple, the right coordinate is coprime to the sum. -/
theorem Triple.coprime_b_c (T : Triple) :
    Nat.Coprime T.b T.c := by
  rw [← T.hsum]
  exact ((Nat.coprime_add_self_left).2 T.hcop).symm

/-- The input product `ab` is coprime to the output `c`. -/
theorem Triple.coprime_ab_c (T : Triple) :
    Nat.Coprime (T.a * T.b) T.c := by
  exact Nat.Coprime.mul_left T.coprime_a_c T.coprime_b_c

/-- The radical of an ABC product splits exactly between `ab` and `c`. -/
theorem Triple.rad_abc_eq_rad_ab_mul_rad_c (T : Triple) :
    rad (T.a * T.b * T.c) =
      rad (T.a * T.b) * rad T.c := by
  exact rad_mul_coprime T.coprime_ab_c

/--
Exact square-tail/radical balance for a coprime additive triple.

This is the denominator-free form of

`c / rad(abc) = sqTail(c) / rad(ab)`.
-/
theorem Triple.c_mul_rad_ab_eq_sqTail_mul_rad_abc
    (T : Triple)
    (hc : T.c ≠ 0) :
    T.c * rad (T.a * T.b) =
      sqTail T.c * rad (T.a * T.b * T.c) := by
  rw [T.rad_abc_eq_rad_ab_mul_rad_c]
  conv_lhs => rw [nat_eq_sqTail_mul_rad T.c hc]
  -- nth_rewrite 1 [nat_eq_sqTail_mul_rad T.c hc]  -- alternative
  ac_rfl

-- Real ---------------------------------------------------

/-- `rad n` は常に 0 ではない。`rad 0 = 1` も含む。 -/
lemma rad_ne_zero (n : ℕ) : rad n ≠ 0 := by
  unfold rad
  rw [Nat.support_factorization, Finset.prod_ne_zero_iff]
  intro p hp
  exact (Nat.prime_of_mem_primeFactors hp).ne_zero

/-- Triple.c_div_rad_abc_eq_sqTail_div_rad_ab の証明 -/
theorem Triple.c_div_rad_abc_eq_sqTail_div_rad_ab
    (T : Triple)
    (hc : T.c ≠ 0) :
    (T.c : ℝ) / (rad (T.a * T.b * T.c) : ℝ) =
      (sqTail T.c : ℝ) / (rad (T.a * T.b) : ℝ) := by
  apply
    (div_eq_div_iff
      (Nat.cast_ne_zero.mpr
        (rad_ne_zero (T.a * T.b * T.c)))
      (Nat.cast_ne_zero.mpr
        (rad_ne_zero (T.a * T.b)))).2
  exact_mod_cast
    T.c_mul_rad_ab_eq_sqTail_mul_rad_abc hc

end DkMath.ABC
