/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.GapFocusing.PrimeOrder

#print "file: DkMathTest.NumberTheory.GapFocusingPrimeOrder"

namespace DkMathTest.NumberTheory.GapFocusingPrimeOrder

open DkMath.NumberTheory.GapFocusing DkMath.Zsigmondy

/-- The prime three has first power-difference degree two for the base two. -/
theorem base_two_order_mod_three : primeOrder 3 2 1 = 2 := by
  apply (primitivePrimeDivisor_iff_primeOrder_eq (by norm_num) (by norm_num)
    (by norm_num)).mp
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro m hmpos hmlt
  interval_cases m
  norm_num

/-- A primitive prime with higher valuation still has order equal to its degree. -/
theorem primitive_seven_order_three : primeOrder 7 5 3 = 3 := by
  let : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  apply (primitivePrimeDivisor_iff_primeOrder_eq (by norm_num) (by norm_num)
    (by norm_num)).mp
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro m hmpos hmlt
  interval_cases m <;> norm_num

/-- The integer bridge accepts signed coordinates. -/
theorem signed_ratio_order_one : primeOrder 5 (-2) 3 = 1 := by
  let : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact Nat.dvd_one.mp
    ((int_dvd_pow_sub_pow_iff_primeOrder_dvd (q := 5) (-2) 3 1
      (by norm_num)).mp (by norm_num))

/-- Excluding a zero numerator is unnecessary for the power-difference iff. -/
theorem zero_numerator_order_zero : primeOrder 5 0 1 = 0 := by
  let : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  simp [primeOrder, primeRatio]

/-- The positive-order hypothesis really needs the numerator to be nonzero. -/
theorem zero_numerator_power_difference (n : ℕ) :
    (5 : ℤ) ∣ (0 : ℤ) ^ n - 1 ^ n ↔ n = 0 := by
  let : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  simpa [zero_numerator_order_zero] using
    (int_dvd_pow_sub_pow_iff_primeOrder_dvd (q := 5) 0 1 n (by norm_num))

/-- Natural subtraction below the denominator cannot encode the signed power difference. -/
theorem truncated_subtraction_changes_divisibility :
    (5 : ℕ) ∣ 1 ^ 1 - 2 ^ 1 ∧ ¬ (5 : ℤ) ∣ (1 : ℤ) ^ 1 - 2 ^ 1 := by
  norm_num

/-- Degree zero satisfies the existing definition vacuously, so a positive degree
is essential in the primitive-prime/order equivalence. -/
theorem existing_primitive_definition_degree_zero : PrimitivePrimeDivisor 2 1 0 3 := by
  norm_num [PrimitivePrimeDivisor]

/-- Above degree one, coordinate coprimality is unnecessary for excluding zero residues. -/
theorem primitive_coordinates_not_divisible : ¬ 7 ∣ 5 ∧ ¬ 7 ∣ 3 := by
  apply primitivePrimeDivisor_not_dvd_coordinates (a := 5) (b := 3) (n := 3)
    (by norm_num) (by norm_num)
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro m hmpos hmlt
  interval_cases m <;> norm_num

#print axioms base_two_order_mod_three
#print axioms primitive_seven_order_three
#print axioms signed_ratio_order_one
#print axioms zero_numerator_order_zero
#print axioms zero_numerator_power_difference
#print axioms truncated_subtraction_changes_divisibility
#print axioms existing_primitive_definition_degree_zero
#print axioms primitive_coordinates_not_divisible

end DkMathTest.NumberTheory.GapFocusingPrimeOrder
