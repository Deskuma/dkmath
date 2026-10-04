/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.GapFocusing.CyclotomicAddress

#print "file: DkMathTest.NumberTheory.CyclotomicAddress"

namespace DkMathTest.NumberTheory.CyclotomicAddress

open Polynomial DkMath.NumberTheory.GapFocusing DkMath.Lib.NumberTheory

/-- Distinct integer cyclotomic layers can even evaluate to the same value. -/
theorem two_six_evaluation :
    cyclotomicEval 2 (2 : ℤ) = 3 ∧ cyclotomicEval 6 (2 : ℤ) = 3 := by
  norm_num [cyclotomicEval, eval₂_eq_eval_map, cyclotomic_two, cyclotomic_six]

/-- The prime two needs no separate divisibility exception. -/
theorem prime_two_degree_addresses {n : ℕ} (hn : 0 < n) :
    (2 : ℤ) ∣ cyclotomicEval n (3 : ℤ) ↔ ∃ k : ℕ, n = 2 ^ k := by
  have h := prime_dvd_cyclotomicEval_iff_prime_pow_mul_orderOf (q := 2) hn (3 : ℤ)
  simp only [Nat.cast_ofNat, Int.cast_ofNat] at h
  rw [h]
  have hc : (3 : ZMod 2) = 1 := by decide
  simp [hc]

/-- If the prime divides the base, every positive-degree address is absent. -/
theorem prime_dividing_base_no_address {n : ℕ} (hn : 0 < n) :
    ¬(3 : ℤ) ∣ cyclotomicEval n (6 : ℤ) := by
  have h := prime_dvd_cyclotomicEval_iff_prime_pow_mul_orderOf (q := 3) hn (6 : ℤ)
  simp only [Nat.cast_ofNat, Int.cast_ofNat] at h
  rw [h]
  have hc : (6 : ZMod 3) = 0 := by decide
  simp [hc, hn.ne']

/-- The first address can have order one: removing degree one leaves the
prime itself as the first allowed nontrivial layer. -/
theorem order_one_initial_layer :
    orderOf (4 : ZMod 3) = 1 ∧
      ¬(3 : ℤ) ∣ cyclotomicEval 2 (4 : ℤ) ∧
      (3 : ℤ) ∣ cyclotomicEval 3 (4 : ℤ) := by
  have hc : (4 : ZMod 3) = 1 := by decide
  constructor
  · rw [hc, orderOf_one]
  · norm_num [cyclotomicEval, eval₂_eq_eval_map,
      cyclotomic_two, cyclotomic_three]

/-- The reappearance has no degree additivity: the relevant progression
multiplies by the rational prime. -/
theorem prime_three_degree_two_ray (k : ℕ) :
    (3 : ℤ) ∣ cyclotomicEval (2 * 3 ^ k) (2 : ℤ) := by
  apply (prime_dvd_cyclotomicEval_mul_prime_pow_iff 2 k (2 : ℤ)).mpr
  rw [two_six_evaluation.1]
  norm_num

#print axioms DkMath.NumberTheory.GapFocusing.isRoot_cyclotomic_iff_prime_pow_mul_orderOf
#print axioms DkMath.NumberTheory.GapFocusing.isRoot_cyclotomic_iff_orderOf_of_not_dvd
#print axioms DkMath.NumberTheory.GapFocusing.isRoot_cyclotomic_mul_prime_iff
#print axioms DkMath.NumberTheory.GapFocusing.isRoot_cyclotomic_mul_prime_pow_iff
#print axioms DkMath.NumberTheory.GapFocusing.prime_dvd_cyclotomicEval_iff_isRoot
#print axioms DkMath.NumberTheory.GapFocusing.prime_dvd_cyclotomicEval_iff_prime_pow_mul_orderOf
#print axioms DkMath.NumberTheory.GapFocusing.prime_dvd_cyclotomicEval_iff_orderOf_of_not_dvd
#print axioms DkMath.NumberTheory.GapFocusing.prime_dvd_cyclotomicEval_mul_prime_pow_iff
#print axioms two_six_evaluation
#print axioms prime_two_degree_addresses
#print axioms prime_dividing_base_no_address
#print axioms order_one_initial_layer
#print axioms prime_three_degree_two_ray

end DkMathTest.NumberTheory.CyclotomicAddress
