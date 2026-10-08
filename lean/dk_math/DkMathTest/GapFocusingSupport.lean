/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.GapFocusing.Support

/-!
Boundary regressions for adjacent support. The degree-six example is a
checked failure of a new primitive prime at every degree: the prime divisors
of `GN₆(1,1) = 63` already occur at degrees two or three.
-/

namespace DkMathTest.GapFocusingSupport

open DkMath.CosmicFormula DkMath.NumberTheory.GapFocusing

example (x u : ℕ) : (GTail 0 1 x u).Coprime (GTail 1 1 x u) := by
  simp [GTail]

example : (GTail 2 1 1 1 : ℕ).Coprime (GTail 3 1 1 1) :=
  nat_coprime_adjacent_GN 2 1 1 (by decide)

example : Int.gcd (GTail 4 1 (-3) 2) (GTail 5 1 (-3) 2) = 1 :=
  int_gcd_adjacent_GN_eq_one 4 (-3) 2 (by decide)

example : (GTail 2 1 2 2 : ℕ) = 6 ∧ (GTail 3 1 2 2 : ℕ) = 28 := by
  decide

example : ¬(GTail 2 1 2 2 : ℕ).Coprime (GTail 3 1 2 2) := by
  rw [nat_coprime_adjacent_GN_iff 0 2 2]
  decide

example : (GTail 2 1 1 1 : ℕ) = 3 ∧ (GTail 6 1 1 1 : ℕ) = 63 := by
  decide

example : 3 ∣ (GTail 2 1 1 1 : ℕ) ∧ 3 ∣ (GTail 6 1 1 1 : ℕ) := by
  decide

/-- No prime dividing the degree-six binary kernel is new relative to all
earlier degrees; each is already present at degree two or three. -/
theorem degree_six_prime_support_repeats {p : ℕ} (hp : p.Prime)
    (h : p ∣ GTail 6 1 1 1) :
    p ∣ GTail 2 1 1 1 ∨ p ∣ GTail 3 1 1 1 := by
  have h6 : (GTail 6 1 1 1 : ℕ) = (3 * 3) * 7 := by
    decide
  have h2 : (GTail 2 1 1 1 : ℕ) = 3 := by
    decide
  have h3 : (GTail 3 1 1 1 : ℕ) = 7 := by
    decide
  rw [h6] at h
  rw [h2, h3]
  rcases hp.dvd_mul.mp h with h9 | h7
  · exact Or.inl ((hp.dvd_mul.mp h9).elim id id)
  · exact Or.inr h7

example : ∃ p : ℕ, p.Prime ∧ p ∣ GTail 6 1 1 1 ∧ ¬p ∣ GTail 5 1 1 1 :=
  nat_exists_prime_dvd_GN_succ_not_dvd_GN 5 1 1 (by decide) (by decide)
    (by decide) (by decide)

example : ¬∃ p : ℕ, p.Prime ∧ p ∣ GTail 1 1 1 1 := by
  simp only [GTail, Nat.reduceAdd, Nat.reduceSub, Finset.sum_range_one,
    Nat.choose_self, Nat.cast_id, pow_zero, mul_one]
  exact fun ⟨p, hp, hpd⟩ => hp.ne_one (Nat.dvd_one.mp hpd)

#print axioms dvd_anchor_pow_of_dvd_adjacent_GN
#print axioms dvd_sum_pow_of_dvd_adjacent_GN
#print axioms nat_dvd_powers_of_dvd_adjacent_GN
#print axioms nat_prime_dvd_coordinates_of_dvd_adjacent_GN
#print axioms nat_coprime_adjacent_GN
#print axioms nat_one_lt_GN_succ
#print axioms nat_exists_prime_dvd_GN_succ_not_dvd_GN
#print axioms dvd_GN_of_dvd_coordinates
#print axioms nat_prime_dvd_adjacent_GN_iff
#print axioms nat_coprime_adjacent_GN_iff
#print axioms isCoprime_adjacent_GN
#print axioms int_gcd_adjacent_GN_eq_one
#print axioms degree_six_prime_support_repeats

end DkMathTest.GapFocusingSupport
