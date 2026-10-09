/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.GTailSevenPrimeOrder

#print "file: DkMathTest.NumberTheory.GTailSevenPrimeOrder"

/-! Nonvacuous modular calibrations; exact power inequalities are explicit. -/

namespace DkMathTest.NumberTheory.GTailSevenPrimeOrder

open DkMath.CosmicFormula DkMath.Lib.NumberTheory

example : 7 ∣ (43 : ℕ) - 1 :=
  seven_dvd_prime_sub_one_of_gtail (c := 1) (g := 3)
    (by decide) (by decide) (by decide) (by decide) (by decide)

example : (43 : ℕ) ≠ 3 :=
  prime_ne_three_of_gtail (c := 1) (g := 3)
    (by decide) (by decide) (by decide) (by decide) (by decide)

example : 3 ∣ (7 : ℕ) - 1 :=
  three_dvd_prime_sub_one_of_quadratic (a := 1) (b := 2)
    (by decide) (by decide) (by decide) (by decide) (by decide)

example : 21 ∣ (43 : ℕ) - 1 :=
  twentyOne_dvd_prime_sub_one_of_quadratic_gtail (a := 5) (b := 8) (c := 9) (g := 4)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

-- Complete T-side compatibility, with no exact equation or FLT import.
example : (5 : ℕ) + 8 = 9 + 4 ∧ Nat.Coprime 5 8 ∧
    (5 : ℕ) ^ 2 + 5 * 8 + 8 ^ 2 = 129 ∧ (129 : ℕ) = 43 * 3 ∧
    43 ∣ ((5 : ℕ) ^ 2 + 5 * 8 + 8 ^ 2) ∧ 43 ∣ GTail 7 1 4 (9 : ℕ) ∧
    ¬ 43 ∣ (5 * 8 * 9 * 4 : ℕ) ∧ 21 ∣ (43 : ℕ) - 1 ∧ 42 ∣ (43 : ℕ) - 1 ∧
    ((5 : ℕ) ^ 7 + 8 ^ 7) % 43 = 9 ^ 7 % 43 ∧ (5 : ℕ) ^ 7 + 8 ^ 7 ≠ 9 ^ 7 := by
  decide

-- G-side contrast: the quadratic prime need not have a nontrivial seventh root.
example : (14 : ℕ) + 29 = 30 + 13 ∧ Nat.Coprime 14 29 ∧
    13 ∣ ((14 : ℕ) ^ 2 + 14 * 29 + 29 ^ 2) ∧ 13 ∣ (13 : ℕ) ∧
    ¬ 13 ∣ (30 : ℕ) ∧ ¬ 13 ∣ GTail 7 1 13 (30 : ℕ) ∧ ¬ 21 ∣ (13 : ℕ) - 1 := by
  decide

-- Repeated quadratic root at characteristic three; the order-three claim fails.
example : 3 ∣ ((1 : ℕ) ^ 2 + 1 * 1 + 1 ^ 2) ∧ ¬ 3 ∣ (1 : ℕ) ∧
    ¬ 3 ∣ (3 : ℕ) - 1 := by decide

example : (1 : ZMod 3) / 1 = 1 := by norm_num

-- A seven-divisible tail with a zero gap residue cannot provide order seven.
example : 7 ∣ GTail 7 1 7 (2 : ℕ) ∧ 7 ∣ (7 : ℕ) ∧ ¬ 7 ∣ (7 : ℕ) - 1 := by decide

#print axioms seven_dvd_prime_sub_one_of_gtail
#print axioms prime_ne_three_of_gtail
#print axioms three_dvd_prime_sub_one_of_quadratic
#print axioms twentyOne_dvd_prime_sub_one_of_quadratic_gtail

end DkMathTest.NumberTheory.GTailSevenPrimeOrder
