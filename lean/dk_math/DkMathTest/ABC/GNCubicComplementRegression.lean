/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.GNExcessCubicComplement

/-!
# Negative regressions for canonical cubic repeated moduli

These exact collisions intentionally live in the test namespace.  They guard
against future claims that a point determines its repeated modulus injectively
or that one full repeated modulus has at most two roots.
-/

namespace DkMathTest.ABC.GNCubicComplementRegression

open DkMath.ABC DkMath.NumberTheory

example : GNNonExceptionalRepeatedPart 3 21 1 = 169 := by
  rw [GNNonExceptionalRepeatedPart_three_one_eq_repeatedPrimePowerPart,
    GN_three_dual_explicit]
  have hid : (21^2+3*21*1+3*1^2:ℕ) = 3^1*13^2 := by norm_num
  rw [hid]
  have hp3 : Nat.Prime 3 := by norm_num
  have hp13 : Nat.Prime 13 := by norm_num
  have hf : (3^1*13^2:ℕ).factorization =
      Finsupp.single 3 1 + Finsupp.single 13 2 := by
    repeat rw [Nat.factorization_mul (by norm_num) (by norm_num)]
    simp only [Nat.factorization_pow, hp3.factorization, hp13.factorization]
    simp
  unfold repeatedPrimePowerPart
  rw [hf]
  have hs : (Finsupp.single 3 1 + Finsupp.single 13 2 : ℕ →₀ ℕ).support = {3,13} := by
    ext q
    simp only [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_apply,
      Finset.mem_insert, Finset.mem_singleton]
    by_cases h3q : 3 = q <;> by_cases h13q : 13 = q <;> simp_all [eq_comm]
  rw [hs]
  norm_num [Finset.filter_insert, Finset.filter_singleton, Finset.prod_insert,
    Finsupp.single_apply]

example : GNNonExceptionalRepeatedPart 3 145 1 = 169 := by
  rw [GNNonExceptionalRepeatedPart_three_one_eq_repeatedPrimePowerPart,
    GN_three_dual_explicit]
  have hid : (145^2+3*145*1+3*1^2:ℕ) = 13^2*127^1 := by norm_num
  rw [hid]
  have hp13 : Nat.Prime 13 := by norm_num
  have hp127 : Nat.Prime 127 := by norm_num
  have hf : (13^2*127^1:ℕ).factorization =
      Finsupp.single 13 2 + Finsupp.single 127 1 := by
    repeat rw [Nat.factorization_mul (by norm_num) (by norm_num)]
    simp only [Nat.factorization_pow, hp13.factorization, hp127.factorization]
    simp
  unfold repeatedPrimePowerPart
  rw [hf]
  have hs : (Finsupp.single 13 2 + Finsupp.single 127 1 : ℕ →₀ ℕ).support = {13,127} := by
    ext q
    simp only [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_apply,
      Finset.mem_insert, Finset.mem_singleton]
    by_cases h13q : 13 = q <;> by_cases h127q : 127 = q <;> simp_all [eq_comm]
  rw [hs]
  norm_num [Finset.filter_insert, Finset.filter_singleton, Finset.prod_insert,
    Finsupp.single_apply]

example : GNNonExceptionalRepeatedPart 3 2173 1 = 8281 := by
  rw [GNNonExceptionalRepeatedPart_three_one_eq_repeatedPrimePowerPart,
    GN_three_dual_explicit]
  have hid : (2173^2+3*2173*1+3*1^2:ℕ) = 7^2*13^2*571^1 := by norm_num
  rw [hid]
  have hp7 : Nat.Prime 7 := by norm_num
  have hp13 : Nat.Prime 13 := by norm_num
  have hp571 : Nat.Prime 571 := by norm_num
  have hf : (7^2*13^2*571^1:ℕ).factorization =
      Finsupp.single 7 2 + Finsupp.single 13 2 + Finsupp.single 571 1 := by
    repeat rw [Nat.factorization_mul (by norm_num) (by norm_num)]
    simp only [Nat.factorization_pow, hp7.factorization, hp13.factorization,
      hp571.factorization]
    simp
  unfold repeatedPrimePowerPart
  rw [hf]
  have hs : (Finsupp.single 7 2 + Finsupp.single 13 2 + Finsupp.single 571 1 : ℕ →₀ ℕ).support = {7,13,571} := by
    ext q
    simp only [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_apply,
      Finset.mem_insert, Finset.mem_singleton]
    by_cases h7q : 7 = q <;> by_cases h13q : 13 = q <;>
      by_cases h571q : 571 = q <;> simp_all [eq_comm]
  rw [hs]
  norm_num [Finset.filter_insert, Finset.filter_singleton, Finset.prod_insert,
    Finsupp.single_apply]

example : GNNonExceptionalRepeatedPart 3 3018 1 = 8281 := by
  rw [GNNonExceptionalRepeatedPart_three_one_eq_repeatedPrimePowerPart,
    GN_three_dual_explicit]
  have hid : (3018^2+3*3018*1+3*1^2:ℕ) = 3^1*7^2*13^2*367^1 := by norm_num
  rw [hid]
  have hp3 : Nat.Prime 3 := by norm_num
  have hp7 : Nat.Prime 7 := by norm_num
  have hp13 : Nat.Prime 13 := by norm_num
  have hp367 : Nat.Prime 367 := by norm_num
  have hf : (3^1*7^2*13^2*367^1:ℕ).factorization =
      Finsupp.single 3 1 + Finsupp.single 7 2 + Finsupp.single 13 2 + Finsupp.single 367 1 := by
    repeat rw [Nat.factorization_mul (by norm_num) (by norm_num)]
    simp only [Nat.factorization_pow, hp3.factorization, hp7.factorization,
      hp13.factorization, hp367.factorization]
    simp
  unfold repeatedPrimePowerPart
  rw [hf]
  have hs : (Finsupp.single 3 1 + Finsupp.single 7 2 + Finsupp.single 13 2 + Finsupp.single 367 1 : ℕ →₀ ℕ).support = {3,7,13,367} := by
    ext q
    simp only [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_apply,
      Finset.mem_insert, Finset.mem_singleton]
    by_cases h3q : 3 = q <;> by_cases h7q : 7 = q <;>
      by_cases h13q : 13 = q <;> by_cases h367q : 367 = q <;>
        simp_all [eq_comm]
  rw [hs]
  norm_num [Finset.filter_insert, Finset.filter_singleton, Finset.prod_insert,
    Finsupp.single_apply]

example : GNNonExceptionalRepeatedPart 3 5260 1 = 8281 := by
  rw [GNNonExceptionalRepeatedPart_three_one_eq_repeatedPrimePowerPart,
    GN_three_dual_explicit]
  have hid : (5260^2+3*5260*1+3*1^2:ℕ) = 7^2*13^2*3343^1 := by norm_num
  rw [hid]
  have hp7 : Nat.Prime 7 := by norm_num
  have hp13 : Nat.Prime 13 := by norm_num
  have hp3343 : Nat.Prime 3343 := by norm_num
  have hf : (7^2*13^2*3343^1:ℕ).factorization =
      Finsupp.single 7 2 + Finsupp.single 13 2 + Finsupp.single 3343 1 := by
    repeat rw [Nat.factorization_mul (by norm_num) (by norm_num)]
    simp only [Nat.factorization_pow, hp7.factorization, hp13.factorization,
      hp3343.factorization]
    simp
  unfold repeatedPrimePowerPart
  rw [hf]
  have hs : (Finsupp.single 7 2 + Finsupp.single 13 2 + Finsupp.single 3343 1 : ℕ →₀ ℕ).support = {7,13,3343} := by
    ext q
    simp only [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_apply,
      Finset.mem_insert, Finset.mem_singleton]
    by_cases h7q : 7 = q <;> by_cases h13q : 13 = q <;>
      by_cases h3343q : 3343 = q <;> simp_all [eq_comm]
  rw [hs]
  norm_num [Finset.filter_insert, Finset.filter_singleton, Finset.prod_insert,
    Finsupp.single_apply]

example : GNNonExceptionalRepeatedPart 3 6105 1 = 8281 := by
  rw [GNNonExceptionalRepeatedPart_three_one_eq_repeatedPrimePowerPart,
    GN_three_dual_explicit]
  have hid : (6105^2+3*6105*1+3*1^2:ℕ) = 3^1*7^2*13^2*19^1*79^1 := by norm_num
  rw [hid]
  have hp3 : Nat.Prime 3 := by norm_num
  have hp7 : Nat.Prime 7 := by norm_num
  have hp13 : Nat.Prime 13 := by norm_num
  have hp19 : Nat.Prime 19 := by norm_num
  have hp79 : Nat.Prime 79 := by norm_num
  have hf : (3^1*7^2*13^2*19^1*79^1:ℕ).factorization =
      Finsupp.single 3 1 + Finsupp.single 7 2 + Finsupp.single 13 2 +
      Finsupp.single 19 1 + Finsupp.single 79 1 := by
    repeat rw [Nat.factorization_mul (by norm_num) (by norm_num)]
    simp only [Nat.factorization_pow, hp3.factorization, hp7.factorization,
      hp13.factorization, hp19.factorization, hp79.factorization]
    simp
  unfold repeatedPrimePowerPart
  rw [hf]
  have hs : (Finsupp.single 3 1 + Finsupp.single 7 2 + Finsupp.single 13 2 +
      Finsupp.single 19 1 + Finsupp.single 79 1 : ℕ →₀ ℕ).support =
      {3,7,13,19,79} := by
    ext q
    simp only [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_apply,
      Finset.mem_insert, Finset.mem_singleton]
    by_cases h3q : 3 = q <;> by_cases h7q : 7 = q <;>
      by_cases h13q : 13 = q <;> by_cases h19q : 19 = q <;>
        by_cases h79q : 79 = q <;> simp_all [eq_comm]
  rw [hs]
  norm_num [Finset.filter_insert, Finset.filter_singleton, Finset.prod_insert,
    Finsupp.single_apply]

end DkMathTest.ABC.GNCubicComplementRegression
