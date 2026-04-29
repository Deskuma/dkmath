/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib

#print "file: DkMath.ABC.RpowExtras"

set_option linter.style.longLine false
set_option linter.style.emptyLine false
set_option linter.style.whitespace false

namespace RpowExtras

open Real

/-- x > 0 かつ任意の k : ℕ に対して x^{a * k} = (x^a)^k となる補題。 -/
lemma rpow_mul_nat {x a : ℝ} (hx : 0 < x) :
  ∀ k : ℕ, Real.rpow x (a * (k : ℝ)) = (Real.rpow x a) ^ k := by
  intro k
  induction k with
  | zero =>
      simp only [CharP.cast_eq_zero, mul_zero, rpow_eq_pow, rpow_zero, pow_zero]
  | succ k ih =>
      have : a * ((k + 1 : ℕ) : ℝ) = a * (k : ℝ) + a := by
        simp [mul_add, Nat.cast_add, Nat.cast_one]
      calc
        Real.rpow x (a * ((k + 1 : ℕ) : ℝ)) = Real.rpow x (a * (k : ℝ) + a) := by rw [this]
        _ = Real.rpow x (a * (k : ℝ)) * Real.rpow x a := by simp [Real.rpow_add hx]
        _ = (Real.rpow x a) ^ (k + 1) := by
          rw [ih]
          rw [pow_succ]

/-- 2^(α+ε) > 1 when α+ε > 0 (helper) -/
lemma one_lt_rpow_two {a : ℝ} (h : 0 < a) : 1 < (2 : ℝ) ^ a := by
  have : (1 : ℝ) < 2 := by norm_num
  exact Real.one_lt_rpow this (by exact_mod_cast h)

/-- (2^a - 1) > 0 when a > 0 -/
lemma denom_pos {a : ℝ} (h : 0 < a) : 0 < (2 : ℝ) ^ a - 1 := by
  have h1 := one_lt_rpow_two (a := a) h
  linarith

end RpowExtras
