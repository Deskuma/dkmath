/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.GTailConstraintAudit

#print "file: DkMathTest.FLT.Seven.GTailConstraintAudit"

/-!
# Constraint and missing-premise regressions

Positive coordinate examples below do not assert a Fermat equation. Concrete
failures concern only the explicitly weakened neutral contracts.
-/

namespace DkMathTest.FLT.Seven.GTailConstraintAudit

open DkMath.CosmicFormula DkMath.FLT.Seven

example {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hEq : Fermat7Equation a b c) :
    max a b < c ∧ c < a + b := fermat7_focused_bounds ha hb hEq

example {a b c g : ℕ} (ha : 0 < a) (hb : 0 < b) (hEq : Fermat7Equation a b c)
    (hsum : c + g = a + b) : g < a ∧ g < b :=
  focused_gap_lt_coordinates ha hb hEq hsum

example {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hEq : Fermat7Equation a b c) :
    ∃ g : ℕ, 0 < g ∧ g < a ∧ g < b ∧ c + g = a + b :=
  exists_positive_focused_gap ha hb hEq

-- Independent instance of the product/address proof; no counterexample packet.
example {a b c g : ℕ} (hEq : Fermat7Equation a b c) (hsum : a + b = c + g) :
    7 ∣ g := by
  have hprod : 7 ∣ g * GTail 7 1 g c := by
    rw [gtail_seven_eq_of_fermat7Equation hEq hsum]
    exact ⟨a * b * (a + b) * (a ^ 2 + a * b + b ^ 2) ^ 2, by ring⟩
  rcases (by decide : Nat.Prime 7).dvd_mul.mp hprod with hg | ht
  · exact hg
  · exact (prime_dvd_GN_iff_dvd_gap (by decide : Nat.Prime 7)).mp ht

example : 7 ∣ (0 : ℕ) :=
  seven_dvd_focused_gap (a := 0) (b := 3) (c := 3)
    (by norm_num [Fermat7Equation]) (by norm_num)

-- Prime-row address on satisfiable inputs, independent of a Fermat equation.
example (g c : ℕ) : 7 ∣ GTail 7 1 g c ↔ 7 ∣ g :=
  prime_dvd_GN_iff_dvd_gap (by decide)

example : 7 ∣ GTail 7 1 7 (2 : ℕ) :=
  (prime_dvd_GN_iff_dvd_gap (by decide : Nat.Prime 7)).mpr (by norm_num)

example : ¬ 7 ∣ GTail 7 1 1 (4 : ℕ) := by decide
example : ¬ 7 ∣ (1 : ℕ) := by norm_num

example {a b : ℕ} (h : Nat.Coprime a b) :
    Nat.Coprime a (a ^ 2 + a * b + b ^ 2) ∧
    Nat.Coprime b (a ^ 2 + a * b + b ^ 2) ∧
    Nat.Coprime (a + b) (a ^ 2 + a * b + b ^ 2) ∧
    Nat.Coprime (a * b * (a + b)) (a ^ 2 + a * b + b ^ 2) :=
  ⟨coprime_left_seven_quadratic h, coprime_right_seven_quadratic h,
    coprime_sum_seven_quadratic h, coprime_product_seven_quadratic h⟩

example : Nat.Coprime (2 * 3 * (2 + 3)) (2 ^ 2 + 2 * 3 + 3 ^ 2) :=
  coprime_product_seven_quadratic (by decide)

example : Nat.Coprime (0 * 1 * (0 + 1)) (0 ^ 2 + 0 * 1 + 1 ^ 2) :=
  coprime_product_seven_quadratic (by decide)

-- Dropping primitive-pair coprimality makes the Q conclusion false.
example : ¬ Nat.Coprime (2 : ℕ) (2 ^ 2 + 2 * 2 + 2 ^ 2) := by decide

example : 7 ∣ GTail 7 1 7 (2 : ℕ) ∧ ¬ 7 ^ 2 ∣ GTail 7 1 7 (2 : ℕ) :=
  gtail_seven_exact_seven_layer (by norm_num) (by norm_num)

-- Endpoint-unit condition is weaker than full coprimality: gcd(14,2)=2.
example : ¬ Nat.Coprime (14 : ℕ) 2 ∧
    (7 ∣ GTail 7 1 14 (2 : ℕ) ∧ ¬ 7 ^ 2 ∣ GTail 7 1 14 (2 : ℕ)) :=
  ⟨by decide, gtail_seven_exact_seven_layer (by norm_num) (by norm_num)⟩

example : 7 ^ 2 ∣ GTail 7 1 7 (7 : ℕ) := by decide

-- Height, primitive pair and mod-seven focus do not imply Coprime g c.
example : Nat.Coprime (11 : ℕ) 17 ∧ 21 + 7 = 11 + 17 ∧
    max 11 17 < 21 ∧ 7 < 11 ∧ 7 < 17 ∧ 7 ∣ (7 : ℕ) ∧
    ¬ Nat.Coprime (7 : ℕ) 21 := by decide

-- Even adding Coprime g c does not imply Coprime g Q.
example : Nat.Coprime (8 : ℕ) 11 ∧ 12 + 7 = 8 + 11 ∧
    max 8 11 < 12 ∧ 7 < 8 ∧ 7 < 11 ∧ Nat.Coprime (7 : ℕ) 12 ∧
    ¬ Nat.Coprime (7 : ℕ) (8 ^ 2 + 8 * 11 + 11 ^ 2) := by decide

-- These missing-premise examples are not positive Fermat solutions.
example : ¬ Fermat7Equation 11 17 21 ∧ ¬ Fermat7Equation 8 11 12 := by
  norm_num [Fermat7Equation]

-- Product square divisibility by itself cannot specify which factor carries it.
example : (3 : ℕ) ^ 2 ∣ 3 * 3 ∧ ¬ (3 : ℕ) ^ 2 ∣ 3 := by norm_num
example : (3 : ℕ) ^ 2 ∣ 3 * GTail 7 1 3 (3 : ℕ) ∧ ¬ (3 : ℕ) ^ 2 ∣ 3 := by
  decide

-- The proved neutral coprimality localizes any prime in Q away from a*b*(a+b).
example {a b q : ℕ} (hcop : Nat.Coprime a b) (hq : Nat.Prime q)
    (hQ : q ∣ a ^ 2 + a * b + b ^ 2) : ¬ q ∣ a * b * (a + b) := by
  intro hprod
  have hgcd := Nat.dvd_gcd hprod hQ
  rw [(coprime_product_seven_quadratic hcop).gcd_eq_one] at hgcd
  exact hq.not_dvd_one hgcd

-- Mod-49 compatibility and Q-divisibility alone do not give a Fermat solution.
example : ((1 : ℕ) ^ 7 + 2 ^ 7) % 49 = 3 ^ 7 % 49 ∧
    7 ∣ ((1 : ℕ) ^ 2 + 1 * 2 + 2 ^ 2) ∧ ¬ Fermat7Equation 1 2 3 := by
  norm_num [Fermat7Equation]

#print axioms fermat7_focused_bounds
#print axioms focused_gap_lt_coordinates
#print axioms exists_positive_focused_gap
#print axioms seven_dvd_focused_gap
#print axioms coprime_left_seven_quadratic
#print axioms coprime_right_seven_quadratic
#print axioms coprime_sum_seven_quadratic
#print axioms coprime_product_seven_quadratic
#print axioms gtail_seven_exact_seven_layer

end DkMathTest.FLT.Seven.GTailConstraintAudit
