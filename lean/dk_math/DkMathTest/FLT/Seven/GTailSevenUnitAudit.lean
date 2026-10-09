/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.GTailSevenUnitAudit

#print "file: DkMathTest.FLT.Seven.GTailSevenUnitAudit"

/-!
Conditional exact-equation interfaces and a satisfiable mod-49-only example.
The numeric residue example is explicitly not an exact Fermat solution.
-/

namespace DkMathTest.FLT.Seven.GTailSevenUnitAudit

open DkMath.FLT.Seven

example {a b c g : ℕ} (hEq : Fermat7Equation a b c)
    (hsum : a + b = c + g) (hc : ¬ 7 ∣ c) : ¬ 7 ∣ a + b :=
  not_seven_dvd_sum_of_focused_equation hEq hsum hc

example {a b c g : ℕ} (ha : 0 < a) (hb : 0 < b) (hEq : Fermat7Equation a b c)
    (hsum : a + b = c + g) (hua : ¬ 7 ∣ a) (hub : ¬ 7 ∣ b) (huc : ¬ 7 ∣ c) :
    padicValNat 7 g = 2 * padicValNat 7 (a ^ 2 + a * b + b ^ 2) :=
  padicValNat_focused_gap_unit_balance ha hb hEq hsum hua hub huc

example {a b c g : ℕ} (ha : 0 < a) (hb : 0 < b) (hEq : Fermat7Equation a b c)
    (hsum : a + b = c + g) (hua : ¬ 7 ∣ a) (hub : ¬ 7 ∣ b) (huc : ¬ 7 ∣ c) :
    7 ∣ a ^ 2 + a * b + b ^ 2 :=
  seven_dvd_quadratic_of_focused_units ha hb hEq hsum hua hub huc

example {a b c g : ℕ} (ha : 0 < a) (hb : 0 < b) (hEq : Fermat7Equation a b c)
    (hsum : a + b = c + g) (hua : ¬ 7 ∣ a) (hub : ¬ 7 ∣ b) (huc : ¬ 7 ∣ c) :
    49 ∣ g := fortyNine_dvd_focused_gap_of_units ha hb hEq hsum hua hub huc

-- Unit coordinates by themselves do not imply a unit sum.
example : ¬ 7 ∣ (1 : ℕ) ∧ ¬ 7 ∣ (6 : ℕ) ∧ 7 ∣ (1 + 6 : ℕ) := by decide

-- All focused arithmetic checks hold, but only the mod-49 Fermat relation holds.
example : (8 : ℕ) + 9 = 10 + 7 ∧ Nat.Coprime 8 9 ∧
    ¬ 7 ∣ (8 : ℕ) ∧ ¬ 7 ∣ (9 : ℕ) ∧ ¬ 7 ∣ (10 : ℕ) ∧
    max (8 : ℕ) 9 < 10 ∧ (10 : ℕ) < 8 + 9 ∧
    0 < (7 : ℕ) ∧ (7 : ℕ) < 8 ∧ (7 : ℕ) < 9 ∧
    ((8 : ℕ) ^ 7 + 9 ^ 7) % 49 = 10 ^ 7 % 49 ∧
    ¬ 49 ∣ (7 : ℕ) ∧ ¬ Fermat7Equation 8 9 10 := by
  unfold Fermat7Equation
  decide

-- Even the quadratic's seven-layer persists in this residue-only example.
example : 7 ∣ ((8 : ℕ) ^ 2 + 8 * 9 + 9 ^ 2) := by decide

-- Congruence alone also fails the exact valuation balance: v7(g)=1, v7(Q)=1.
example : padicValNat 7 7 ≠
    2 * padicValNat 7 ((8 : ℕ) ^ 2 + 8 * 9 + 9 ^ 2) := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hQ : (8 : ℕ) ^ 2 + 8 * 9 + 9 ^ 2 = 7 * 31 := by decide
  rw [hQ, padicValNat.mul (by decide) (by decide)]
  norm_num [padicValNat.eq_zero_of_not_dvd (by decide : ¬ 7 ∣ (31 : ℕ))]

#print axioms not_seven_dvd_sum_of_focused_equation
#print axioms padicValNat_focused_gap_unit_balance
#print axioms seven_dvd_quadratic_of_focused_units
#print axioms fortyNine_dvd_focused_gap_of_units

end DkMathTest.FLT.Seven.GTailSevenUnitAudit
