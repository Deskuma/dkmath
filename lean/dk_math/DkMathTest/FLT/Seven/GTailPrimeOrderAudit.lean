/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.GTailPrimeOrderAudit

#print "file: DkMathTest.FLT.Seven.GTailPrimeOrderAudit"

/-! Guarded exact interfaces and the explicit non-Fermat status of calibration. -/

namespace DkMathTest.FLT.Seven.GTailPrimeOrderAudit

open DkMath.CosmicFormula DkMath.FLT.Seven

example {q a b c g : ℕ} (hcop : Nat.Coprime a b)
    (hEq : Fermat7Equation a b c) (hsum : a + b = c + g)
    (hq : Nat.Prime q) (hq7 : q ≠ 7) (hQ : q ∣ a ^ 2 + a * b + b ^ 2)
    (hT : q ∣ GTail 7 1 g c) : 21 ∣ q - 1 :=
  twentyOne_dvd_prime_sub_one_of_focused_tail hcop hEq hsum hq hq7 hQ hT

example {q a b c g : ℕ} (ha : 0 < a) (hb : 0 < b) (hcop : Nat.Coprime a b)
    (hEq : Fermat7Equation a b c) (hsum : a + b = c + g)
    (hq : Nat.Prime q) (hq7 : q ≠ 7) (hQ : q ∣ a ^ 2 + a * b + b ^ 2)
    (hnot : ¬ 21 ∣ q - 1) : q ^ 2 ∣ g ∧ ¬ q ∣ GTail 7 1 g c :=
  prime_square_dvd_gap_of_not_twentyOne ha hb hcop hEq hsum hq hq7 hQ hnot

-- Independently use Step 010's head-unit theorem on the neutral gap calibration.
example : ¬ 13 ∣ GTail 7 1 13 (30 : ℕ) :=
  not_prime_dvd_gtail_seven_of_gap (by decide) (by decide) (by decide) (by decide)

example : ¬ Fermat7Equation 5 8 9 := by
  unfold Fermat7Equation
  decide

#print axioms twentyOne_dvd_prime_sub_one_of_focused_tail
#print axioms prime_square_dvd_gap_of_not_twentyOne

end DkMathTest.FLT.Seven.GTailPrimeOrderAudit
