/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.GTailPrimeAllocationAudit

#print "file: DkMathTest.FLT.Seven.GTailPrimeAllocationAudit"

/-! Conditional interfaces; no positive Fermat solution is fabricated. -/

namespace DkMathTest.FLT.Seven.GTailPrimeAllocationAudit

open DkMath.CosmicFormula DkMath.FLT.Seven

example {q a b : ℕ}
    (hq : Nat.Prime q) (hcop : Nat.Coprime a b)
    (hqQ : q ∣ a ^ 2 + a * b + b ^ 2) : ¬ q ∣ a * b * (a + b) :=
  not_prime_dvd_coordinate_product_of_quadratic hq hcop hqQ

example {q a b c : ℕ}
    (hq : Nat.Prime q) (hcop : Nat.Coprime a b)
    (hEq : Fermat7Equation a b c) (hqQ : q ∣ a ^ 2 + a * b + b ^ 2) :
    ¬ q ∣ c :=
  not_prime_dvd_endpoint_of_quadratic hq hcop hEq hqQ

example {q a b c g : ℕ}
    (hq : Nat.Prime q) (hq7 : q ≠ 7) (hcop : Nat.Coprime a b)
    (hEq : Fermat7Equation a b c) (hsum : a + b = c + g)
    (hqQ : q ∣ a ^ 2 + a * b + b ^ 2) :
    (q ∣ g ∧ ¬ q ∣ GTail 7 1 g c) ∨ (q ∣ GTail 7 1 g c ∧ ¬ q ∣ g) :=
  prime_focused_support_exclusive hq hq7 hcop hEq hsum hqQ

example {q a b c g : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hcop : Nat.Coprime a b)
    (hEq : Fermat7Equation a b c) (hsum : a + b = c + g)
    (hq : Nat.Prime q) (hq7 : q ≠ 7) (hqQ : q ∣ a ^ 2 + a * b + b ^ 2) :
    padicValNat q g + padicValNat q (GTail 7 1 g c) =
      2 * padicValNat q (a ^ 2 + a * b + b ^ 2) :=
  padicValNat_focused_quadratic_budget ha hb hcop hEq hsum hq hq7 hqQ

example {q a b c g : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hcop : Nat.Coprime a b)
    (hEq : Fermat7Equation a b c) (hsum : a + b = c + g)
    (hq : Nat.Prime q) (hq7 : q ≠ 7) (hqQ : q ∣ a ^ 2 + a * b + b ^ 2) :
    (q ^ 2 ∣ g ∧ ¬ q ∣ GTail 7 1 g c) ∨
      (q ^ 2 ∣ GTail 7 1 g c ∧ ¬ q ∣ g) :=
  prime_square_focused_allocation ha hb hcop hEq hsum hq hq7 hqQ

#print axioms not_prime_dvd_coordinate_product_of_quadratic
#print axioms not_prime_dvd_endpoint_of_quadratic
#print axioms prime_focused_support_exclusive
#print axioms padicValNat_focused_quadratic_budget
#print axioms prime_square_focused_allocation

end DkMathTest.FLT.Seven.GTailPrimeAllocationAudit
