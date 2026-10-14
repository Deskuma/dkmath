/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Cosmic.GTailSevenPrimeAllocation

#print "file: DkMathTest.CosmicFormula.GTailSevenPrimeAllocation"

/-! Actual GTail prime addresses and independent abstract allocation regressions. -/

namespace DkMathTest.CosmicFormula.GTailSevenPrimeAllocation

open DkMath.CosmicFormula

example : 13 ∣ (13 : ℕ) ∧ ¬ 13 ∣ GTail 7 1 13 (2 : ℕ) :=
  ⟨dvd_refl _, not_prime_dvd_gtail_seven_of_gap (by decide) (by decide)
    (dvd_refl _) (by decide)⟩

example : GTail 7 1 13 (2 : ℕ) = 13143019 ∧
    ¬ 13 ∣ GTail 7 1 13 (2 : ℕ) := by decide

example : GTail 7 1 3 (1 : ℕ) = 5461 ∧ (5461 : ℕ) = 43 * 127 ∧
    ¬ 43 ∣ (3 : ℕ) ∧ 43 ∣ GTail 7 1 3 (1 : ℕ) := by decide

-- The endpoint-unit and degree-prime exclusions are both essential.
example : 13 ∣ GTail 7 1 13 (13 : ℕ) := by decide

example : 7 ∣ (7 : ℕ) ∧ 7 ∣ GTail 7 1 7 (2 : ℕ) := by decide

-- Abstract factors, not a Fermat or actual-GTail packet.
private theorem abstract_budget :
    padicValNat 43 (43 ^ 2) + padicValNat 43 7 = 2 * padicValNat 43 43 :=
  padicValNat_prime_square_product (A := 1) (B := 1) (C := 1)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

example : (43 : ℕ) ^ 2 * 7 = 7 * 1 * 1 * 1 * 43 ^ 2 ∧
    padicValNat 43 (43 ^ 2) + padicValNat 43 7 = 2 * padicValNat 43 43 :=
  ⟨by decide, abstract_budget⟩

example : (43 ^ 2 ∣ (43 : ℕ) ^ 2 ∧ ¬ 43 ∣ (7 : ℕ)) ∨
    (43 ^ 2 ∣ (7 : ℕ) ∧ ¬ 43 ∣ (43 : ℕ) ^ 2) :=
  prime_square_allocation_of_budget (by decide) (by decide) (by decide) (by decide)
    (dvd_refl _) abstract_budget (fun _ => by decide)

-- Mixed allocation satisfies the budget but neither left factor contains q².
example : padicValNat 43 43 + padicValNat 43 (7 * 43) = 2 * padicValNat 43 43 ∧
    43 ∣ (43 : ℕ) ∧ 43 ∣ (7 * 43 : ℕ) ∧
    ¬ 43 ^ 2 ∣ (43 : ℕ) ∧ ¬ 43 ^ 2 ∣ (7 * 43 : ℕ) := by
  refine ⟨?_, by decide, by decide, by decide, by decide⟩
  exact padicValNat_prime_square_product (A := 1) (B := 1) (C := 1)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

#print axioms not_prime_dvd_gtail_seven_of_gap
#print axioms padicValNat_prime_square_product
#print axioms prime_square_allocation_of_budget

end DkMathTest.CosmicFormula.GTailSevenPrimeAllocation
