/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.GTailPrimeAllocationAudit
import DkMath.Lib.NumberTheory.GTailSevenPrimeOrder

#print "file: DkMath.FLT.Seven.GTailPrimeOrderAudit"

/-!
# Branch-guarded scalar prime order

The exact equation provides local units, while nontrivial finite-field
orders are proved independently in the neutral module. No descent is built.
-/

namespace DkMath.FLT.Seven

/-- Only quadratic primes on the tail side must carry both orders three and seven. -/
theorem twentyOne_dvd_prime_sub_one_of_focused_tail {q a b c g : ℕ}
    (hcop : Nat.Coprime a b) (hEq : Fermat7Equation a b c) (hsum : a + b = c + g)
    (hq : Nat.Prime q) (hq7 : q ≠ 7) (hQ : q ∣ a ^ 2 + a * b + b ^ 2)
    (hT : q ∣ DkMath.CosmicFormula.GTail 7 1 g c) : 21 ∣ q - 1 := by
  have hunit := not_prime_dvd_coordinate_product_of_quadratic hq hcop hQ
  have ha : ¬ q ∣ a := fun hd => hunit (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hd _) _)
  have hb : ¬ q ∣ b := fun hd => hunit (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hd _) _)
  have hc := not_prime_dvd_endpoint_of_quadratic hq hcop hEq hQ
  have hsupport := prime_focused_support_exclusive hq hq7 hcop hEq hsum hQ
  have hg : ¬ q ∣ g := (hsupport.resolve_left (fun hl => hl.2 hT)).2
  exact DkMath.Lib.NumberTheory.twentyOne_dvd_prime_sub_one_of_quadratic_gtail
    hq hq7 hQ hT ha hb hc hg

/-- Primes without the tail-side order intersection must allocate their square to the gap. -/
theorem prime_square_dvd_gap_of_not_twentyOne {q a b c g : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hcop : Nat.Coprime a b)
    (hEq : Fermat7Equation a b c) (hsum : a + b = c + g)
    (hq : Nat.Prime q) (hq7 : q ≠ 7) (hQ : q ∣ a ^ 2 + a * b + b ^ 2)
    (hnot : ¬ 21 ∣ q - 1) : q ^ 2 ∣ g ∧ ¬ q ∣ DkMath.CosmicFormula.GTail 7 1 g c := by
  have hnT : ¬ q ∣ DkMath.CosmicFormula.GTail 7 1 g c := fun hd =>
    hnot (twentyOne_dvd_prime_sub_one_of_focused_tail hcop hEq hsum hq hq7 hQ hd)
  have halloc := prime_square_focused_allocation ha hb hcop hEq hsum hq hq7 hQ
  have hright : ¬ (q ^ 2 ∣ DkMath.CosmicFormula.GTail 7 1 g c ∧ ¬ q ∣ g) := fun hr =>
    hnT ((dvd_pow_self q (by decide : 2 ≠ 0)).trans hr.1)
  exact halloc.resolve_right hright

end DkMath.FLT.Seven
