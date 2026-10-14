/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.GTailConstraintAudit
import DkMath.Lib.Cosmic.GTailSevenPrimeAllocation

#print "file: DkMath.FLT.Seven.GTailPrimeAllocationAudit"

/-!
# Conditional q-local square allocation

Primitive input localizes primes of the quadratic. The exact Fermat equation
supplies the endpoint unit; no global gap coprimality or descent is asserted.
-/

namespace DkMath.FLT.Seven

open DkMath.CosmicFormula

/-- A prime of the quadratic is absent from all ordinary coordinate factors. -/
theorem not_prime_dvd_coordinate_product_of_quadratic {q a b : ℕ}
    (hq : Nat.Prime q) (hcop : Nat.Coprime a b)
    (hqQ : q ∣ a ^ 2 + a * b + b ^ 2) : ¬ q ∣ a * b * (a + b) := by
  have hcopQ := coprime_product_seven_quadratic hcop
  intro hd
  have hcommon := Nat.dvd_gcd hd hqQ
  exact hq.not_dvd_one (by simpa [hcopQ.gcd_eq_one] using hcommon)

/-- The exact additive power identity excludes a quadratic prime from the endpoint. -/
theorem not_prime_dvd_endpoint_of_quadratic {q a b c : ℕ}
    (hq : Nat.Prime q) (hcop : Nat.Coprime a b)
    (hEq : Fermat7Equation a b c) (hqQ : q ∣ a ^ 2 + a * b + b ^ 2) :
    ¬ q ∣ c := by
  have hprodunit := not_prime_dvd_coordinate_product_of_quadratic hq hcop hqQ
  have hsumunit : ¬ q ∣ a + b := fun hd => hprodunit (dvd_mul_of_dvd_right hd _)
  have hbalance := add_pow_seven_eq_gap_add_interior a b
  have hEq' : a ^ 7 + b ^ 7 = c ^ 7 := hEq
  rw [add_comm (b ^ 7) (a ^ 7), hEq'] at hbalance
  intro hqc
  have hinterior : q ∣ 7 * a * b * (a + b) * (a ^ 2 + a * b + b ^ 2) ^ 2 :=
    dvd_mul_of_dvd_right (hqQ.trans (dvd_pow_self _ (by decide : 2 ≠ 0))) _
  have hsumPow : q ∣ (a + b) ^ 7 := by
    rw [hbalance]
    exact dvd_add (hqc.trans (dvd_pow_self _ (by decide : 7 ≠ 0))) hinterior
  exact hsumunit (hq.dvd_of_dvd_pow hsumPow)

/-- A quadratic prime other than seven occupies exactly one focused product factor. -/
theorem prime_focused_support_exclusive {q a b c g : ℕ}
    (hq : Nat.Prime q) (hq7 : q ≠ 7) (hcop : Nat.Coprime a b)
    (hEq : Fermat7Equation a b c) (hsum : a + b = c + g)
    (hqQ : q ∣ a ^ 2 + a * b + b ^ 2) :
    (q ∣ g ∧ ¬ q ∣ GTail 7 1 g c) ∨ (q ∣ GTail 7 1 g c ∧ ¬ q ∣ g) := by
  have hc := not_prime_dvd_endpoint_of_quadratic hq hcop hEq hqQ
  have hexclude : q ∣ g → ¬ q ∣ GTail 7 1 g c := fun hd =>
    not_prime_dvd_gtail_seven_of_gap hq hq7 hd hc
  have hprod : q ∣ g * GTail 7 1 g c := by
    rw [gtail_seven_eq_of_fermat7Equation hEq hsum]
    exact dvd_mul_of_dvd_right (hqQ.trans (dvd_pow_self _ (by decide : 2 ≠ 0))) _
  by_cases hg : q ∣ g
  · exact Or.inl ⟨hg, hexclude hg⟩
  · exact Or.inr ⟨(hq.dvd_mul.mp hprod).resolve_left hg, hg⟩

private theorem focused_gap_tail_ne_zero {a b c g : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hEq : Fermat7Equation a b c)
    (hsum : a + b = c + g) : g ≠ 0 ∧ GTail 7 1 g c ≠ 0 := by
  have hheight := (fermat7_focused_bounds ha hb hEq).2
  have hg : g ≠ 0 := by omega
  refine ⟨hg, ?_⟩
  intro hzero
  have hprod := gtail_seven_eq_of_fermat7Equation hEq hsum
  rw [hzero, mul_zero] at hprod
  have hpositive : 0 < 7 * a * b * (a + b) * (a ^ 2 + a * b + b ^ 2) ^ 2 := by
    positivity
  omega

/-- The exact q-local valuation budget with proved ordinary-factor units. -/
theorem padicValNat_focused_quadratic_budget {q a b c g : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hcop : Nat.Coprime a b)
    (hEq : Fermat7Equation a b c) (hsum : a + b = c + g)
    (hq : Nat.Prime q) (hq7 : q ≠ 7) (hqQ : q ∣ a ^ 2 + a * b + b ^ 2) :
    padicValNat q g + padicValNat q (GTail 7 1 g c) =
      2 * padicValNat q (a ^ 2 + a * b + b ^ 2) := by
  have hunit := not_prime_dvd_coordinate_product_of_quadratic hq hcop hqQ
  have hua : ¬ q ∣ a := fun hd => hunit (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hd _) _)
  have hub : ¬ q ∣ b := fun hd => hunit (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hd _) _)
  have huSum : ¬ q ∣ a + b := fun hd => hunit (dvd_mul_of_dvd_right hd _)
  have hne := focused_gap_tail_ne_zero ha hb hEq hsum
  exact padicValNat_prime_square_product hq hq7 hne.1 hne.2
    (Nat.ne_of_gt ha) (Nat.ne_of_gt hb) (by positivity) (by positivity)
    (gtail_seven_eq_of_fermat7Equation hEq hsum) hua hub huSum

/-- Local head exclusion upgrades the budget to an unsplit square allocation. -/
theorem prime_square_focused_allocation {q a b c g : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hcop : Nat.Coprime a b)
    (hEq : Fermat7Equation a b c) (hsum : a + b = c + g)
    (hq : Nat.Prime q) (hq7 : q ≠ 7) (hqQ : q ∣ a ^ 2 + a * b + b ^ 2) :
    (q ^ 2 ∣ g ∧ ¬ q ∣ GTail 7 1 g c) ∨
      (q ^ 2 ∣ GTail 7 1 g c ∧ ¬ q ∣ g) := by
  have hne := focused_gap_tail_ne_zero ha hb hEq hsum
  have hc := not_prime_dvd_endpoint_of_quadratic hq hcop hEq hqQ
  exact prime_square_allocation_of_budget hq hne.1 hne.2 (by positivity) hqQ
    (padicValNat_focused_quadratic_budget ha hb hcop hEq hsum hq hq7 hqQ)
    (fun hd => not_prime_dvd_gtail_seven_of_gap hq hq7 hd hc)

end DkMath.FLT.Seven
