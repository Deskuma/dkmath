/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Cosmic.GTailNat
import DkMath.Lib.NumberTheory.PadicValNat

#print "file: DkMath.Lib.Cosmic.GTailSevenPrimeAllocation"

/-!
# Neutral q-local allocation

The head-unit exclusion concerns the actual seven-row GTail. The abstract
product budget alone allows mixed allocation; its square upgrade separately
requires an exclusion premise. No Fermat equation is imported here.
-/

namespace DkMath.CosmicFormula

/-- A prime other than seven dividing the gap cannot divide a unit-head tail. -/
theorem not_prime_dvd_gtail_seven_of_gap {q g c : ℕ}
    (hq : Nat.Prime q) (hq7 : q ≠ 7) (hgap : q ∣ g) (hc : ¬ q ∣ c) :
    ¬ q ∣ GTail 7 1 g c := by
  have hqseven : ¬ q ∣ 7 := by
    intro hd
    exact hq7 ((Nat.prime_dvd_prime_iff_eq hq (by decide : Nat.Prime 7)).mp hd)
  apply GTail_not_dvd_of_head_unit_of_prime_dvd_x hq (by decide : 1 < 7) _ hgap
  simpa using (show ¬ q ∣ 7 * c ^ 6 from fun hd =>
    (hq.dvd_mul.mp hd).elim hqseven (fun hpow => hc (hq.dvd_of_dvd_pow hpow)))

/-- Unit ordinary factors give the doubled quadratic budget in an exact product. -/
theorem padicValNat_prime_square_product {q g T A B C Q : ℕ}
    (hq : Nat.Prime q) (hq7 : q ≠ 7)
    (hg : g ≠ 0) (hT : T ≠ 0) (hA : A ≠ 0) (hB : B ≠ 0)
    (hC : C ≠ 0) (hQ : Q ≠ 0)
    (hprod : g * T = 7 * A * B * C * Q ^ 2)
    (huA : ¬ q ∣ A) (huB : ¬ q ∣ B) (huC : ¬ q ∣ C) :
    padicValNat q g + padicValNat q T = 2 * padicValNat q Q := by
  let : Fact (Nat.Prime q) := ⟨hq⟩
  have hu7 : ¬ q ∣ 7 := fun hd =>
    hq7 ((Nat.prime_dvd_prime_iff_eq hq (by decide : Nat.Prime 7)).mp hd)
  have h7A : 7 * A ≠ 0 := mul_ne_zero (by decide) hA
  have h7AB : 7 * A * B ≠ 0 := mul_ne_zero h7A hB
  have h7ABC : 7 * A * B * C ≠ 0 := mul_ne_zero h7AB hC
  have hv := congrArg (padicValNat q) hprod
  rw [padicValNat.mul hg hT, padicValNat.mul h7ABC (pow_ne_zero _ hQ),
    padicValNat.mul h7AB hC, padicValNat.mul h7A hB,
    padicValNat.mul (by decide : 7 ≠ 0) hA, padicValNat.pow,
    padicValNat.eq_zero_of_not_dvd hu7, padicValNat.eq_zero_of_not_dvd huA,
    padicValNat.eq_zero_of_not_dvd huB, padicValNat.eq_zero_of_not_dvd huC] at hv
  simpa using hv

/-- The square budget allocates to one factor only after mixed support is excluded. -/
theorem prime_square_allocation_of_budget {q g T Q : ℕ}
    (hq : Nat.Prime q) (hg : g ≠ 0) (hT : T ≠ 0) (hQ : Q ≠ 0) (hqQ : q ∣ Q)
    (hbudget : padicValNat q g + padicValNat q T = 2 * padicValNat q Q)
    (hexclude : q ∣ g → ¬ q ∣ T) :
    (q ^ 2 ∣ g ∧ ¬ q ∣ T) ∨ (q ^ 2 ∣ T ∧ ¬ q ∣ g) := by
  have hge := (DkMath.Lib.NumberTheory.Vp_ge_one_iff hq hQ).mpr hqQ
  by_cases hqg : q ∣ g
  · have hnT := hexclude hqg
    have hvT := padicValNat.eq_zero_of_not_dvd hnT
    have htwo : 2 ≤ padicValNat q g := by omega
    exact Or.inl ⟨(DkMath.Lib.NumberTheory.padicValNat_le_iff_dvd hq hg 2).mp htwo, hnT⟩
  · have hvg := padicValNat.eq_zero_of_not_dvd hqg
    have htwo : 2 ≤ padicValNat q T := by omega
    exact Or.inr ⟨(DkMath.Lib.NumberTheory.padicValNat_le_iff_dvd hq hT 2).mp htwo, hqg⟩

end DkMath.CosmicFormula
