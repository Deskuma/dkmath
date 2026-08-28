/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PrimorialUniverse.FiniteReservationEscape
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Tactic

#print "file: DkMath.NumberTheory.PrimorialUniverse.FinitePrimeSynchronization"

/-!
# Finite prime-scale synchronization

For a finite basis `S` of distinct ordinary primes, the product
`finitePrimeBasisProduct S` is the least common multiple in the divisibility
order: every member of `S` divides it, and it divides every natural divisible
by all members of `S`.  Consequently the reservation sheet defined by `S`
repeats after adding any multiple of this product.

For an initial segment of the primes this product is the ordinary primorial.
This module stops at the finite common period and its exact periodicity law;
it does not define survivor sets or wheels, and makes no claim about
reflection, next-prime deletion, Legendre, or analytic counting.
-/

namespace DkMath.NumberTheory.PrimorialUniverse

open scoped BigOperators

/-! ## Common periods -/

/-- Every member of `S` divides the proposed finite synchronization period. -/
def IsCommonMultipleOfPrimeBasis (S : Finset ℕ) (T : ℕ) : Prop :=
  ∀ p ∈ S, p ∣ T

theorem finitePrimeBasisProduct_isCommonMultiple
    {S : Finset ℕ} :
    IsCommonMultipleOfPrimeBasis S (finitePrimeBasisProduct S) := by
  intro p hp
  exact mem_dvd_finitePrimeBasisProduct hp

/--
The product of a finite prime basis divides every common multiple of that
basis.  Pairwise coprimality comes from distinct members of the `Finset`.
-/
theorem finitePrimeBasisProduct_dvd_of_commonMultiple
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S) {T : ℕ}
    (hT : IsCommonMultipleOfPrimeBasis S T) :
    finitePrimeBasisProduct S ∣ T := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [finitePrimeBasisProduct]
  | @insert p S hpS ih =>
      have hpPrime : Nat.Prime p := hS p (Finset.mem_insert_self p S)
      have hS' : IsFinitePrimeBasis S := by
        intro q hq
        exact hS q (Finset.mem_insert_of_mem hq)
      have hT' : IsCommonMultipleOfPrimeBasis S T := by
        intro q hq
        exact hT q (Finset.mem_insert_of_mem hq)
      have hProductS : finitePrimeBasisProduct S ∣ T := ih hS' hT'
      have hpT : p ∣ T := hT p (Finset.mem_insert_self p S)
      have hCoprime : Nat.Coprime p (finitePrimeBasisProduct S) := by
        unfold finitePrimeBasisProduct
        rw [Nat.coprime_prod_right_iff]
        intro q hq
        apply (Nat.coprime_primes hpPrime (hS q (Finset.mem_insert_of_mem hq))).mpr
        intro hpq
        apply hpS
        simpa [hpq] using hq
      have hProduct : p * finitePrimeBasisProduct S ∣ T :=
        hCoprime.mul_dvd_of_dvd_of_dvd hpT hProductS
      simpa [finitePrimeBasisProduct, hpS] using hProduct

/-- The finite prime-basis product is the least common period in divisibility. -/
theorem finitePrimeBasisProduct_dvd_iff_commonMultiple
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S) {T : ℕ} :
    finitePrimeBasisProduct S ∣ T ↔
      IsCommonMultipleOfPrimeBasis S T := by
  constructor
  · intro hProduct p hp
    exact (mem_dvd_finitePrimeBasisProduct hp).trans hProduct
  · exact finitePrimeBasisProduct_dvd_of_commonMultiple hS

/-! ## Periodicity of the reservation sheet -/

/-- Reservation by a finite prime basis is invariant under its product period. -/
theorem reservedByPrimeBasis_add_mul_period_iff
    {S : Finset ℕ} (_hS : IsFinitePrimeBasis S) (n k : ℕ) :
    ReservedByPrimeBasis S
        (n + k * finitePrimeBasisProduct S) ↔
      ReservedByPrimeBasis S n := by
  constructor
  · rintro ⟨p, hp, hpSum⟩
    refine ⟨p, hp, ?_⟩
    have hpPeriod : p ∣ k * finitePrimeBasisProduct S := by
      simpa [Nat.mul_comm] using
        (mem_dvd_finitePrimeBasisProduct hp).trans
          (dvd_mul_right (finitePrimeBasisProduct S) k)
    exact (Nat.dvd_add_left hpPeriod).mp hpSum
  · rintro ⟨p, hp, hpN⟩
    refine ⟨p, hp, ?_⟩
    have hpPeriod : p ∣ k * finitePrimeBasisProduct S := by
      simpa [Nat.mul_comm] using
        (mem_dvd_finitePrimeBasisProduct hp).trans
          (dvd_mul_right (finitePrimeBasisProduct S) k)
    exact (Nat.dvd_add_left hpPeriod).mpr hpN

/-- The non-reserved (survivor) predicate has the same finite period. -/
theorem not_reserved_add_mul_period_iff
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S) (n k : ℕ) :
    ¬ ReservedByPrimeBasis S
        (n + k * finitePrimeBasisProduct S) ↔
      ¬ ReservedByPrimeBasis S n := by
  exact not_congr (reservedByPrimeBasis_add_mul_period_iff hS n k)

/-! ## Small arithmetic regressions -/

theorem finitePrimeBasisProduct_two_three_five :
    finitePrimeBasisProduct ({2, 3, 5} : Finset ℕ) = 30 := by
  decide

theorem finitePrimeBasisProduct_two_three_five_seven :
    finitePrimeBasisProduct ({2, 3, 5, 7} : Finset ℕ) = 210 := by
  decide

theorem reservedByPrimeBasis_two_three_five_period_regression :
    ReservedByPrimeBasis ({2, 3, 5} : Finset ℕ) 37 ↔
      ReservedByPrimeBasis ({2, 3, 5} : Finset ℕ) 7 := by
  have hS : IsFinitePrimeBasis ({2, 3, 5} : Finset ℕ) := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl <;> norm_num
  have hPeriod := reservedByPrimeBasis_add_mul_period_iff hS 7 1
  convert hPeriod using 1; norm_num [finitePrimeBasisProduct]

end DkMath.NumberTheory.PrimorialUniverse
