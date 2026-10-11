/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.GTailFocusedDefectSquareFirewall

#print "file: DkMath.FLT.Seven.GTailFocusedDefectGlobalCapacity"

/-!
# Finite square-support capacity for a signed defect

Distinct prime squares aggregate to an integer modulus. A separate strict
absolute-size bound supplies the zero certificate. Neither collective support
nor this Archimedean bound is inferred from a selected local prime.
-/

namespace DkMath.FLT.Seven.GTailFocusedDefectGlobalCapacity

open scoped BigOperators
open GTailFocusedDefectSquareFirewall

/-- A finite natural modulus, with an empty support giving one. -/
def squarePrimeSupportModulus (S : Finset ℕ) : ℕ := ∏ p ∈ S, p ^ 2

/-- Actual prime certificates make the finite square modulus strictly positive. -/
theorem squarePrimeSupportModulus_pos (S : Finset ℕ) (hs : ∀ p ∈ S, Nat.Prime p) :
    0 < squarePrimeSupportModulus S := by
  exact Finset.prod_pos (fun p hp => pow_pos (hs p hp).pos 2)

/-- Finite product powers identify the modulus with the square of the distinct-prime product. -/
theorem squarePrimeSupportModulus_eq (S : Finset ℕ) :
    squarePrimeSupportModulus S = (∏ p ∈ S, p) ^ 2 := Finset.prod_pow S 2 id

private theorem square_support_dvd_nat (S : Finset ℕ) (n : ℕ)
    (hs : ∀ p ∈ S, Nat.Prime p) (hlocal : ∀ p ∈ S, p ^ 2 ∣ n) :
    squarePrimeSupportModulus S ∣ n := by
  induction S using Finset.induction_on with
  | empty => simp [squarePrimeSupportModulus]
  | @insert p S hp ih =>
    have hprime := hs p (Finset.mem_insert_self p S)
    have hsS : ∀ r ∈ S, Nat.Prime r := fun r hr => hs r (Finset.mem_insert_of_mem hr)
    have hcop : Nat.Coprime (p ^ 2) (squarePrimeSupportModulus S) := by
      apply Nat.coprime_prod_right_iff.mpr
      intro r hr
      have hne : p ≠ r := fun he => hp (he.symm ▸ hr)
      exact ((Nat.coprime_primes hprime (hsS r hr)).mpr hne).pow_left 2 |>.pow_right 2
    rw [squarePrimeSupportModulus, Finset.prod_insert hp]
    exact hcop.mul_dvd_of_dvd_of_dvd (hlocal p (Finset.mem_insert_self p S))
      (ih hsS (fun r hr => hlocal r (Finset.mem_insert_of_mem hr)))

/-- Distinct prime-square congruences aggregate, and product divisibility recovers every factor. -/
theorem squarePrimeSupportModulus_dvd_iff (S : Finset ℕ) (z : ℤ)
    (hs : ∀ p ∈ S, Nat.Prime p) :
    (squarePrimeSupportModulus S : ℤ) ∣ z ↔ ∀ p ∈ S, (p : ℤ) ^ 2 ∣ z := by
  constructor
  · intro hm p hp
    have hf : p ^ 2 ∣ squarePrimeSupportModulus S := Finset.dvd_prod_of_mem (fun r => r ^ 2) hp
    have hn := hf.trans (Int.natCast_dvd.mp hm)
    have hi := Int.natCast_dvd.mpr hn
    exact_mod_cast hi
  · intro hlocal
    apply Int.natCast_dvd.mpr
    apply square_support_dvd_nat S z.natAbs hs
    intro p hp
    have hi : ((p ^ 2 : ℕ) : ℤ) ∣ z := by exact_mod_cast hlocal p hp
    exact Int.natCast_dvd.mp hi

/-- A divisor and a strict absolute-size bound force zero, with signs retained. -/
theorem int_zero_of_modulus_size {m : ℕ} {z : ℤ}
    (hdiv : (m : ℤ) ∣ z) (hsize : z.natAbs < m) : z = 0 := by
  apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdiv
  simpa only [Int.natAbs_natCast] using hsize

/-- Nonzero signed multiples have absolute value at least their natural modulus. -/
theorem int_nonzero_modulus_bound {m : ℕ} {z : ℤ}
    (hdiv : (m : ℤ) ∣ z) (hz : z ≠ 0) : m ≤ z.natAbs := by
  simpa only [Int.natAbs_natCast] using Int.natAbs_le_of_dvd_ne_zero hdiv hz

/-- Collective prime-square support plus an independent size bound is a zero certificate. -/
theorem finite_support_zero (S : Finset ℕ) (z : ℤ) (hs : ∀ p ∈ S, Nat.Prime p)
    (hlocal : ∀ p ∈ S, (p : ℤ) ^ 2 ∣ z)
    (hsize : z.natAbs < squarePrimeSupportModulus S) : z = 0 :=
  int_zero_of_modulus_size ((squarePrimeSupportModulus_dvd_iff S z hs).mpr hlocal) hsize

/-- Full finite congruence support alone gives only the nonzero capacity lower bound. -/
theorem finite_support_nonzero_bound (S : Finset ℕ) (z : ℤ) (hs : ∀ p ∈ S, Nat.Prime p)
    (hlocal : ∀ p ∈ S, (p : ℤ) ^ 2 ∣ z) (hz : z ≠ 0) :
    squarePrimeSupportModulus S ≤ z.natAbs :=
  int_nonzero_modulus_bound ((squarePrimeSupportModulus_dvd_iff S z hs).mpr hlocal) hz

/-- The Fermat-facing certificate keeps collective support and the size bound explicit. -/
theorem finite_defect_zero_certificate (S : Finset ℕ) (a b c : ℕ)
    (hs : ∀ p ∈ S, Nat.Prime p)
    (hlocal : ∀ p ∈ S, (p : ℤ) ^ 2 ∣ focusedFermatDefect a b c)
    (hsize : (focusedFermatDefect a b c).natAbs < squarePrimeSupportModulus S) :
    Fermat7Equation a b c :=
  focusedFermatDefect_zero_iff.mp (finite_support_zero S _ hs hlocal hsize)

/-- The actual full quadratic support consists of primes dividing the nonzero quadratic. -/
theorem quadratic_prime_support (a b : ℕ) (hQ0 : a ^ 2 + a * b + b ^ 2 ≠ 0)
    {p : ℕ} (hp : p ∈ Nat.primeFactors (a ^ 2 + a * b + b ^ 2)) :
    Nat.Prime p ∧ p ∣ a ^ 2 + a * b + b ^ 2 := by
  exact (Nat.mem_primeFactors_of_ne_zero hQ0).mp hp

/-- The full distinct-prime square modulus divides Q squared, using the existing product lemma. -/
theorem quadratic_modulus_dvd_square (a b : ℕ) :
    squarePrimeSupportModulus (Nat.primeFactors (a ^ 2 + a * b + b ^ 2)) ∣
      (a ^ 2 + a * b + b ^ 2) ^ 2 := by
  rw [squarePrimeSupportModulus_eq]
  exact pow_dvd_pow_of_dvd (Nat.prod_primeFactors_dvd _) 2

/-- For nonzero Q the full-support square capacity is at most Q squared. -/
theorem quadratic_modulus_le_square (a b : ℕ) (hQ0 : a ^ 2 + a * b + b ^ 2 ≠ 0) :
    squarePrimeSupportModulus (Nat.primeFactors (a ^ 2 + a * b + b ^ 2)) ≤
      (a ^ 2 + a * b + b ^ 2) ^ 2 :=
  Nat.le_of_dvd (pow_pos (Nat.pos_of_ne_zero hQ0) 2) (quadratic_modulus_dvd_square a b)

/-- The full-Q zero certificate exposes both missing collective support and magnitude bound. -/
theorem full_quadratic_defect_zero_certificate (a b c : ℕ)
    (hQ0 : a ^ 2 + a * b + b ^ 2 ≠ 0)
    (hsupport : ∀ p ∈ Nat.primeFactors (a ^ 2 + a * b + b ^ 2),
      (p : ℤ) ^ 2 ∣ focusedFermatDefect a b c)
    (hsize : (focusedFermatDefect a b c).natAbs <
      squarePrimeSupportModulus (Nat.primeFactors (a ^ 2 + a * b + b ^ 2))) :
    Fermat7Equation a b c :=
  finite_defect_zero_certificate _ a b c
    (fun p hp => (quadratic_prime_support a b hQ0 (p := p) hp).1) hsupport hsize

end DkMath.FLT.Seven.GTailFocusedDefectGlobalCapacity
