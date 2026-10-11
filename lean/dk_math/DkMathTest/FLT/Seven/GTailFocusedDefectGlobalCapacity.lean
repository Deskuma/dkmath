/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.GTailFocusedDefectGlobalCapacity

#print "file: DkMathTest.FLT.Seven.GTailFocusedDefectGlobalCapacity"

namespace DkMathTest.FLT.Seven.GTailFocusedDefectGlobalCapacity

open scoped BigOperators
open DkMath.FLT.Seven DkMath.CosmicFormula
open DkMath.FLT.Seven.GTailFocusedDefectSquareFirewall
open DkMath.FLT.Seven.GTailFocusedDefectGlobalCapacity

section Symbolic

variable (S : Finset ℕ) (z : ℤ) (hs : ∀ p ∈ S, Nat.Prime p)

example : 0 < squarePrimeSupportModulus S := squarePrimeSupportModulus_pos S hs
example : squarePrimeSupportModulus S = (∏ p ∈ S, p) ^ 2 := squarePrimeSupportModulus_eq S
example : (squarePrimeSupportModulus S : ℤ) ∣ z ↔ ∀ p ∈ S, (p : ℤ) ^ 2 ∣ z :=
  squarePrimeSupportModulus_dvd_iff S z hs
example (hlocal : ∀ p ∈ S, (p : ℤ) ^ 2 ∣ z) : squarePrimeSupportModulus S ∣ z.natAbs :=
  Int.natCast_dvd.mp ((squarePrimeSupportModulus_dvd_iff S z hs).mpr hlocal)
example (hlocal : ∀ p ∈ S, (p : ℤ) ^ 2 ∣ z) (hsize : z.natAbs < squarePrimeSupportModulus S) :
    z = 0 := finite_support_zero S z hs hlocal hsize
example (hlocal : ∀ p ∈ S, (p : ℤ) ^ 2 ∣ z) (hz : z ≠ 0) :
    squarePrimeSupportModulus S ≤ z.natAbs := finite_support_nonzero_bound S z hs hlocal hz
example (a b c : ℕ) (hlocal : ∀ p ∈ S, (p : ℤ) ^ 2 ∣ focusedFermatDefect a b c)
    (hsize : (focusedFermatDefect a b c).natAbs < squarePrimeSupportModulus S) :
    Fermat7Equation a b c := finite_defect_zero_certificate S a b c hs hlocal hsize
example (a b : ℕ) (hQ0 : a ^ 2 + a * b + b ^ 2 ≠ 0)
    {p : ℕ} (hp : p ∈ Nat.primeFactors (a ^ 2 + a * b + b ^ 2)) :
    Nat.Prime p ∧ p ∣ a ^ 2 + a * b + b ^ 2 := quadratic_prime_support a b hQ0 hp
example (a b : ℕ) :
    squarePrimeSupportModulus (Nat.primeFactors (a ^ 2 + a * b + b ^ 2)) ∣
      (a ^ 2 + a * b + b ^ 2) ^ 2 := quadratic_modulus_dvd_square a b
example (a b : ℕ) (hQ0 : a ^ 2 + a * b + b ^ 2 ≠ 0) :
    squarePrimeSupportModulus (Nat.primeFactors (a ^ 2 + a * b + b ^ 2)) ≤
      (a ^ 2 + a * b + b ^ 2) ^ 2 := quadratic_modulus_le_square a b hQ0
example (a b c : ℕ) (hQ0 : a ^ 2 + a * b + b ^ 2 ≠ 0)
    (hsupport : ∀ p ∈ Nat.primeFactors (a ^ 2 + a * b + b ^ 2),
      (p : ℤ) ^ 2 ∣ focusedFermatDefect a b c)
    (hsize : (focusedFermatDefect a b c).natAbs <
      squarePrimeSupportModulus (Nat.primeFactors (a ^ 2 + a * b + b ^ 2))) :
    Fermat7Equation a b c := full_quadratic_defect_zero_certificate a b c hQ0 hsupport hsize

-- Equality to the actual defining expression of ABC.rad, with no ABC owner import.
example (n : ℕ) : squarePrimeSupportModulus (Nat.primeFactors n) =
    (n.factorization.support.prod (fun p => p)) ^ 2 := by
  rw [Nat.support_factorization, squarePrimeSupportModulus_eq]

end Symbolic

-- Empty/zero conventions and signed thresholds.
example : squarePrimeSupportModulus ∅ = 1 := rfl
example : squarePrimeSupportModulus (Nat.primeFactors 0) = 1 := by simp [squarePrimeSupportModulus]
example : squarePrimeSupportModulus (Nat.primeFactors 1) = 1 := by simp [squarePrimeSupportModulus]
example : ¬ squarePrimeSupportModulus (Nat.primeFactors 0) ≤ (0 : ℕ) ^ 2 := by simp [squarePrimeSupportModulus]
example : (0 : ℤ) = 0 := int_zero_of_modulus_size (m := 1) (by decide) (by decide)
example : (100 : ℕ) ≤ (-300 : ℤ).natAbs := int_nonzero_modulus_bound (by decide) (by decide)
example : ¬ ((-300 : ℤ).natAbs < (100 : ℕ)) := by decide

-- Distinctness alone does not make nonprime overlapping factors coprime.
example : (4 : ℕ) ∣ 8 ∧ (8 : ℕ) ∣ 8 ∧ ¬ (4 * 8 : ℕ) ∣ 8 := by decide

namespace AbstractCongruence
local notation "S" => ({2, 3} : Finset ℕ)
private theorem primes : ∀ p ∈ S, Nat.Prime p := by
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl <;> decide
example : squarePrimeSupportModulus S = 36 := by decide
example : ∀ p ∈ S, (p : ℤ) ^ 2 ∣ 36 := by
  apply (squarePrimeSupportModulus_dvd_iff S 36 primes).mp
  decide
example : ∀ p ∈ S, (p : ℤ) ^ 2 ∣ -36 := by
  apply (squarePrimeSupportModulus_dvd_iff S (-36) primes).mp
  decide
example : (36 : ℤ) ≠ 0 ∧ ¬ ((36 : ℤ).natAbs < squarePrimeSupportModulus S) := by decide
example : squarePrimeSupportModulus S ≤ (-36 : ℤ).natAbs :=
  finite_support_nonzero_bound S (-36) primes
    ((squarePrimeSupportModulus_dvd_iff S (-36) primes).mp (by decide)) (by decide)
example : (0 : ℤ) = 0 := finite_support_zero S 0 primes (by simp) (by decide)
end AbstractCongruence

namespace Tail43

local notation "Q" => (1166 ^ 2 + 1166 * 1857 + 1857 ^ 2 : ℕ)
local notation "S" => Nat.primeFactors Q
local notation "M" => squarePrimeSupportModulus S
local notation "Δ" => focusedFermatDefect 1166 1857 1858

example : (1166 + 1857 : ℕ) = 1858 + 1165 ∧ Nat.Coprime 1166 1857 ∧
    0 < (1165 : ℕ) ∧ (1165 : ℕ) < 1166 ∧ (1165 : ℕ) < 1857 ∧
    (1166 : ℕ) < 1858 ∧ (1857 : ℕ) < 1858 ∧ (1858 : ℕ) < 1166 + 1857 := by decide
example : Q = 6973267 ∧ Q = 7 * 43 * 23167 := by decide
private theorem primes : Nat.Prime 7 ∧ Nat.Prime 43 ∧ Nat.Prime 23167 := by norm_num
example : Nat.Prime 7 ∧ Nat.Prime 43 ∧ Nat.Prime 23167 := primes
private theorem support : S = ({7, 43, 23167} : Finset ℕ) := by
  rw [show Q = 7 * 43 * 23167 from by decide,
    Nat.primeFactors_mul (by decide : (7 * 43 : ℕ) ≠ 0) (by decide : (23167 : ℕ) ≠ 0),
    Nat.primeFactors_mul (by decide : (7 : ℕ) ≠ 0) (by decide : (43 : ℕ) ≠ 0),
    primes.1.primeFactors, primes.2.1.primeFactors, primes.2.2.primeFactors]
  decide
example : S = ({7, 43, 23167} : Finset ℕ) := support
example : M = 48626452653289 ∧ M = Q ^ 2 ∧ 0 < M := by rw [support]; decide
example : Δ = (2642627963860178152897 : ℤ) ∧ 0 < Δ := by decide
example : (Δ).natAbs = 2642627963860178152897 := by decide
example : (43 : ℤ) ^ 2 ∣ Δ := by decide
example : ¬ (7 : ℤ) ^ 2 ∣ Δ ∧ ¬ (23167 : ℤ) ^ 2 ∣ Δ := by decide
example : ¬ (∀ p ∈ S, (p : ℤ) ^ 2 ∣ Δ) := by
  intro h
  exact (by decide : ¬ (7 : ℤ) ^ 2 ∣ Δ) (h 7 (by rw [support]; decide))
example : M < (Δ).natAbs := by rw [support]; decide
example : ¬ ((Δ).natAbs < M) := by rw [support]; decide
example : M ≤ Q ^ 2 := quadratic_modulus_le_square 1166 1857 (by decide)
example : ¬ Fermat7Equation 1166 1857 1858 :=
  fun h => (by decide : Δ ≠ 0) (focusedFermatDefect_zero_iff.mpr h)
example : ¬ ((1165 : ℕ) * GTail 7 1 1165 1858 = 7 * 1166 * 1857 * (1166 + 1857) * Q ^ 2) := by
  intro h
  have he := (fermat7Equation_iff_focused_scalar_balance
    (by decide : (1166 + 1857 : ℕ) = 1858 + 1165)).mpr h
  exact (by decide : Δ ≠ 0) (focusedFermatDefect_zero_iff.mpr he)

end Tail43

namespace Gap13

local notation "Q" => (196 ^ 2 + 196 * 211 + 211 ^ 2 : ℕ)
local notation "S" => Nat.primeFactors Q
local notation "M" => squarePrimeSupportModulus S
local notation "Δ" => focusedFermatDefect 196 211 238

example : (196 + 211 : ℕ) = 238 + 169 ∧ Nat.Coprime 196 211 ∧
    0 < (169 : ℕ) ∧ (169 : ℕ) < 196 ∧ (169 : ℕ) < 211 ∧
    (196 : ℕ) < 238 ∧ (211 : ℕ) < 238 ∧ (238 : ℕ) < 196 + 211 := by decide
example : Q = 124293 ∧ Q = 3 * 13 * 3187 := by decide
private theorem primes : Nat.Prime 3 ∧ Nat.Prime 13 ∧ Nat.Prime 3187 := by norm_num
example : Nat.Prime 3 ∧ Nat.Prime 13 ∧ Nat.Prime 3187 := primes
private theorem support : S = ({3, 13, 3187} : Finset ℕ) := by
  rw [show Q = 3 * 13 * 3187 from by decide,
    Nat.primeFactors_mul (by decide : (3 * 13 : ℕ) ≠ 0) (by decide : (3187 : ℕ) ≠ 0),
    Nat.primeFactors_mul (by decide : (3 : ℕ) ≠ 0) (by decide : (13 : ℕ) ≠ 0),
    primes.1.primeFactors, primes.2.1.primeFactors, primes.2.2.primeFactors]
  decide
example : S = ({3, 13, 3187} : Finset ℕ) := support
example : M = 15448749849 ∧ M = Q ^ 2 ∧ 0 < M := by rw [support]; decide
example : Δ = (-13523337259569605 : ℤ) ∧ Δ < 0 := by decide
example : (Δ).natAbs = 13523337259569605 := by decide
example : (13 : ℤ) ^ 2 ∣ Δ := by decide
example : ¬ (3 : ℤ) ^ 2 ∣ Δ ∧ ¬ (3187 : ℤ) ^ 2 ∣ Δ := by decide
example : ¬ (∀ p ∈ S, (p : ℤ) ^ 2 ∣ Δ) := by
  intro h
  exact (by decide : ¬ (3 : ℤ) ^ 2 ∣ Δ) (h 3 (by rw [support]; decide))
example : M < (Δ).natAbs := by rw [support]; decide
example : ¬ ((Δ).natAbs < M) := by rw [support]; decide
example : M ≤ Q ^ 2 := quadratic_modulus_le_square 196 211 (by decide)
example : ¬ Fermat7Equation 196 211 238 :=
  fun h => (by decide : Δ ≠ 0) (focusedFermatDefect_zero_iff.mpr h)
example : ¬ ((169 : ℕ) * GTail 7 1 169 238 = 7 * 196 * 211 * (196 + 211) * Q ^ 2) := by
  intro h
  have he := (fermat7Equation_iff_focused_scalar_balance
    (by decide : (196 + 211 : ℕ) = 238 + 169)).mpr h
  exact (by decide : Δ ≠ 0) (focusedFermatDefect_zero_iff.mpr he)

end Gap13

#check DkMath.FLT.Seven.GTailFocusedDefectGlobalCapacity.squarePrimeSupportModulus
#print axioms DkMath.FLT.Seven.GTailFocusedDefectGlobalCapacity.squarePrimeSupportModulus
#check DkMath.FLT.Seven.GTailFocusedDefectGlobalCapacity.squarePrimeSupportModulus_pos
#print axioms DkMath.FLT.Seven.GTailFocusedDefectGlobalCapacity.squarePrimeSupportModulus_pos
#check DkMath.FLT.Seven.GTailFocusedDefectGlobalCapacity.squarePrimeSupportModulus_eq
#print axioms DkMath.FLT.Seven.GTailFocusedDefectGlobalCapacity.squarePrimeSupportModulus_eq
#check DkMath.FLT.Seven.GTailFocusedDefectGlobalCapacity.squarePrimeSupportModulus_dvd_iff
#print axioms DkMath.FLT.Seven.GTailFocusedDefectGlobalCapacity.squarePrimeSupportModulus_dvd_iff
#check DkMath.FLT.Seven.GTailFocusedDefectGlobalCapacity.int_zero_of_modulus_size
#print axioms DkMath.FLT.Seven.GTailFocusedDefectGlobalCapacity.int_zero_of_modulus_size
#check DkMath.FLT.Seven.GTailFocusedDefectGlobalCapacity.int_nonzero_modulus_bound
#print axioms DkMath.FLT.Seven.GTailFocusedDefectGlobalCapacity.int_nonzero_modulus_bound
#check DkMath.FLT.Seven.GTailFocusedDefectGlobalCapacity.finite_support_zero
#print axioms DkMath.FLT.Seven.GTailFocusedDefectGlobalCapacity.finite_support_zero
#check DkMath.FLT.Seven.GTailFocusedDefectGlobalCapacity.finite_support_nonzero_bound
#print axioms DkMath.FLT.Seven.GTailFocusedDefectGlobalCapacity.finite_support_nonzero_bound
#check DkMath.FLT.Seven.GTailFocusedDefectGlobalCapacity.finite_defect_zero_certificate
#print axioms DkMath.FLT.Seven.GTailFocusedDefectGlobalCapacity.finite_defect_zero_certificate
#check DkMath.FLT.Seven.GTailFocusedDefectGlobalCapacity.quadratic_prime_support
#print axioms DkMath.FLT.Seven.GTailFocusedDefectGlobalCapacity.quadratic_prime_support
#check DkMath.FLT.Seven.GTailFocusedDefectGlobalCapacity.quadratic_modulus_dvd_square
#print axioms DkMath.FLT.Seven.GTailFocusedDefectGlobalCapacity.quadratic_modulus_dvd_square
#check DkMath.FLT.Seven.GTailFocusedDefectGlobalCapacity.quadratic_modulus_le_square
#print axioms DkMath.FLT.Seven.GTailFocusedDefectGlobalCapacity.quadratic_modulus_le_square
#check DkMath.FLT.Seven.GTailFocusedDefectGlobalCapacity.full_quadratic_defect_zero_certificate
#print axioms DkMath.FLT.Seven.GTailFocusedDefectGlobalCapacity.full_quadratic_defect_zero_certificate

end DkMathTest.FLT.Seven.GTailFocusedDefectGlobalCapacity
