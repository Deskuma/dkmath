/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.Fermat

#print "file: DkMath.NumberTheory.EuclideanGeometry.FermatForm"

/-!
# Fermat form for Gauss-Wantzel indices

This module isolates the arithmetic shape that occurs in the classical
Gauss-Wantzel criterion.  It does not define geometric constructibility and
does not assert that the five currently known Fermat primes are the only ones.

A finite set of indices records distinct Fermat numbers by construction.
Primality remains an explicit hypothesis for every selected index.
-/

namespace DkMath.NumberTheory.EuclideanGeometry

open scoped Nat
open Finset

/-- The product of the Fermat numbers selected by a finite index set. -/
def fermatProduct (s : Finset ℕ) : ℕ :=
  ∏ i ∈ s, Nat.fermatNumber i

/-- An index selects a Fermat prime when its Fermat number is prime. -/
def IsFermatPrimeIndex (i : ℕ) : Prop :=
  Nat.Prime (Nat.fermatNumber i)

/--
The arithmetic Gauss-Wantzel form: a power of two times a finite product of
Fermat primes with distinct indices.

This predicate is purely number theoretic.  Its relation to straightedge-and-
compass construction belongs to a separate bridge layer.
-/
def IsGaussWantzelIndex (n : ℕ) : Prop :=
  ∃ a : ℕ, ∃ s : Finset ℕ,
    (∀ i ∈ s, IsFermatPrimeIndex i) ∧
      n = 2 ^ a * fermatProduct s

/-- Distinct selected Fermat numbers are pairwise coprime. -/
theorem fermatNumbers_pairwise_coprime (s : Finset ℕ) :
    (s : Set ℕ).Pairwise
      (fun i j ↦ Nat.Coprime (Nat.fermatNumber i) (Nat.fermatNumber j)) := by
  intro i _ j _ hij
  exact Nat.coprime_fermatNumber_fermatNumber hij

/-- One is represented by the empty Fermat-prime product. -/
theorem isGaussWantzelIndex_one : IsGaussWantzelIndex 1 := by
  refine ⟨0, ∅, ?_, ?_⟩
  · simp
  · simp [fermatProduct]

/-- Every power of two has Gauss-Wantzel form with empty odd part. -/
theorem isGaussWantzelIndex_two_pow (a : ℕ) :
    IsGaussWantzelIndex (2 ^ a) := by
  refine ⟨a, ∅, ?_, ?_⟩
  · simp
  · simp [fermatProduct]

/-- Every prime Fermat number has Gauss-Wantzel form. -/
theorem isGaussWantzelIndex_fermatNumber {i : ℕ}
    (hi : IsFermatPrimeIndex i) :
    IsGaussWantzelIndex (Nat.fermatNumber i) := by
  refine ⟨0, {i}, ?_, ?_⟩
  · simpa using hi
  · simp [fermatProduct]

/-- The totient of a prime Fermat number is its defining power of two. -/
theorem totient_fermatNumber {i : ℕ} (hi : IsFermatPrimeIndex i) :
    Nat.totient (Nat.fermatNumber i) = 2 ^ (2 ^ i) := by
  rw [Nat.totient_prime hi]
  simp [Nat.fermatNumber]

/-- The totient of a power of two is the power indexed by the predecessor. -/
theorem totient_two_pow (a : ℕ) :
    Nat.totient (2 ^ a) = 2 ^ a.pred := by
  cases a with
  | zero => simp
  | succ a =>
      simpa using Nat.totient_prime_pow_succ Nat.prime_two a

/--
The totient of a finite product of selected Fermat primes is the power of two
whose exponent is the sum of their Fermat exponents.
-/
theorem totient_fermatProduct (s : Finset ℕ)
    (hs : ∀ i ∈ s, IsFermatPrimeIndex i) :
    Nat.totient (fermatProduct s) = 2 ^ (∑ i ∈ s, 2 ^ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [fermatProduct]
  | @insert i s hi ih =>
      have his : IsFermatPrimeIndex i := hs i (by simp)
      have hs' : ∀ j ∈ s, IsFermatPrimeIndex j := by
        intro j hj
        exact hs j (by simp [hj])
      have hcoprime : Nat.Coprime (Nat.fermatNumber i) (fermatProduct s) := by
        rw [fermatProduct, Nat.coprime_prod_right_iff]
        intro j hj
        exact Nat.coprime_fermatNumber_fermatNumber (by
          intro hij
          apply hi
          simpa [hij] using hj)
      rw [show fermatProduct (insert i s) =
          Nat.fermatNumber i * fermatProduct s by
            simp [fermatProduct, hi],
        Nat.totient_mul hcoprime, totient_fermatNumber his, ih hs',
        sum_insert hi, pow_add]

/-- A power of two is coprime to every finite product of Fermat numbers. -/
theorem two_pow_coprime_fermatProduct (a : ℕ) (s : Finset ℕ) :
    Nat.Coprime (2 ^ a) (fermatProduct s) := by
  rw [fermatProduct, Nat.coprime_prod_right_iff]
  intro i _
  exact Nat.Coprime.pow_left a (Nat.odd_fermatNumber i).coprime_two_left

/--
Every Gauss-Wantzel-form index has Euler totient equal to a power of two.

This is the forward arithmetic bridge only.  The converse requires a separate
prime-factor classification argument and is not asserted here.
-/
theorem IsGaussWantzelIndex.exists_totient_eq_two_pow {n : ℕ}
    (hn : IsGaussWantzelIndex n) :
    ∃ e : ℕ, Nat.totient n = 2 ^ e := by
  rcases hn with ⟨a, s, hs, rfl⟩
  refine ⟨a.pred + ∑ i ∈ s, 2 ^ i, ?_⟩
  rw [Nat.totient_mul (two_pow_coprime_fermatProduct a s),
    totient_two_pow, totient_fermatProduct s hs, pow_add]

section InterfaceChecks

#check Nat.fermatNumber
#check Nat.fermatNumber_injective
#check Nat.coprime_fermatNumber_fermatNumber
#check Nat.totient
#check IsGaussWantzelIndex
#check fermatNumbers_pairwise_coprime
#check IsGaussWantzelIndex.exists_totient_eq_two_pow

end InterfaceChecks

end DkMath.NumberTheory.EuclideanGeometry
