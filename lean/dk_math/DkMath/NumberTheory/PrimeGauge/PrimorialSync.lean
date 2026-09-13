/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: DkMath contributors.
-/

import DkMath.NumberTheory.PrimeGauge.Return
import DkMath.NumberTheory.Primitive.PrimeWorldRefinement

#print "file: DkMath.NumberTheory.PrimeGauge.PrimorialSync"

/-!
# Finite Prime Gauge synchronization

This module packages the common return period of a finite certified prime
family.  It deliberately keeps the family synchronization statement separate
from the order of any product kernel and from all Goldbach or prime-existence
claims.
-/

namespace DkMath.NumberTheory.PrimeGauge

open DkMath.CosmicFormula.Rotation.CF2D
open DkMath.NumberTheory
open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.StructuralArithmetic

private theorem primeWorldModulus_dvd_of_dvd_each
    {S : Finset ℕ} (hS : KnownPrimeScales S) {n : ℕ}
    (hdiv : ∀ p ∈ S, p ∣ n) :
    primeWorldModulus S ∣ n := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp [primeWorldModulus]
  | @insert p S hpS ih =>
      have hpPrime : Nat.Prime p := hS (Finset.mem_insert_self p S)
      have hS' : KnownPrimeScales S := by
        intro q hq
        exact hS (Finset.mem_insert_of_mem hq)
      have hdivS : ∀ q ∈ S, q ∣ n := by
        intro q hq
        exact hdiv q (Finset.mem_insert_of_mem hq)
      have hProductS : primeWorldModulus S ∣ n := ih hS' hdivS
      have hpN : p ∣ n := hdiv p (Finset.mem_insert_self p S)
      have hCoprime : Nat.Coprime p (primeWorldModulus S) := by
        unfold primeWorldModulus
        rw [Nat.coprime_prod_right_iff]
        intro q hq
        apply (Nat.coprime_primes hpPrime
          (hS (Finset.mem_insert_of_mem hq))).mpr
        intro hpq
        apply hpS
        simpa [hpq] using hq
      have hProduct : p * primeWorldModulus S ∣ n :=
        hCoprime.mul_dvd_of_dvd_of_dvd hpN hProductS
      simpa [primeWorldModulus, hpS] using hProduct

/-- Simultaneous return of every member of `S` is exactly divisibility by the
finite prime-world modulus. -/
theorem all_primeGauge_return_iff_worldModulus_dvd
    {S : Finset ℕ} (hS : KnownPrimeScales S) {n : ℕ} :
    (∀ p ∈ S, regularKernel p ^ n = 1) ↔
      primeWorldModulus S ∣ n := by
  constructor
  · intro hreturn
    apply primeWorldModulus_dvd_of_dvd_each hS
    intro p hp
    apply (regularKernel_pow_eq_one_iff_dvd (k := p) (n := n)
      (hS hp).pos).mp
    exact hreturn p hp
  · intro hmod p hp
    apply (regularKernel_pow_eq_one_iff_dvd (k := p) (n := n)
      (hS hp).pos).mpr
    exact (dvd_primeWorldModulus_of_mem hp).trans hmod

/-- The finite prime-world modulus is the least positive simultaneous return. -/
theorem primeGauge_worldModulus_is_first_positive_sync
    {S : Finset ℕ} (hS : KnownPrimeScales S) :
    0 < primeWorldModulus S ∧
      (∀ p ∈ S, regularKernel p ^ primeWorldModulus S = 1) ∧
      ∀ n : ℕ, 0 < n →
        (∀ p ∈ S, regularKernel p ^ n = 1) →
          primeWorldModulus S ≤ n := by
  have hMpos : 0 < primeWorldModulus S := by
    simpa [primeWorldModulus] using
      (Finset.prod_pos (s := S) (f := fun p : ℕ => p)
        (fun p hp => (hS hp).pos))
  refine ⟨hMpos, ?_, ?_⟩
  · exact (all_primeGauge_return_iff_worldModulus_dvd hS).mpr
      (dvd_refl (primeWorldModulus S))
  · intro n hn hreturn
    exact Nat.le_of_dvd hn
      ((all_primeGauge_return_iff_worldModulus_dvd hS).mp hreturn)

end DkMath.NumberTheory.PrimeGauge
