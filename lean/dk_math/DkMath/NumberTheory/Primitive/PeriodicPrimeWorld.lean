/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Nat.Prime.Basic
import DkMath.NumberTheory.Primitive.FinitePrimeWorld

#print "file: DkMath.NumberTheory.Primitive.PeriodicPrimeWorld"

/-!
## Periodicity of a finite prime world

The product of a finite support set is a period for its divisibility waves.
This module formalizes repetition of the semantic support pattern under
translation by that product and its multiples.  A support-disjoint position
remains only a candidate seat: no primality conclusion is made here.

The set is intentionally arbitrary.  It need not be an initial prime segment,
so the modulus is a finite-world product rather than a primorial.
-/

namespace DkMath.NumberTheory.Primitive

open scoped BigOperators
open DkMath.NumberTheory.StructuralArithmetic

/-- The product modulus attached to an arbitrary finite world `S`. -/
def primeWorldModulus (S : Finset ℕ) : ℕ :=
  ∏ p ∈ S, p

/-- Every member of a finite world divides its product modulus. -/
theorem dvd_primeWorldModulus_of_mem
    {S : Finset ℕ} {q : ℕ} (hq : q ∈ S) :
    q ∣ primeWorldModulus S := by
  simpa [primeWorldModulus] using
    (Finset.dvd_prod_of_mem (fun p : ℕ => p) hq)

/--
Support disjointness is invariant under translation by one full finite-world
period.
-/
theorem supportDisjointFrom_add_primeWorldModulus_iff
    {S : Finset ℕ} {m : ℕ} :
    SupportDisjointFrom S (m + primeWorldModulus S) ↔
      SupportDisjointFrom S m := by
  constructor
  · intro hdisj q hq hqd hqmem
    have hqperiod : q ∣ primeWorldModulus S :=
      dvd_primeWorldModulus_of_mem hqmem
    have hqsum : q ∣ m + primeWorldModulus S := dvd_add hqd hqperiod
    exact hdisj hq hqsum hqmem
  · intro hdisj q hq hqsum hqmem
    have hqperiod : q ∣ primeWorldModulus S :=
      dvd_primeWorldModulus_of_mem hqmem
    exact hdisj hq ((Nat.dvd_add_iff_left hqperiod).mpr hqsum) hqmem

/--
Support disjointness is invariant under translation by any multiple of the
finite-world product modulus.  This is the generic periodic observer theorem.
-/
theorem supportDisjointFrom_add_mul_primeWorldModulus_iff
    {S : Finset ℕ} {m k : ℕ} :
    SupportDisjointFrom S (m + k * primeWorldModulus S) ↔
      SupportDisjointFrom S m := by
  constructor
  · intro hdisj q hq hqd hqmem
    have hqperiod : q ∣ primeWorldModulus S :=
      dvd_primeWorldModulus_of_mem hqmem
    have hqmul : q ∣ k * primeWorldModulus S :=
      dvd_mul_of_dvd_right hqperiod k
    have hqsum : q ∣ m + k * primeWorldModulus S := dvd_add hqd hqmul
    exact hdisj hq hqsum hqmem
  · intro hdisj q hq hqsum hqmem
    have hqperiod : q ∣ primeWorldModulus S :=
      dvd_primeWorldModulus_of_mem hqmem
    have hqmul : q ∣ k * primeWorldModulus S :=
      dvd_mul_of_dvd_right hqperiod k
    exact hdisj hq ((Nat.dvd_add_iff_left hqmul).mpr hqsum) hqmem

/--
For a certified prime world, support disjointness is equivalent to coprimality
with the world modulus.
-/
theorem supportDisjointFrom_iff_coprime_primeWorldModulus
    {S : Finset ℕ} (hS : KnownPrimeScales S) {m : ℕ} :
    SupportDisjointFrom S m ↔ Nat.Coprime m (primeWorldModulus S) := by
  constructor
  · intro hdisj
    apply Nat.coprime_of_dvd'
    intro q hq hqm hqmod
    obtain ⟨a, haS, hqa⟩ :=
      (hq.prime.dvd_finsetProd_iff (fun p : ℕ => p)).mp (by
        simpa [primeWorldModulus] using hqmod)
    have hqa_eq : q = a :=
      ((Nat.dvd_prime (hS haS)).mp hqa).resolve_left hq.ne_one
    have hqS : q ∈ S := by simpa [hqa_eq] using haS
    exact False.elim (hdisj hq hqm hqS)
  · intro hcop q hq hqm hqS
    exact (Nat.not_coprime_of_dvd_of_dvd hq.one_lt hqm
      (dvd_primeWorldModulus_of_mem hqS)) hcop

/--
The support observer depends only on the residue modulo its finite-world
modulus.  The statement also covers the empty-world modulus `1` case.
-/
theorem supportDisjointFrom_mod_primeWorldModulus_iff
    {S : Finset ℕ} {m : ℕ} :
    SupportDisjointFrom S (m % primeWorldModulus S) ↔
      SupportDisjointFrom S m := by
  simpa [Nat.mod_add_div, mul_comm] using
    (supportDisjointFrom_add_mul_primeWorldModulus_iff
      (S := S) (m := m % primeWorldModulus S)
      (k := m / primeWorldModulus S)).symm

/-- The canonical bounded prime world inherits the generic period theorem. -/
theorem supportDisjointFrom_primeScalesUpTo_add_period_iff
    {P m k : ℕ} :
    SupportDisjointFrom
        (primeScalesUpTo P)
        (m + k * primeWorldModulus (primeScalesUpTo P)) ↔
      SupportDisjointFrom (primeScalesUpTo P) m :=
  supportDisjointFrom_add_mul_primeWorldModulus_iff

end DkMath.NumberTheory.Primitive
