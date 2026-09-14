/-
Copyright (c) 2026 DkMath contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: DkMath contributors.
-/

import DkMath.Gnomon.Algebra
import Mathlib.Data.Nat.Prime.Basic

#print "file: DkMath.Gnomon.PetalPrime"

/-!
# Prime odd gnomons and Petal atomicity

The odd-gnomon map transports Petal multiplication to ordinary multiplication:

`oddGnomon (petalMul a b) = oddGnomon a * oddGnomon b`.

This module records the corresponding atomicity statement.  It is purely
algebraic and does not prove existence of new primes.
-/

namespace DkMath.Gnomon

/-- A non-unit Petal address that has no factorization into two non-unit Petal
addresses.  The Petal multiplicative unit is address `0`. -/
def PetalAtom (n : ℕ) : Prop :=
  n ≠ 0 ∧ ∀ a b, n = petalMul a b → a = 0 ∨ b = 0

/-- Every odd natural number has an odd-gnomon address. -/
theorem exists_eq_oddGnomon_of_odd
    {m : ℕ} (hm : Odd m) :
    ∃ n : ℕ, oddGnomon n = m := by
  rcases hm with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [oddGnomon] using hn.symm

/-- The odd-gnomon address of an odd number is unique. -/
theorem existsUnique_eq_oddGnomon_of_odd
    {m : ℕ} (hm : Odd m) :
    ∃! n : ℕ, oddGnomon n = m := by
  obtain ⟨n, hn⟩ := exists_eq_oddGnomon_of_odd hm
  refine ⟨n, hn, ?_⟩
  intro k hk
  exact oddGnomon_injective (hk.trans hn.symm)

/-- Prime odd gnomons are exactly the non-unit atoms for Petal multiplication. -/
theorem prime_oddGnomon_iff_petalAtom (n : ℕ) :
    Nat.Prime (oddGnomon n) ↔ PetalAtom n := by
  constructor
  · intro hp
    constructor
    · intro hn
      subst n
      exact hp.ne_one oddGnomon_zero
    · intro a b hab
      have hprod : oddGnomon n = oddGnomon a * oddGnomon b := by
        rw [hab, oddGnomon_petalMul]
      have hdivA : oddGnomon a ∣ oddGnomon n :=
        ⟨oddGnomon b, hprod⟩
      rcases hp.eq_one_or_self_of_dvd (oddGnomon a) hdivA with ha1 | haSelf
      · exact Or.inl ((oddGnomon_eq_one_iff a).mp ha1)
      · right
        have hcancel : oddGnomon n * 1 = oddGnomon n * oddGnomon b := by
          rw [Nat.mul_one]
          calc
            oddGnomon n = oddGnomon a * oddGnomon b := hprod
            _ = oddGnomon n * oddGnomon b := by rw [haSelf]
        have hb1 : oddGnomon b = 1 :=
          (Nat.mul_left_cancel (oddGnomon_pos n) hcancel).symm
        exact (oddGnomon_eq_one_iff b).mp hb1
  · intro hAtom
    rw [Nat.prime_def_lt]
    constructor
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hAtom.1
      simp only [oddGnomon]
      omega
    · intro m hmlt hmdvd
      have hmOdd : Odd m := (oddGnomon_odd n).of_dvd_nat hmdvd
      obtain ⟨a, ha⟩ := exists_eq_oddGnomon_of_odd hmOdd
      rcases hmdvd with ⟨k, hk⟩
      have hkDvd : k ∣ oddGnomon n := by
        refine ⟨m, ?_⟩
        simpa [Nat.mul_comm] using hk
      have hkOdd : Odd k := (oddGnomon_odd n).of_dvd_nat hkDvd
      obtain ⟨b, hb⟩ := exists_eq_oddGnomon_of_odd hkOdd
      have hprod : oddGnomon n = oddGnomon a * oddGnomon b := by
        rw [ha, hb]
        exact hk
      have haddr : n = petalMul a b := by
        apply oddGnomon_injective
        rw [oddGnomon_petalMul]
        exact hprod
      rcases hAtom.2 a b haddr with ha0 | hb0
      · rw [ha0, oddGnomon_zero] at ha
        exact ha.symm
      · have hna : n = a := by
          simpa [hb0] using haddr
        have hmeq : m = oddGnomon n := by
          calc
            m = oddGnomon a := ha.symm
            _ = oddGnomon n := by rw [hna]
        rw [hmeq] at hmlt
        omega

/-- Every odd prime has a unique Petal / odd-gnomon address. -/
theorem odd_prime_existsUnique_gnomonAddress
    {p : ℕ} (hp : Nat.Prime p) (hp2 : p ≠ 2) :
    ∃! n : ℕ, oddGnomon n = p := by
  have hpOdd : Odd p := (hp.eq_two_or_odd).resolve_left hp2
  obtain ⟨n, hn⟩ := exists_eq_oddGnomon_of_odd hpOdd
  refine ⟨n, hn, ?_⟩
  intro m hm
  exact oddGnomon_injective (hm.trans hn.symm)

end DkMath.Gnomon

#print axioms DkMath.Gnomon.prime_oddGnomon_iff_petalAtom
#print axioms DkMath.Gnomon.odd_prime_existsUnique_gnomonAddress
