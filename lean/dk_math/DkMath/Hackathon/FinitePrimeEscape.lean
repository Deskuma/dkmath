/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Nat.Prime.Basic

namespace DkMath.Hackathon

open scoped BigOperators

/-- A prime divisor of `n` outside the finite reference set `S`. -/
def FreshPrimeFactor (S : Finset ℕ) (n q : ℕ) : Prop :=
  Nat.Prime q ∧ q ∣ n ∧ q ∉ S

/--
A prime divisor of the product-plus-offset boundary cannot be one of the
factors in the product when the product and offset are coprime.
-/
theorem prime_dvd_product_add_coprime_not_mem
    {S : Finset ℕ} {u q : ℕ}
    (hcop : Nat.Coprime (∏ p ∈ S, p) u)
    (hqPrime : Nat.Prime q)
    (hqDiv : q ∣ (∏ p ∈ S, p) + u) :
    q ∉ S := by
  classical
  intro hqMem
  have hqProd : q ∣ ∏ p ∈ S, p :=
    Finset.dvd_prod_of_mem (fun p : ℕ => p) hqMem
  have hqU : q ∣ u :=
    (Nat.dvd_add_iff_right hqProd).mpr hqDiv
  have hqGcd : q ∣ Nat.gcd (∏ p ∈ S, p) u :=
    Nat.dvd_gcd hqProd hqU
  have hgcd : Nat.gcd (∏ p ∈ S, p) u = 1 := hcop
  rw [hgcd] at hqGcd
  exact hqPrime.not_dvd_one hqGcd

/--
Every nontrivial product-plus-offset boundary has a prime divisor outside the
finite reference set when the product and offset are coprime.
-/
theorem exists_fresh_prime_factor
    {S : Finset ℕ} {u : ℕ}
    (hcop : Nat.Coprime (∏ p ∈ S, p) u)
    (hboundary : 1 < (∏ p ∈ S, p) + u) :
    ∃ q, FreshPrimeFactor S ((∏ p ∈ S, p) + u) q := by
  obtain ⟨q, hqPrime, hqDiv⟩ :=
    Nat.ne_one_iff_exists_prime_dvd.mp (Nat.ne_of_gt hboundary)
  refine ⟨q, hqPrime, hqDiv, ?_⟩
  exact prime_dvd_product_add_coprime_not_mem hcop hqPrime hqDiv

end DkMath.Hackathon
