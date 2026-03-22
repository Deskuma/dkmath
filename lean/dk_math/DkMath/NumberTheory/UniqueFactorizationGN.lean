/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Basic.Nat
import DkMath.NumberTheory.Gcd.GN
import Mathlib

/-!
# DkMath.NumberTheory.UniqueFactorizationGN

Prototype (Mathlib-dependent) lemmas for uniqueness of factorization on `ℕ`.
The goal is to solidify the proof skeleton first, then move heavy dependencies
behind wrappers/bridges in later phases.
-/

namespace DkMath.NumberTheory

open DkMath.CosmicFormulaBinom

/-- Prime membership in `factorization.support` is equivalent to divisibility. -/
lemma prime_mem_support_iff_dvd {n p : ℕ} (hn : n ≠ 0) (hp : Nat.Prime p) :
    p ∈ n.factorization.support ↔ p ∣ n := by
  constructor
  · intro h
    exact (DkMath.Basic.Nat.mem_support_factorization_iff.mp h).2.2
  · intro h
    exact DkMath.Basic.Nat.mem_support_factorization_iff.mpr ⟨hn, hp, h⟩

/-- If prime divisibility matches pointwise, supports of factorizations match. -/
lemma support_eq_of_primewise_dvd_iff {m n : ℕ}
    (hm : m ≠ 0) (hn : n ≠ 0)
    (h : ∀ p : ℕ, Nat.Prime p → (p ∣ m ↔ p ∣ n)) :
    m.factorization.support = n.factorization.support := by
  ext p
  constructor
  · intro hp_mem
    have hp : Nat.Prime p := (DkMath.Basic.Nat.mem_support_factorization_iff.mp hp_mem).2.1
    have hpm : p ∣ m := (prime_mem_support_iff_dvd (n := m) (p := p) hm hp).1 hp_mem
    have hpn : p ∣ n := (h p hp).1 hpm
    exact (prime_mem_support_iff_dvd (n := n) (p := p) hn hp).2 hpn
  · intro hp_mem
    have hp : Nat.Prime p := (DkMath.Basic.Nat.mem_support_factorization_iff.mp hp_mem).2.1
    have hpn : p ∣ n := (prime_mem_support_iff_dvd (n := n) (p := p) hn hp).1 hp_mem
    have hpm : p ∣ m := (h p hp).2 hpn
    exact (prime_mem_support_iff_dvd (n := m) (p := p) hm hp).2 hpm

/--
Prime-power divisibility equivalence determines the entire factorization.

This is a prototype theorem that deliberately leans on Mathlib's
`Nat.Prime.pow_dvd_iff_le_factorization`.
-/
theorem factorization_eq_of_prime_pow_dvd_iff {m n : ℕ}
    (hm : m ≠ 0) (hn : n ≠ 0)
    (h : ∀ p k : ℕ, Nat.Prime p → (p ^ k ∣ m ↔ p ^ k ∣ n)) :
    m.factorization = n.factorization := by
  ext p
  by_cases hp : Nat.Prime p
  · apply le_antisymm
    · have hpow_m : p ^ m.factorization p ∣ m := by
        exact (hp.pow_dvd_iff_le_factorization hm).2 le_rfl
      have hpow_n : p ^ m.factorization p ∣ n := (h p (m.factorization p) hp).1 hpow_m
      exact (hp.pow_dvd_iff_le_factorization hn).1 hpow_n
    · have hpow_n : p ^ n.factorization p ∣ n := by
        exact (hp.pow_dvd_iff_le_factorization hn).2 le_rfl
      have hpow_m : p ^ n.factorization p ∣ m := (h p (n.factorization p) hp).2 hpow_n
      exact (hp.pow_dvd_iff_le_factorization hm).1 hpow_m
  · simp [Nat.factorization_eq_zero_of_not_prime, hp]

/--
Uniqueness of factorization (prototype form):
if all prime-power divisibility predicates agree, then the naturals are equal.
-/
theorem unique_factorization_nat_via_prime_powers {m n : ℕ}
    (hm : m ≠ 0) (hn : n ≠ 0)
    (h : ∀ p k : ℕ, Nat.Prime p → (p ^ k ∣ m ↔ p ^ k ∣ n)) :
    m = n := by
  have hfac : m.factorization = n.factorization :=
    factorization_eq_of_prime_pow_dvd_iff hm hn h
  calc
    m = m.factorization.support.prod (fun p => p ^ m.factorization p) := by
      simpa using (Nat.factorization_prod_pow_eq_self hm).symm
    _ = n.factorization.support.prod (fun p => p ^ n.factorization p) := by
      simp [hfac]
    _ = n := by
      simpa using Nat.factorization_prod_pow_eq_self hn

/--
GN-side layer separation (right boundary):
if a prime `q` divides the gap `x` and does not divide the exponent `d`,
then under `Nat.Coprime x u` it cannot divide `GN d x u`.
-/
theorem prime_dvd_left_not_dvd_GN_of_coprime_of_not_dvd_exp
    {d x u q : ℕ}
    (hd1 : 1 ≤ d) (hx : 0 < x) (hcop : Nat.Coprime x u)
    (_hqP : Nat.Prime q) (hq_ndvd_d : ¬ q ∣ d)
    (hq_dvd_x : q ∣ x) :
    ¬ q ∣ GN d x u := by
  intro hq_dvd_GN
  have hyz : u < x + u := by omega
  have hcop_zu : Nat.Coprime (x + u) u := (Nat.coprime_add_self_left).2 hcop
  have hgcd_dvd :
      Int.gcd (x : ℤ) (GN d (x : ℤ) (u : ℤ)) ∣ d := by
    have htmp :=
      DkMath.NumberTheory.Gcd.gcd_gap_GN_dvd_exp_int
        (p := d) (z := x + u) (y := u) hd1 hyz hcop_zu
    simpa [Nat.add_sub_cancel_left] using htmp
  have hq_dvd_x_int : (q : ℤ) ∣ (x : ℤ) := by
    exact_mod_cast hq_dvd_x
  have hq_dvd_GN_int : (q : ℤ) ∣ GN d (x : ℤ) (u : ℤ) := by
    have hq_dvd_GN_cast : (q : ℤ) ∣ ((GN d x u : ℕ) : ℤ) := by
      exact_mod_cast hq_dvd_GN
    simpa [GN] using hq_dvd_GN_cast
  have hq_dvd_gcd :
      q ∣ Int.gcd (x : ℤ) (GN d (x : ℤ) (u : ℤ)) :=
    Int.dvd_gcd hq_dvd_x_int hq_dvd_GN_int
  have hq_dvd_d : q ∣ d := dvd_trans hq_dvd_gcd hgcd_dvd
  exact hq_ndvd_d hq_dvd_d

/--
GN-side layer separation (left boundary, swapped GN orientation):
if a prime `q` divides the gap `u` and does not divide the exponent `d`,
then under `Nat.Coprime x u` it cannot divide `GN d u x`.
-/
theorem prime_dvd_right_not_dvd_GN_swap_of_coprime_of_not_dvd_exp
    {d x u q : ℕ}
    (hd1 : 1 ≤ d) (hu : 0 < u) (hcop : Nat.Coprime x u)
    (_hqP : Nat.Prime q) (hq_ndvd_d : ¬ q ∣ d)
    (hq_dvd_u : q ∣ u) :
    ¬ q ∣ GN d u x := by
  simpa using
    (prime_dvd_left_not_dvd_GN_of_coprime_of_not_dvd_exp
      (d := d) (x := u) (u := x) hd1 hu hcop.symm _hqP hq_ndvd_d hq_dvd_u)

end DkMath.NumberTheory
