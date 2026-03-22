/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Basic.Nat
import Mathlib

/-!
# DkMath.NumberTheory.UniqueFactorizationGN

Prototype (Mathlib-dependent) lemmas for uniqueness of factorization on `ℕ`.
The goal is to solidify the proof skeleton first, then move heavy dependencies
behind wrappers/bridges in later phases.
-/

namespace DkMath.NumberTheory

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

end DkMath.NumberTheory
