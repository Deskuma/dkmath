/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CFBRC.Defs
import Mathlib

namespace DkMath.CFBRC

open scoped BigOperators

open DkMath.CosmicFormulaBinom

lemma cyclotomicPrimeCore_succ {R : Type _} [CommSemiring R] (p : ℕ) (x u : R) :
    cyclotomicPrimeCore (p + 1) x u = u * cyclotomicPrimeCore p x u + (x + u) ^ p := by
  unfold cyclotomicPrimeCore
  rw [Finset.sum_range_succ]
  rw [Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro k hk
    have hk' : k < p := Finset.mem_range.mp hk
    have hsub : p + 1 - 1 - k = p - 1 - k + 1 := by omega
    rw [hsub, pow_succ]
    ring
  · simp

theorem add_pow_eq_mul_cyclotomicPrimeCore_add_gap
    {R : Type _} [CommSemiring R] (p : ℕ) (x u : R) :
    (x + u) ^ p = x * cyclotomicPrimeCore p x u + u ^ p := by
  induction p with
  | zero =>
      simp [cyclotomicPrimeCore]
  | succ p ih =>
      rw [pow_succ', ih, add_mul, mul_add, cyclotomicPrimeCore_succ, pow_succ]
      rw [ih]
      ring

theorem mul_cyclotomicPrimeCore_eq_mul_GN
    {R : Type _} [CommSemiring R] [IsRightCancelAdd R] (p : ℕ) (x u : R) :
    x * cyclotomicPrimeCore p x u = x * GN p x u := by
  have h₁ : (x + u) ^ p = x * cyclotomicPrimeCore p x u + u ^ p :=
    add_pow_eq_mul_cyclotomicPrimeCore_add_gap p x u
  have h₂ : (x + u) ^ p = x * GN p x u + u ^ p := cosmic_id_csr' p x u
  have hcmp : x * cyclotomicPrimeCore p x u + u ^ p = x * GN p x u + u ^ p := h₁.symm.trans h₂
  exact add_right_cancel hcmp

theorem cyclotomicPrimeCore_eq_GN_nat
    {p x u : ℕ} (hx : 0 < x) :
    cyclotomicPrimeCore p x u = GN p x u := by
  have hmul : x * cyclotomicPrimeCore p x u = x * GN p x u :=
    mul_cyclotomicPrimeCore_eq_mul_GN p x u
  exact Nat.eq_of_mul_eq_mul_left hx hmul

theorem dvd_cyclotomicPrimeCore_iff_dvd_GN_nat
    {p x u q : ℕ} (hx : 0 < x) :
    q ∣ cyclotomicPrimeCore p x u ↔ q ∣ GN p x u := by
  have hEq : cyclotomicPrimeCore p x u = GN p x u :=
    cyclotomicPrimeCore_eq_GN_nat (p := p) (x := x) (u := u) hx
  constructor <;> intro h
  · rw [← hEq]
    exact h
  · rw [hEq]
    exact h

lemma sub_eq_mul_cyclotomicPrimeCore_nat (p x u : ℕ) :
    (x + u) ^ p - u ^ p = x * cyclotomicPrimeCore p x u := by
  have hbig : (x + u) ^ p = x * cyclotomicPrimeCore p x u + u ^ p :=
    add_pow_eq_mul_cyclotomicPrimeCore_add_gap p x u
  have hpow : u ^ p ≤ (x + u) ^ p := by
    exact Nat.pow_le_pow_left (Nat.le_add_left u x) p
  omega

theorem prime_dvd_cyclotomicPrimeCore_of_dvd_sub_not_dvd_left
    {p x u q : ℕ}
    (hq : Nat.Prime q)
    (hq_dvd : q ∣ (x + u) ^ p - u ^ p)
    (hq_ndvd : ¬ q ∣ x) :
    q ∣ cyclotomicPrimeCore p x u := by
  have hmul : q ∣ x * cyclotomicPrimeCore p x u := by
    simpa [sub_eq_mul_cyclotomicPrimeCore_nat p x u] using hq_dvd
  exact (hq.dvd_mul.mp hmul).resolve_left hq_ndvd

end DkMath.CFBRC
