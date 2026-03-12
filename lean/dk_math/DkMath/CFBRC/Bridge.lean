/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CFBRC.Basic
import DkMath.CFBRC.CyclotomicProduct
import DkMath.NumberTheory.Gcd.GN

/-!
# CFBRC Bridge

`cyclotomicPrimeCore` と Zsigmondy / valuation 層（`DkMath.NumberTheory.Gcd.*`）
を接続する再利用 API。
-/

namespace DkMath.CFBRC

open DkMath.CosmicFormulaBinom

/-- `q ∤ x` のもとで、prime `q` に対する差の冪除法と core 除法は同値。 -/
theorem prime_dvd_sub_pow_iff_dvd_cyclotomicPrimeCore_nat
    {p x u q : ℕ}
    (hq : Nat.Prime q) (hq_not_dvd_x : ¬ q ∣ x) :
    q ∣ ((x + u) ^ p - u ^ p) ↔ q ∣ cyclotomicPrimeCore p x u := by
  constructor
  · intro hsub
    exact prime_dvd_cyclotomicPrimeCore_of_dvd_sub_not_dvd_left
      (p := p) (x := x) (u := u) (q := q) hq hsub hq_not_dvd_x
  · intro hcore
    have hmul : q ∣ x * cyclotomicPrimeCore p x u := dvd_mul_of_dvd_right hcore x
    simpa [sub_eq_mul_cyclotomicPrimeCore_nat p x u] using hmul

/--
deprecated alias:
`cyclotomicDivisorsProductShifted_eq_GN_of_ne_zero` を使うこと。
-/
@[deprecated cyclotomicDivisorsProductShifted_eq_GN_of_ne_zero
  (since := "2026-03-12")]
theorem cyclotomicDivisorsProductShifted_eq_GN_of_ne_zero_bridge
    {R : Type _} [Field R] {d : ℕ} (hd : 0 < d)
    {x u : R} (hx : x ≠ 0) (hu : u ≠ 0) :
    cyclotomicDivisorsProductShifted d x u = GN d x u :=
  cyclotomicDivisorsProductShifted_eq_GN_of_ne_zero (R := R) hd hx hu

/--
Zsigmondy primitive-prime existence bridge（prime exponent）:
`a := x + u, b := u` と置いた存在補題を CFBRC 記法で公開する。
-/
theorem exists_primitive_prime_factor_sub_pow_of_prime_exp_boundary
    {d x u : ℕ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hx : 0 < x) (hu : 0 < u) (hcop : Nat.Coprime (x + u) u)
    (hpnd : ¬ d ∣ x) :
    ∃ q : ℕ, Nat.Prime q ∧ q ∣ ((x + u) ^ d - u ^ d) ∧ ¬ q ∣ x ∧
      (∀ {k : ℕ}, 0 < k → k < d → ¬ q ∣ ((x + u) ^ k - u ^ k)) := by
  have hab_lt : u < x + u := by omega
  rcases DkMath.NumberTheory.GcdNext.exists_primitive_prime_factor_basic
      (a := x + u) (b := u) (d := d)
      hd_prime hd_ge hab_lt hu hcop (by simpa [Nat.add_sub_cancel] using hpnd) with
    ⟨q, hqP, hq_dvd_diff, hq_ndvd_gap⟩
  have hd1 : 1 < d := lt_of_lt_of_le (by decide : 1 < 3) hd_ge
  have hprim :
      ∀ {k : ℕ}, 0 < k → k < d → ¬ q ∣ ((x + u) ^ k - u ^ k) :=
    DkMath.NumberTheory.GcdNext.prime_exp_not_dvd_diff_imp_primitive
      (a := x + u) (b := u) (d := d) (q := q)
      hd_prime hd1 hqP hcop hab_lt hu hq_dvd_diff hq_ndvd_gap
  refine ⟨q, hqP, hq_dvd_diff, ?_, hprim⟩
  simpa [Nat.add_sub_cancel] using hq_ndvd_gap

/--
Zsigmondy existence を CFBRC core 除法へ直結する API（prime exponent）。
-/
theorem exists_primitive_prime_factor_dvd_cyclotomicPrimeCore_of_prime_exp_boundary
    {d x u : ℕ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hx : 0 < x) (hu : 0 < u) (hcop : Nat.Coprime (x + u) u)
    (hpnd : ¬ d ∣ x) :
    ∃ q : ℕ, Nat.Prime q ∧ q ∣ cyclotomicPrimeCore d x u ∧ ¬ q ∣ x ∧
      (∀ {k : ℕ}, 0 < k → k < d → ¬ q ∣ ((x + u) ^ k - u ^ k)) := by
  rcases exists_primitive_prime_factor_sub_pow_of_prime_exp_boundary
      (d := d) (x := x) (u := u) hd_prime hd_ge hx hu hcop hpnd with
    ⟨q, hqP, hq_dvd_diff, hq_ndvd_x, hprim⟩
  have hq_dvd_core : q ∣ cyclotomicPrimeCore d x u :=
    (prime_dvd_sub_pow_iff_dvd_cyclotomicPrimeCore_nat
      (p := d) (x := x) (u := u) (q := q) hqP hq_ndvd_x).1 hq_dvd_diff
  exact ⟨q, hqP, hq_dvd_core, hq_ndvd_x, hprim⟩

/--
`hcop : Nat.Coprime x u` 版 wrapper（差分形）。
-/
theorem exists_primitive_prime_factor_sub_pow_of_prime_exp_boundary_of_coprime
    {d x u : ℕ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hx : 0 < x) (hu : 0 < u) (hcop : Nat.Coprime x u)
    (hpnd : ¬ d ∣ x) :
    ∃ q : ℕ, Nat.Prime q ∧ q ∣ ((x + u) ^ d - u ^ d) ∧ ¬ q ∣ x ∧
      (∀ {k : ℕ}, 0 < k → k < d → ¬ q ∣ ((x + u) ^ k - u ^ k)) := by
  exact exists_primitive_prime_factor_sub_pow_of_prime_exp_boundary
    (d := d) (x := x) (u := u) hd_prime hd_ge hx hu
    ((Nat.coprime_add_self_left).2 hcop) hpnd

/--
`hcop : Nat.Coprime x u` 版 wrapper（core 除法形）。
-/
theorem exists_primitive_prime_factor_dvd_cyclotomicPrimeCore_of_prime_exp_boundary_of_coprime
    {d x u : ℕ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hx : 0 < x) (hu : 0 < u) (hcop : Nat.Coprime x u)
    (hpnd : ¬ d ∣ x) :
    ∃ q : ℕ, Nat.Prime q ∧ q ∣ cyclotomicPrimeCore d x u ∧ ¬ q ∣ x ∧
      (∀ {k : ℕ}, 0 < k → k < d → ¬ q ∣ ((x + u) ^ k - u ^ k)) := by
  exact exists_primitive_prime_factor_dvd_cyclotomicPrimeCore_of_prime_exp_boundary
    (d := d) (x := x) (u := u) hd_prime hd_ge hx hu
    ((Nat.coprime_add_self_left).2 hcop) hpnd

/--
valuation bridge（general `u` 版）:
`q ∤ x` のとき、`(x+u)^d - u^d` の `q`-進付値は `GN d x u` のそれに一致。
-/
theorem padicValNat_sub_pow_eq_padicValNat_GN_of_not_dvd_boundary
    {d x u q : ℕ}
    (hd2 : 2 ≤ d) (hx : 0 < x) (hu : 0 < u)
    (hqP : Nat.Prime q) (hq_not_dvd_x : ¬ q ∣ x) :
    padicValNat q ((x + u) ^ d - u ^ d) =
      padicValNat q (GN d x u) := by
  have hval_gap :=
    DkMath.NumberTheory.Gcd.padicValNat_sub_pow_eq_padicValNat_GN_of_not_dvd_gap
      (p := d) (z := x + u) (y := u) (q := q)
      hd2 (by omega) hu hqP
      (by simpa [Nat.add_sub_cancel_left] using hq_not_dvd_x)
  simpa [Nat.add_sub_cancel_left] using hval_gap

/--
valuation bridge:
`q ∤ x` のとき、`(x+u)^p - u^p` の `q`-進付値は `cyclotomicPrimeCore p x u` のそれに一致。
-/
theorem padicValNat_sub_pow_eq_padicValNat_cyclotomicPrimeCore_of_not_dvd_boundary
    {p x u q : ℕ}
    (hp2 : 2 ≤ p) (hx : 0 < x) (hu : 0 < u)
    (hqP : Nat.Prime q) (hq_not_dvd_x : ¬ q ∣ x) :
    padicValNat q ((x + u) ^ p - u ^ p) =
      padicValNat q (cyclotomicPrimeCore p x u) := by
  have hval_GN :
      padicValNat q ((x + u) ^ p - u ^ p) = padicValNat q (GN p x u) := by
    exact padicValNat_sub_pow_eq_padicValNat_GN_of_not_dvd_boundary
      (d := p) (x := x) (u := u) (q := q) hp2 hx hu hqP hq_not_dvd_x
  have hcore_eq_GN : cyclotomicPrimeCore p x u = GN p x u :=
    cyclotomicPrimeCore_eq_GN_nat (p := p) (x := x) (u := u) hx
  calc
    padicValNat q ((x + u) ^ p - u ^ p) = padicValNat q (GN p x u) := hval_GN
    _ = padicValNat q (cyclotomicPrimeCore p x u) := by
      rw [hcore_eq_GN]

end DkMath.CFBRC
