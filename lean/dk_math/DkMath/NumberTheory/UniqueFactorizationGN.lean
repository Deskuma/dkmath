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

@[simp] def boundaryRight (x _u : ℕ) : ℕ := x
@[simp] def boundaryLeft (_x u : ℕ) : ℕ := u
@[simp] def kernelRight (d x u : ℕ) : ℕ := GN d x u
@[simp] def kernelLeft (d x u : ℕ) : ℕ := GN d u x
@[simp] def boundaryProd (x u : ℕ) : ℕ := x * u

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

/--
`q ∤ d` の下で、`q` は `gcd(x, GN d x u)` を割らない（右境界）。

これは `v_q` 補題に進むための直接前段。
-/
theorem prime_not_dvd_gcd_left_GN_of_coprime_of_not_dvd_exp
    {d x u q : ℕ}
    (hd1 : 1 ≤ d) (hx : 0 < x) (hcop : Nat.Coprime x u)
    (hqP : Nat.Prime q) (hq_ndvd_d : ¬ q ∣ d) :
    ¬ q ∣ Nat.gcd x (GN d x u) := by
  intro hq_dvd_gcd
  by_cases hq_dvd_x : q ∣ x
  · have hq_not_dvd_GN :
      ¬ q ∣ GN d x u :=
      prime_dvd_left_not_dvd_GN_of_coprime_of_not_dvd_exp
        (d := d) (x := x) (u := u) hd1 hx hcop hqP hq_ndvd_d hq_dvd_x
    exact hq_not_dvd_GN (dvd_trans hq_dvd_gcd (Nat.gcd_dvd_right x (GN d x u)))
  · exact hq_dvd_x (dvd_trans hq_dvd_gcd (Nat.gcd_dvd_left x (GN d x u)))

/--
`q ∤ d` の下で、`v_q(gcd(x, GN d x u)) = 0`（右境界）。
-/
theorem padicValNat_gcd_left_GN_eq_zero_of_coprime_of_not_dvd_exp
    {d x u q : ℕ}
    (hd1 : 1 ≤ d) (hx : 0 < x) (hcop : Nat.Coprime x u)
    (hqP : Nat.Prime q) (hq_ndvd_d : ¬ q ∣ d) :
    padicValNat q (Nat.gcd x (GN d x u)) = 0 := by
  exact padicValNat.eq_zero_of_not_dvd
    (prime_not_dvd_gcd_left_GN_of_coprime_of_not_dvd_exp
      (d := d) (x := x) (u := u) (q := q) hd1 hx hcop hqP hq_ndvd_d)

/--
`q ∤ d` の下で、`v_q(gcd(u, GN d u x)) = 0`（左境界対称版）。
-/
theorem padicValNat_gcd_right_GN_swap_eq_zero_of_coprime_of_not_dvd_exp
    {d x u q : ℕ}
    (hd1 : 1 ≤ d) (hu : 0 < u) (hcop : Nat.Coprime x u)
    (hqP : Nat.Prime q) (hq_ndvd_d : ¬ q ∣ d) :
    padicValNat q (Nat.gcd u (GN d u x)) = 0 := by
  simpa using
    (padicValNat_gcd_left_GN_eq_zero_of_coprime_of_not_dvd_exp
      (d := d) (x := u) (u := x) (q := q) hd1 hu hcop.symm hqP hq_ndvd_d)

/--
prime-power 接続の最初の帰結（右境界）:
`k > 0` なら `q^k` も `gcd(x, GN d x u)` を割れない。
-/
theorem not_primePow_dvd_gcd_left_GN_of_coprime_of_not_dvd_exp
    {d x u q k : ℕ}
    (hd1 : 1 ≤ d) (hx : 0 < x) (hcop : Nat.Coprime x u)
    (hqP : Nat.Prime q) (hq_ndvd_d : ¬ q ∣ d) (hk : 0 < k) :
    ¬ q ^ k ∣ Nat.gcd x (GN d x u) := by
  intro hqk
  have hq_dvd_gcd : q ∣ Nat.gcd x (GN d x u) := by
    exact dvd_trans (dvd_pow_self q (Nat.pos_iff_ne_zero.mp hk)) hqk
  exact (prime_not_dvd_gcd_left_GN_of_coprime_of_not_dvd_exp
    (d := d) (x := x) (u := u) (q := q) hd1 hx hcop hqP hq_ndvd_d) hq_dvd_gcd

/--
`q ∤ d` かつ `Nat.Coprime x u` の右境界で、積 `x * GN d x u` の `q`-進付値は加法化できる。

`v_q(gcd(x,GN))=0` を確保した上で、prototype では `padicValNat.mul` を直接利用する。
-/
theorem padicValNat_mul_boundaryRight_kernelRight_eq_add
    {d x u q : ℕ}
    (hd2 : 2 ≤ d) (hx : 0 < x) (hu : 0 < u) (hcop : Nat.Coprime x u)
    (hqP : Nat.Prime q) (hq_ndvd_d : ¬ q ∣ d) :
    padicValNat q (x * GN d x u) =
      padicValNat q x + padicValNat q (GN d x u) := by
  have _ :
      padicValNat q (Nat.gcd x (GN d x u)) = 0 :=
    padicValNat_gcd_left_GN_eq_zero_of_coprime_of_not_dvd_exp
      (d := d) (x := x) (u := u) (q := q)
      (Nat.le_trans (by decide : 1 ≤ 2) hd2) hx hcop hqP hq_ndvd_d
  haveI : Fact q.Prime := ⟨hqP⟩
  have hx0 : x ≠ 0 := Nat.ne_of_gt hx
  have hGN0 : GN d x u ≠ 0 :=
    GN_ne_zero_nat_of_two_le (d := d) (x := x) (u := u) hd2 hx hu
  simpa using (padicValNat.mul (p := q) (a := x) (b := GN d x u) hx0 hGN0)

/--
三層圧縮の積 `x*u*GN d x u` 版の `q`-進付値加法（prototype）。
-/
theorem padicValNat_mul_boundaryProd_kernelRight_eq_add
    {d x u q : ℕ}
    (hd2 : 2 ≤ d) (hx : 0 < x) (hu : 0 < u)
    (hqP : Nat.Prime q) :
    padicValNat q (x * u * GN d x u) =
      padicValNat q x + padicValNat q u + padicValNat q (GN d x u) := by
  haveI : Fact q.Prime := ⟨hqP⟩
  have hx0 : x ≠ 0 := Nat.ne_of_gt hx
  have hu0 : u ≠ 0 := Nat.ne_of_gt hu
  have hxu0 : x * u ≠ 0 := Nat.mul_ne_zero hx0 hu0
  have hGN0 : GN d x u ≠ 0 :=
    GN_ne_zero_nat_of_two_le (d := d) (x := x) (u := u) hd2 hx hu
  calc
    padicValNat q (x * u * GN d x u)
        = padicValNat q (x * u) + padicValNat q (GN d x u) := by
            simpa [Nat.mul_assoc] using
              (padicValNat.mul (p := q) (a := x * u) (b := GN d x u) hxu0 hGN0)
    _ = (padicValNat q x + padicValNat q u) + padicValNat q (GN d x u) := by
          rw [padicValNat.mul (p := q) (a := x) (b := u) hx0 hu0]
    _ = padicValNat q x + padicValNat q u + padicValNat q (GN d x u) := by
          omega

/--
Wrapper:
right boundary divisibility implies right kernel non-divisibility
(nonexception prime).
-/
theorem prime_dvd_boundaryRight_not_dvd_kernelRight_of_coprime_of_not_dvd_exp
    {d x u q : ℕ}
    (hd1 : 1 ≤ d) (hx : 0 < x) (hcop : Nat.Coprime x u)
    (hqP : Nat.Prime q) (hq_ndvd_d : ¬ q ∣ d)
    (hq_dvd_boundary : q ∣ boundaryRight x u) :
    ¬ q ∣ kernelRight d x u := by
  simpa [boundaryRight, kernelRight] using
    (prime_dvd_left_not_dvd_GN_of_coprime_of_not_dvd_exp
      (d := d) (x := x) (u := u) hd1 hx hcop hqP hq_ndvd_d hq_dvd_boundary)

/--
Wrapper:
left boundary divisibility implies left kernel non-divisibility
(nonexception prime).
-/
theorem prime_dvd_boundaryLeft_not_dvd_kernelLeft_of_coprime_of_not_dvd_exp
    {d x u q : ℕ}
    (hd1 : 1 ≤ d) (hu : 0 < u) (hcop : Nat.Coprime x u)
    (hqP : Nat.Prime q) (hq_ndvd_d : ¬ q ∣ d)
    (hq_dvd_boundary : q ∣ boundaryLeft x u) :
    ¬ q ∣ kernelLeft d x u := by
  simpa [boundaryLeft, kernelLeft] using
    (prime_dvd_right_not_dvd_GN_swap_of_coprime_of_not_dvd_exp
      (d := d) (x := x) (u := u) hd1 hu hcop hqP hq_ndvd_d hq_dvd_boundary)

end DkMath.NumberTheory
