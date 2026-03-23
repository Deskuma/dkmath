/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Basic.Nat
import DkMath.NumberTheory.Gcd.GN
import DkMath.FLT.Core
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
例外素数レイヤ（`q ∣ d`）に限定した prime-power 比較 API。
-/
abbrev PrimePowComparisonExceptionalLayer (d m n : ℕ) : Prop :=
  ∀ q k : ℕ, Nat.Prime q → q ∣ d → (q ^ k ∣ m ↔ q ^ k ∣ n)

/--
非例外素数レイヤ（`q ∤ d`）に限定した prime-power 比較 API。
-/
abbrev PrimePowComparisonNonExceptionalLayer (d m n : ℕ) : Prop :=
  ∀ q k : ℕ, Nat.Prime q → ¬ q ∣ d → (q ^ k ∣ m ↔ q ^ k ∣ n)

/--
例外/非例外の 2 層比較 API から、factorization 一致へ接続する橋。
-/
theorem factorization_eq_of_prime_pow_dvd_iff_split_layers
    {d m n : ℕ}
    (hm : m ≠ 0) (hn : n ≠ 0)
    (hExc : PrimePowComparisonExceptionalLayer d m n)
    (hNonExc : PrimePowComparisonNonExceptionalLayer d m n) :
    m.factorization = n.factorization := by
  apply factorization_eq_of_prime_pow_dvd_iff hm hn
  intro q k hqP
  by_cases hq_dvd_d : q ∣ d
  · exact hExc q k hqP hq_dvd_d
  · exact hNonExc q k hqP hq_dvd_d

/--
例外/非例外の 2 層比較 API から、自然数本体の一致へ接続する最終形。
-/
theorem unique_factorization_nat_via_split_prime_layers
    {d m n : ℕ}
    (hm : m ≠ 0) (hn : n ≠ 0)
    (hExc : PrimePowComparisonExceptionalLayer d m n)
    (hNonExc : PrimePowComparisonNonExceptionalLayer d m n) :
    m = n := by
  apply unique_factorization_nat_via_prime_powers hm hn
  intro q k hqP
  by_cases hq_dvd_d : q ∣ d
  · exact hExc q k hqP hq_dvd_d
  · exact hNonExc q k hqP hq_dvd_d

/--
例外素数層の具体補題（right boundary -> right kernel）:
`q ∣ d` かつ `q ∣ boundaryRight x u` なら `q ∣ kernelRight d x u`。
-/
theorem prime_dvd_boundaryRight_dvd_kernelRight_of_dvd_exp
    {d x u q : ℕ}
    (hd1 : 1 ≤ d) (hqP : Nat.Prime q) (hq_dvd_d : q ∣ d)
    (hq_dvd_boundary : q ∣ boundaryRight x u) :
    q ∣ kernelRight d x u := by
  have hhead :
      GN (R := ZMod q) d (x : ZMod q) (u : ZMod q) =
        (Nat.choose d 1 : ZMod q) * (u : ZMod q) ^ (d - 1) := by
    simpa [boundaryRight] using
      (DkMath.GN_zmod_eq_head_of_dvd
        (p := q) (d := d) (x := x) (u := u) hqP hd1 hq_dvd_boundary)
  have hd0 : (d : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff d q).2 hq_dvd_d
  have hGN0 : (GN d x u : ZMod q) = 0 := by
    calc
      (GN d x u : ZMod q)
          = (Nat.choose d 1 : ZMod q) * (u : ZMod q) ^ (d - 1) := by
              simpa using hhead
      _ = (d : ZMod q) * (u : ZMod q) ^ (d - 1) := by simp
      _ = 0 := by simp [hd0]
  exact (ZMod.natCast_eq_zero_iff (kernelRight d x u) q).1 (by simpa [kernelRight] using hGN0)

/--
例外素数層の具体補題（boundaryProd 版）:
`q ∣ d`、`q ∣ boundaryProd x u`、`q ∤ boundaryLeft x u` なら `q ∣ kernelRight d x u`。
-/
theorem prime_dvd_boundaryProd_dvd_kernelRight_of_dvd_exp_of_not_dvd_boundaryLeft
    {d x u q : ℕ}
    (hd1 : 1 ≤ d) (hqP : Nat.Prime q) (hq_dvd_d : q ∣ d)
    (hq_dvd_boundaryProd : q ∣ boundaryProd x u)
    (hq_not_dvd_boundaryLeft : ¬ q ∣ boundaryLeft x u) :
    q ∣ kernelRight d x u := by
  have hq_dvd_x : q ∣ x := by
    have hq_dvd_x_or_u : q ∣ x ∨ q ∣ u := by
      have hq_dvd_mul : q ∣ x * u := by simpa [boundaryProd] using hq_dvd_boundaryProd
      exact hqP.dvd_mul.mp hq_dvd_mul
    rcases hq_dvd_x_or_u with hq_dvd_x | hq_dvd_u
    · exact hq_dvd_x
    · exact False.elim (hq_not_dvd_boundaryLeft (by simpa [boundaryLeft] using hq_dvd_u))
  exact
    prime_dvd_boundaryRight_dvd_kernelRight_of_dvd_exp
      (d := d) (x := x) (u := u) (q := q)
      hd1 hqP hq_dvd_d (by simpa [boundaryRight] using hq_dvd_x)

/--
例外素数層の `boundaryProd ↔ kernelRight` 比較を valuation 等式から自動供給する。
-/
theorem exceptionalBK_of_padicValNat_eq_boundaryProd_kernelRight
    {d x u : ℕ}
    (hd2 : 2 ≤ d) (hx : 0 < x) (hu : 0 < u)
    (hExcVal : ∀ q : ℕ, Nat.Prime q → q ∣ d →
      padicValNat q (boundaryProd x u) = padicValNat q (kernelRight d x u)) :
    ∀ q k : ℕ, Nat.Prime q → q ∣ d →
      (q ^ k ∣ boundaryProd x u ↔ q ^ k ∣ kernelRight d x u) := by
  intro q k hqP hq_dvd_d
  haveI : Fact q.Prime := ⟨hqP⟩
  have hB0 : boundaryProd x u ≠ 0 := Nat.mul_ne_zero (Nat.ne_of_gt hx) (Nat.ne_of_gt hu)
  have hK0 : kernelRight d x u ≠ 0 := by
    simpa [kernelRight] using
      (GN_ne_zero_nat_of_two_le (d := d) (x := x) (u := u) hd2 hx hu)
  have hval : padicValNat q (x * u) = padicValNat q (GN d x u) := by
    simpa [boundaryProd, kernelRight] using hExcVal q hqP hq_dvd_d
  calc
    q ^ k ∣ boundaryProd x u ↔ k ≤ padicValNat q (boundaryProd x u) :=
      (padicValNat_dvd_iff_le (p := q) (a := boundaryProd x u) (n := k) hB0)
    _ ↔ k ≤ padicValNat q (kernelRight d x u) := by
      simp [boundaryProd, kernelRight, hval]
    _ ↔ q ^ k ∣ kernelRight d x u :=
      (padicValNat_dvd_iff_le (p := q) (a := kernelRight d x u) (n := k) hK0).symm

/--
非例外素数層の `boundaryProd ↔ kernelRight` 比較を valuation 等式から自動供給する。
-/
theorem nonExceptionalBK_of_padicValNat_eq_boundaryProd_kernelRight
    {d x u : ℕ}
    (hd2 : 2 ≤ d) (hx : 0 < x) (hu : 0 < u)
    (hNonExcVal : ∀ q : ℕ, Nat.Prime q → ¬ q ∣ d →
      padicValNat q (boundaryProd x u) = padicValNat q (kernelRight d x u)) :
    ∀ q k : ℕ, Nat.Prime q → ¬ q ∣ d →
      (q ^ k ∣ boundaryProd x u ↔ q ^ k ∣ kernelRight d x u) := by
  intro q k hqP hq_ndvd_d
  haveI : Fact q.Prime := ⟨hqP⟩
  have hB0 : boundaryProd x u ≠ 0 := Nat.mul_ne_zero (Nat.ne_of_gt hx) (Nat.ne_of_gt hu)
  have hK0 : kernelRight d x u ≠ 0 := by
    simpa [kernelRight] using
      (GN_ne_zero_nat_of_two_le (d := d) (x := x) (u := u) hd2 hx hu)
  have hval : padicValNat q (x * u) = padicValNat q (GN d x u) := by
    simpa [boundaryProd, kernelRight] using hNonExcVal q hqP hq_ndvd_d
  calc
    q ^ k ∣ boundaryProd x u ↔ k ≤ padicValNat q (boundaryProd x u) :=
      (padicValNat_dvd_iff_le (p := q) (a := boundaryProd x u) (n := k) hB0)
    _ ↔ k ≤ padicValNat q (kernelRight d x u) := by
      simp [boundaryProd, kernelRight, hval]
    _ ↔ q ^ k ∣ kernelRight d x u :=
      (padicValNat_dvd_iff_le (p := q) (a := kernelRight d x u) (n := k) hK0).symm

/--
例外素数層の `boundaryProd -> kernelRight` 比較を valuation 不等式（`≤`）から供給する。
-/
theorem exceptionalBK_fwd_of_padicValNat_le_boundaryProd_kernelRight
    {d x u : ℕ}
    (hd2 : 2 ≤ d) (hx : 0 < x) (hu : 0 < u)
    (hExcLe : ∀ q : ℕ, Nat.Prime q → q ∣ d →
      padicValNat q (boundaryProd x u) ≤ padicValNat q (kernelRight d x u)) :
    ∀ q k : ℕ, Nat.Prime q → q ∣ d →
      (q ^ k ∣ boundaryProd x u → q ^ k ∣ kernelRight d x u) := by
  intro q k hqP hq_dvd_d hqk_dvd_boundary
  haveI : Fact q.Prime := ⟨hqP⟩
  have hB0 : boundaryProd x u ≠ 0 := Nat.mul_ne_zero (Nat.ne_of_gt hx) (Nat.ne_of_gt hu)
  have hK0 : kernelRight d x u ≠ 0 := by
    simpa [kernelRight] using
      (GN_ne_zero_nat_of_two_le (d := d) (x := x) (u := u) hd2 hx hu)
  have hk_le_boundary : k ≤ padicValNat q (boundaryProd x u) :=
    (padicValNat_dvd_iff_le (p := q) (a := boundaryProd x u) (n := k) hB0).1 hqk_dvd_boundary
  have hk_le_kernel : k ≤ padicValNat q (kernelRight d x u) :=
    le_trans hk_le_boundary (hExcLe q hqP hq_dvd_d)
  exact (padicValNat_dvd_iff_le (p := q) (a := kernelRight d x u) (n := k) hK0).2 hk_le_kernel

/--
例外素数層の `kernelRight -> boundaryProd` 比較を valuation 不等式（`≤`）から供給する。
-/
theorem exceptionalBK_rev_of_padicValNat_le_kernelRight_boundaryProd
    {d x u : ℕ}
    (hd2 : 2 ≤ d) (hx : 0 < x) (hu : 0 < u)
    (hExcLeRev : ∀ q : ℕ, Nat.Prime q → q ∣ d →
      padicValNat q (kernelRight d x u) ≤ padicValNat q (boundaryProd x u)) :
    ∀ q k : ℕ, Nat.Prime q → q ∣ d →
      (q ^ k ∣ kernelRight d x u → q ^ k ∣ boundaryProd x u) := by
  intro q k hqP hq_dvd_d hqk_dvd_kernel
  haveI : Fact q.Prime := ⟨hqP⟩
  have hB0 : boundaryProd x u ≠ 0 := Nat.mul_ne_zero (Nat.ne_of_gt hx) (Nat.ne_of_gt hu)
  have hK0 : kernelRight d x u ≠ 0 := by
    simpa [kernelRight] using
      (GN_ne_zero_nat_of_two_le (d := d) (x := x) (u := u) hd2 hx hu)
  have hk_le_kernel : k ≤ padicValNat q (kernelRight d x u) :=
    (padicValNat_dvd_iff_le (p := q) (a := kernelRight d x u) (n := k) hK0).1 hqk_dvd_kernel
  have hk_le_boundary : k ≤ padicValNat q (boundaryProd x u) :=
    le_trans hk_le_kernel (hExcLeRev q hqP hq_dvd_d)
  exact (padicValNat_dvd_iff_le (p := q) (a := boundaryProd x u) (n := k) hB0).2 hk_le_boundary

/--
例外素数層の `boundaryProd ↔ kernelRight` 比較を valuation 不等式の両向きから供給する。
-/
theorem exceptionalBK_of_padicValNat_le_le_boundaryProd_kernelRight
    {d x u : ℕ}
    (hd2 : 2 ≤ d) (hx : 0 < x) (hu : 0 < u)
    (hExcLe : ∀ q : ℕ, Nat.Prime q → q ∣ d →
      padicValNat q (boundaryProd x u) ≤ padicValNat q (kernelRight d x u))
    (hExcLeRev : ∀ q : ℕ, Nat.Prime q → q ∣ d →
      padicValNat q (kernelRight d x u) ≤ padicValNat q (boundaryProd x u)) :
    ∀ q k : ℕ, Nat.Prime q → q ∣ d →
      (q ^ k ∣ boundaryProd x u ↔ q ^ k ∣ kernelRight d x u) := by
  intro q k hqP hq_dvd_d
  constructor
  · intro hqk_dvd_boundary
    exact exceptionalBK_fwd_of_padicValNat_le_boundaryProd_kernelRight
      (d := d) (x := x) (u := u) hd2 hx hu hExcLe q k hqP hq_dvd_d hqk_dvd_boundary
  · intro hqk_dvd_kernel
    exact exceptionalBK_rev_of_padicValNat_le_kernelRight_boundaryProd
      (d := d) (x := x) (u := u) hd2 hx hu hExcLeRev q k hqP hq_dvd_d hqk_dvd_kernel

/--
非例外素数層の `boundaryProd ↔ kernelRight` 比較を両側 0 化から供給する。
-/
theorem nonExceptionalBK_of_padicValNat_eq_zero_boundaryProd_kernelRight
    {d x u : ℕ}
    (hd2 : 2 ≤ d) (hx : 0 < x) (hu : 0 < u)
    (hNonExcZero :
      ∀ q : ℕ, Nat.Prime q → ¬ q ∣ d →
        padicValNat q (boundaryProd x u) = 0 ∧
        padicValNat q (kernelRight d x u) = 0) :
    ∀ q k : ℕ, Nat.Prime q → ¬ q ∣ d →
      (q ^ k ∣ boundaryProd x u ↔ q ^ k ∣ kernelRight d x u) := by
  intro q k hqP hq_ndvd_d
  haveI : Fact q.Prime := ⟨hqP⟩
  have hB0 : boundaryProd x u ≠ 0 := Nat.mul_ne_zero (Nat.ne_of_gt hx) (Nat.ne_of_gt hu)
  have hK0 : kernelRight d x u ≠ 0 := by
    simpa [kernelRight] using
      (GN_ne_zero_nat_of_two_le (d := d) (x := x) (u := u) hd2 hx hu)
  rcases hNonExcZero q hqP hq_ndvd_d with ⟨hBz, hKz⟩
  calc
    q ^ k ∣ boundaryProd x u ↔ k ≤ padicValNat q (boundaryProd x u) :=
      (padicValNat_dvd_iff_le (p := q) (a := boundaryProd x u) (n := k) hB0)
    _ ↔ k ≤ padicValNat q (kernelRight d x u) := by
      rw [hBz, hKz]
    _ ↔ q ^ k ∣ kernelRight d x u :=
      (padicValNat_dvd_iff_le (p := q) (a := kernelRight d x u) (n := k) hK0).symm

/--
`boundaryProd/kernelRight` の具体比較補題群から、例外層 `hExc` を構成する。
-/
theorem exceptionalLayer_of_boundaryProd_kernelRight
    {d x u m n : ℕ}
    (hExcM : ∀ q k : ℕ, Nat.Prime q → q ∣ d →
      (q ^ k ∣ m ↔ q ^ k ∣ boundaryProd x u))
    (hExcK : ∀ q k : ℕ, Nat.Prime q → q ∣ d →
      (q ^ k ∣ n ↔ q ^ k ∣ kernelRight d x u))
    (hExcBK : ∀ q k : ℕ, Nat.Prime q → q ∣ d →
      (q ^ k ∣ boundaryProd x u ↔ q ^ k ∣ kernelRight d x u)) :
    PrimePowComparisonExceptionalLayer d m n := by
  intro q k hqP hq_dvd_d
  exact (hExcM q k hqP hq_dvd_d).trans
    ((hExcBK q k hqP hq_dvd_d).trans (hExcK q k hqP hq_dvd_d).symm)

/--
`boundaryProd/kernelRight` の具体比較補題群から、非例外層 `hNonExc` を構成する。
-/
theorem nonExceptionalLayer_of_boundaryProd_kernelRight
    {d x u m n : ℕ}
    (hNonExcM : ∀ q k : ℕ, Nat.Prime q → ¬ q ∣ d →
      (q ^ k ∣ m ↔ q ^ k ∣ boundaryProd x u))
    (hNonExcK : ∀ q k : ℕ, Nat.Prime q → ¬ q ∣ d →
      (q ^ k ∣ n ↔ q ^ k ∣ kernelRight d x u))
    (hNonExcBK : ∀ q k : ℕ, Nat.Prime q → ¬ q ∣ d →
      (q ^ k ∣ boundaryProd x u ↔ q ^ k ∣ kernelRight d x u)) :
    PrimePowComparisonNonExceptionalLayer d m n := by
  intro q k hqP hq_ndvd_d
  exact (hNonExcM q k hqP hq_ndvd_d).trans
    ((hNonExcBK q k hqP hq_ndvd_d).trans (hNonExcK q k hqP hq_ndvd_d).symm)

/--
`hExcBK` を valuation 等式から自動供給する縮約版（例外層）。
-/
theorem exceptionalLayer_of_boundaryProd_kernelRight_autoBK
    {d x u m n : ℕ}
    (hd2 : 2 ≤ d) (hx : 0 < x) (hu : 0 < u)
    (hExcM : ∀ q k : ℕ, Nat.Prime q → q ∣ d →
      (q ^ k ∣ m ↔ q ^ k ∣ boundaryProd x u))
    (hExcK : ∀ q k : ℕ, Nat.Prime q → q ∣ d →
      (q ^ k ∣ n ↔ q ^ k ∣ kernelRight d x u))
    (hExcVal : ∀ q : ℕ, Nat.Prime q → q ∣ d →
      padicValNat q (boundaryProd x u) = padicValNat q (kernelRight d x u)) :
    PrimePowComparisonExceptionalLayer d m n := by
  have hExcBK :
      ∀ q k : ℕ, Nat.Prime q → q ∣ d →
        (q ^ k ∣ boundaryProd x u ↔ q ^ k ∣ kernelRight d x u) :=
    exceptionalBK_of_padicValNat_eq_boundaryProd_kernelRight
      (d := d) (x := x) (u := u) hd2 hx hu hExcVal
  exact exceptionalLayer_of_boundaryProd_kernelRight
    (d := d) (x := x) (u := u) (m := m) (n := n) hExcM hExcK hExcBK

/--
`hNonExcBK` を valuation 等式から自動供給する縮約版（非例外層）。
-/
theorem nonExceptionalLayer_of_boundaryProd_kernelRight_autoBK
    {d x u m n : ℕ}
    (hd2 : 2 ≤ d) (hx : 0 < x) (hu : 0 < u)
    (hNonExcM : ∀ q k : ℕ, Nat.Prime q → ¬ q ∣ d →
      (q ^ k ∣ m ↔ q ^ k ∣ boundaryProd x u))
    (hNonExcK : ∀ q k : ℕ, Nat.Prime q → ¬ q ∣ d →
      (q ^ k ∣ n ↔ q ^ k ∣ kernelRight d x u))
    (hNonExcVal : ∀ q : ℕ, Nat.Prime q → ¬ q ∣ d →
      padicValNat q (boundaryProd x u) = padicValNat q (kernelRight d x u)) :
    PrimePowComparisonNonExceptionalLayer d m n := by
  have hNonExcBK :
      ∀ q k : ℕ, Nat.Prime q → ¬ q ∣ d →
        (q ^ k ∣ boundaryProd x u ↔ q ^ k ∣ kernelRight d x u) :=
    nonExceptionalBK_of_padicValNat_eq_boundaryProd_kernelRight
      (d := d) (x := x) (u := u) hd2 hx hu hNonExcVal
  exact nonExceptionalLayer_of_boundaryProd_kernelRight
    (d := d) (x := x) (u := u) (m := m) (n := n) hNonExcM hNonExcK hNonExcBK

/--
`hExcBK` を valuation 不等式（両向き `≤`）から自動供給する縮約版（例外層）。
-/
theorem exceptionalLayer_of_boundaryProd_kernelRight_autoBK_le
    {d x u m n : ℕ}
    (hd2 : 2 ≤ d) (hx : 0 < x) (hu : 0 < u)
    (hExcM : ∀ q k : ℕ, Nat.Prime q → q ∣ d →
      (q ^ k ∣ m ↔ q ^ k ∣ boundaryProd x u))
    (hExcK : ∀ q k : ℕ, Nat.Prime q → q ∣ d →
      (q ^ k ∣ n ↔ q ^ k ∣ kernelRight d x u))
    (hExcLe : ∀ q : ℕ, Nat.Prime q → q ∣ d →
      padicValNat q (boundaryProd x u) ≤ padicValNat q (kernelRight d x u))
    (hExcLeRev : ∀ q : ℕ, Nat.Prime q → q ∣ d →
      padicValNat q (kernelRight d x u) ≤ padicValNat q (boundaryProd x u)) :
    PrimePowComparisonExceptionalLayer d m n := by
  have hExcBK :
      ∀ q k : ℕ, Nat.Prime q → q ∣ d →
        (q ^ k ∣ boundaryProd x u ↔ q ^ k ∣ kernelRight d x u) :=
    exceptionalBK_of_padicValNat_le_le_boundaryProd_kernelRight
      (d := d) (x := x) (u := u) hd2 hx hu hExcLe hExcLeRev
  exact exceptionalLayer_of_boundaryProd_kernelRight
    (d := d) (x := x) (u := u) (m := m) (n := n) hExcM hExcK hExcBK

/--
`hNonExcBK` を両側 0 化から自動供給する縮約版（非例外層）。
-/
theorem nonExceptionalLayer_of_boundaryProd_kernelRight_autoBK_zero
    {d x u m n : ℕ}
    (hd2 : 2 ≤ d) (hx : 0 < x) (hu : 0 < u)
    (hNonExcM : ∀ q k : ℕ, Nat.Prime q → ¬ q ∣ d →
      (q ^ k ∣ m ↔ q ^ k ∣ boundaryProd x u))
    (hNonExcK : ∀ q k : ℕ, Nat.Prime q → ¬ q ∣ d →
      (q ^ k ∣ n ↔ q ^ k ∣ kernelRight d x u))
    (hNonExcZero :
      ∀ q : ℕ, Nat.Prime q → ¬ q ∣ d →
        padicValNat q (boundaryProd x u) = 0 ∧
        padicValNat q (kernelRight d x u) = 0) :
    PrimePowComparisonNonExceptionalLayer d m n := by
  have hNonExcBK :
      ∀ q k : ℕ, Nat.Prime q → ¬ q ∣ d →
        (q ^ k ∣ boundaryProd x u ↔ q ^ k ∣ kernelRight d x u) :=
    nonExceptionalBK_of_padicValNat_eq_zero_boundaryProd_kernelRight
      (d := d) (x := x) (u := u) hd2 hx hu hNonExcZero
  exact nonExceptionalLayer_of_boundaryProd_kernelRight
    (d := d) (x := x) (u := u) (m := m) (n := n) hNonExcM hNonExcK hNonExcBK

/--
実データ向け end-to-end 比較定理:
`boundaryProd/kernelRight` 由来の層別比較補題群を束ねて `m = n` を得る。
-/
theorem unique_factorization_nat_via_boundaryProd_kernelRight_split_layers_e2e
    {d x u m n : ℕ}
    (hm : m ≠ 0) (hn : n ≠ 0)
    (hExcM : ∀ q k : ℕ, Nat.Prime q → q ∣ d →
      (q ^ k ∣ m ↔ q ^ k ∣ boundaryProd x u))
    (hExcK : ∀ q k : ℕ, Nat.Prime q → q ∣ d →
      (q ^ k ∣ n ↔ q ^ k ∣ kernelRight d x u))
    (hExcBK : ∀ q k : ℕ, Nat.Prime q → q ∣ d →
      (q ^ k ∣ boundaryProd x u ↔ q ^ k ∣ kernelRight d x u))
    (hNonExcM : ∀ q k : ℕ, Nat.Prime q → ¬ q ∣ d →
      (q ^ k ∣ m ↔ q ^ k ∣ boundaryProd x u))
    (hNonExcK : ∀ q k : ℕ, Nat.Prime q → ¬ q ∣ d →
      (q ^ k ∣ n ↔ q ^ k ∣ kernelRight d x u))
    (hNonExcBK : ∀ q k : ℕ, Nat.Prime q → ¬ q ∣ d →
      (q ^ k ∣ boundaryProd x u ↔ q ^ k ∣ kernelRight d x u)) :
    m = n := by
  have hExc : PrimePowComparisonExceptionalLayer d m n :=
    exceptionalLayer_of_boundaryProd_kernelRight
      (d := d) (x := x) (u := u) (m := m) (n := n)
      hExcM hExcK hExcBK
  have hNonExc : PrimePowComparisonNonExceptionalLayer d m n :=
    nonExceptionalLayer_of_boundaryProd_kernelRight
      (d := d) (x := x) (u := u) (m := m) (n := n)
      hNonExcM hNonExcK hNonExcBK
  exact unique_factorization_nat_via_split_prime_layers
    (d := d) (m := m) (n := n) hm hn hExc hNonExc

/--
実データ向け end-to-end 比較定理（`hExcBK` / `hNonExcBK` 自動供給版）。

`boundaryProd ↔ kernelRight` の prime-power 比較を valuation 等式で与えるだけで、
層別 API を経由して `m = n` を得る。
-/
theorem unique_factorization_nat_via_boundaryProd_kernelRight_split_layers_e2e_autoBK
    {d x u m n : ℕ}
    (hm : m ≠ 0) (hn : n ≠ 0)
    (hd2 : 2 ≤ d) (hx : 0 < x) (hu : 0 < u)
    (hExcM : ∀ q k : ℕ, Nat.Prime q → q ∣ d →
      (q ^ k ∣ m ↔ q ^ k ∣ boundaryProd x u))
    (hExcK : ∀ q k : ℕ, Nat.Prime q → q ∣ d →
      (q ^ k ∣ n ↔ q ^ k ∣ kernelRight d x u))
    (hExcVal : ∀ q : ℕ, Nat.Prime q → q ∣ d →
      padicValNat q (boundaryProd x u) = padicValNat q (kernelRight d x u))
    (hNonExcM : ∀ q k : ℕ, Nat.Prime q → ¬ q ∣ d →
      (q ^ k ∣ m ↔ q ^ k ∣ boundaryProd x u))
    (hNonExcK : ∀ q k : ℕ, Nat.Prime q → ¬ q ∣ d →
      (q ^ k ∣ n ↔ q ^ k ∣ kernelRight d x u))
    (hNonExcVal : ∀ q : ℕ, Nat.Prime q → ¬ q ∣ d →
      padicValNat q (boundaryProd x u) = padicValNat q (kernelRight d x u)) :
    m = n := by
  have hExc : PrimePowComparisonExceptionalLayer d m n :=
    exceptionalLayer_of_boundaryProd_kernelRight_autoBK
      (d := d) (x := x) (u := u) (m := m) (n := n)
      hd2 hx hu hExcM hExcK hExcVal
  have hNonExc : PrimePowComparisonNonExceptionalLayer d m n :=
    nonExceptionalLayer_of_boundaryProd_kernelRight_autoBK
      (d := d) (x := x) (u := u) (m := m) (n := n)
      hd2 hx hu hNonExcM hNonExcK hNonExcVal
  exact unique_factorization_nat_via_split_prime_layers
    (d := d) (m := m) (n := n) hm hn hExc hNonExc

/--
実データ向け end-to-end 比較定理（`≤` / 0 化ベース縮約版）。

- 例外層 `hExcBK` は valuation 不等式（両向き `≤`）から自動供給
- 非例外層 `hNonExcBK` は両側 0 化から自動供給
-/
theorem unique_factorization_nat_via_boundaryProd_kernelRight_split_layers_e2e_autoBK_le_zero
    {d x u m n : ℕ}
    (hm : m ≠ 0) (hn : n ≠ 0)
    (hd2 : 2 ≤ d) (hx : 0 < x) (hu : 0 < u)
    (hExcM : ∀ q k : ℕ, Nat.Prime q → q ∣ d →
      (q ^ k ∣ m ↔ q ^ k ∣ boundaryProd x u))
    (hExcK : ∀ q k : ℕ, Nat.Prime q → q ∣ d →
      (q ^ k ∣ n ↔ q ^ k ∣ kernelRight d x u))
    (hExcLe : ∀ q : ℕ, Nat.Prime q → q ∣ d →
      padicValNat q (boundaryProd x u) ≤ padicValNat q (kernelRight d x u))
    (hExcLeRev : ∀ q : ℕ, Nat.Prime q → q ∣ d →
      padicValNat q (kernelRight d x u) ≤ padicValNat q (boundaryProd x u))
    (hNonExcM : ∀ q k : ℕ, Nat.Prime q → ¬ q ∣ d →
      (q ^ k ∣ m ↔ q ^ k ∣ boundaryProd x u))
    (hNonExcK : ∀ q k : ℕ, Nat.Prime q → ¬ q ∣ d →
      (q ^ k ∣ n ↔ q ^ k ∣ kernelRight d x u))
    (hNonExcZero :
      ∀ q : ℕ, Nat.Prime q → ¬ q ∣ d →
        padicValNat q (boundaryProd x u) = 0 ∧
        padicValNat q (kernelRight d x u) = 0) :
    m = n := by
  have hExc : PrimePowComparisonExceptionalLayer d m n :=
    exceptionalLayer_of_boundaryProd_kernelRight_autoBK_le
      (d := d) (x := x) (u := u) (m := m) (n := n)
      hd2 hx hu hExcM hExcK hExcLe hExcLeRev
  have hNonExc : PrimePowComparisonNonExceptionalLayer d m n :=
    nonExceptionalLayer_of_boundaryProd_kernelRight_autoBK_zero
      (d := d) (x := x) (u := u) (m := m) (n := n)
      hd2 hx hu hNonExcM hNonExcK hNonExcZero
  exact unique_factorization_nat_via_split_prime_layers
    (d := d) (m := m) (n := n) hm hn hExc hNonExc

/--
例外層の valuation 等式から、`hExcLe`（`boundaryProd ≤ kernelRight`）を自動導出する。
-/
theorem exceptionalLe_of_padicValNat_eq_boundaryProd_kernelRight
    {d x u : ℕ}
    (hExcVal : ∀ q : ℕ, Nat.Prime q → q ∣ d →
      padicValNat q (boundaryProd x u) = padicValNat q (kernelRight d x u)) :
    ∀ q : ℕ, Nat.Prime q → q ∣ d →
      padicValNat q (boundaryProd x u) ≤ padicValNat q (kernelRight d x u) := by
  intro q hqP hq_dvd_d
  exact le_of_eq (hExcVal q hqP hq_dvd_d)

/--
例外層の valuation 等式から、`hExcLeRev`（`kernelRight ≤ boundaryProd`）を自動導出する。
-/
theorem exceptionalLeRev_of_padicValNat_eq_boundaryProd_kernelRight
    {d x u : ℕ}
    (hExcVal : ∀ q : ℕ, Nat.Prime q → q ∣ d →
      padicValNat q (boundaryProd x u) = padicValNat q (kernelRight d x u)) :
    ∀ q : ℕ, Nat.Prime q → q ∣ d →
      padicValNat q (kernelRight d x u) ≤ padicValNat q (boundaryProd x u) := by
  intro q hqP hq_dvd_d
  exact le_of_eq (hExcVal q hqP hq_dvd_d).symm

/--
`boundaryRight`/`boundaryLeft` の非除法情報から、`boundaryProd` の非除法を作る（非例外層）。
-/
theorem nonExceptionalNotDvd_boundaryProd_of_not_dvd_boundarySides
    {d x u : ℕ}
    (hNonExcNotDvdRight : ∀ q : ℕ, Nat.Prime q → ¬ q ∣ d → ¬ q ∣ boundaryRight x u)
    (hNonExcNotDvdLeft : ∀ q : ℕ, Nat.Prime q → ¬ q ∣ d → ¬ q ∣ boundaryLeft x u) :
    ∀ q : ℕ, Nat.Prime q → ¬ q ∣ d → ¬ q ∣ boundaryProd x u := by
  intro q hqP hq_ndvd_d hq_dvd_boundaryProd
  have hq_dvd_mul : q ∣ x * u := by
    simpa [boundaryProd] using hq_dvd_boundaryProd
  rcases hqP.dvd_mul.mp hq_dvd_mul with hq_dvd_x | hq_dvd_u
  · exact hNonExcNotDvdRight q hqP hq_ndvd_d (by simpa [boundaryRight] using hq_dvd_x)
  · exact hNonExcNotDvdLeft q hqP hq_ndvd_d (by simpa [boundaryLeft] using hq_dvd_u)

/--
非例外層 boundary 入口の facade:
`boundaryProd` 直入力、または `boundaryRight/Left` 入力のどちらかを受ける。
-/
def NonExceptionalBoundaryEntrance (d x u : ℕ) : Prop :=
  (∀ q : ℕ, Nat.Prime q → ¬ q ∣ d → ¬ q ∣ boundaryProd x u) ∨
  ((∀ q : ℕ, Nat.Prime q → ¬ q ∣ d → ¬ q ∣ boundaryRight x u) ∧
   (∀ q : ℕ, Nat.Prime q → ¬ q ∣ d → ¬ q ∣ boundaryLeft x u))

/-- `boundaryProd` 直入力を facade 入口へ持ち上げる。 -/
theorem nonExceptionalBoundaryEntrance_of_not_dvd_boundaryProd
    {d x u : ℕ}
    (hNonExcNotDvdBoundaryProd :
      ∀ q : ℕ, Nat.Prime q → ¬ q ∣ d → ¬ q ∣ boundaryProd x u) :
    NonExceptionalBoundaryEntrance d x u :=
  Or.inl hNonExcNotDvdBoundaryProd

/-- `boundaryRight/Left` 入力を facade 入口へ持ち上げる。 -/
theorem nonExceptionalBoundaryEntrance_of_not_dvd_boundarySides
    {d x u : ℕ}
    (hNonExcNotDvdRight :
      ∀ q : ℕ, Nat.Prime q → ¬ q ∣ d → ¬ q ∣ boundaryRight x u)
    (hNonExcNotDvdLeft :
      ∀ q : ℕ, Nat.Prime q → ¬ q ∣ d → ¬ q ∣ boundaryLeft x u) :
    NonExceptionalBoundaryEntrance d x u :=
  Or.inr ⟨hNonExcNotDvdRight, hNonExcNotDvdLeft⟩

/--
boundary 入口 facade から `hNonExcNotDvdBoundaryProd` を抽出する。
-/
theorem nonExceptionalNotDvd_boundaryProd_of_boundaryEntrance
    {d x u : ℕ}
    (hNonExcBoundary : NonExceptionalBoundaryEntrance d x u) :
    ∀ q : ℕ, Nat.Prime q → ¬ q ∣ d → ¬ q ∣ boundaryProd x u := by
  rcases hNonExcBoundary with hNonExcNotDvdBoundaryProd | ⟨hNonExcNotDvdRight, hNonExcNotDvdLeft⟩
  · exact hNonExcNotDvdBoundaryProd
  · exact
      nonExceptionalNotDvd_boundaryProd_of_not_dvd_boundarySides
        (d := d) (x := x) (u := u) hNonExcNotDvdRight hNonExcNotDvdLeft

/--
非例外層での kernel→boundary prime-power 連鎖（`k>0`）から、
valuation 比較 `hNonExcLeRev` を導出する。
-/
theorem nonExceptionalLeRev_of_primePow_kernelRight_to_boundaryProd
    {d x u : ℕ}
    (hd2 : 2 ≤ d) (hx : 0 < x) (hu : 0 < u)
    (hNonExcPowRev :
      ∀ q k : ℕ, Nat.Prime q → ¬ q ∣ d → 0 < k →
        q ^ k ∣ kernelRight d x u → q ^ k ∣ boundaryProd x u) :
    ∀ q : ℕ, Nat.Prime q → ¬ q ∣ d →
      padicValNat q (kernelRight d x u) ≤ padicValNat q (boundaryProd x u) := by
  intro q hqP hq_ndvd_d
  haveI : Fact q.Prime := ⟨hqP⟩
  have hK0 : kernelRight d x u ≠ 0 := by
    simpa [kernelRight] using
      (GN_ne_zero_nat_of_two_le (d := d) (x := x) (u := u) hd2 hx hu)
  have hB0 : boundaryProd x u ≠ 0 := Nat.mul_ne_zero (Nat.ne_of_gt hx) (Nat.ne_of_gt hu)
  by_cases hKz : padicValNat q (kernelRight d x u) = 0
  · rw [hKz]
    exact Nat.zero_le _
  · have hKpos : 0 < padicValNat q (kernelRight d x u) := Nat.pos_iff_ne_zero.mpr hKz
    have hpow_dvd_kernel :
        q ^ padicValNat q (kernelRight d x u) ∣ kernelRight d x u :=
      (padicValNat_dvd_iff_le
        (p := q) (a := kernelRight d x u) (n := padicValNat q (kernelRight d x u)) hK0).2 le_rfl
    have hpow_dvd_boundary :
        q ^ padicValNat q (kernelRight d x u) ∣ boundaryProd x u :=
      hNonExcPowRev q (padicValNat q (kernelRight d x u)) hqP hq_ndvd_d hKpos hpow_dvd_kernel
    exact
      (padicValNat_dvd_iff_le
        (p := q) (a := boundaryProd x u) (n := padicValNat q (kernelRight d x u)) hB0).1
        hpow_dvd_boundary

/--
非例外層比較 `hNonExcBK`（`boundaryProd ↔ kernelRight`）から、
kernel→boundary の prime-power 連鎖 `hNonExcPowRev` を抽出する。
-/
theorem nonExceptionalPowRev_of_nonExceptionalBK
    {d x u : ℕ}
    (hNonExcBK :
      ∀ q k : ℕ, Nat.Prime q → ¬ q ∣ d →
        (q ^ k ∣ boundaryProd x u ↔ q ^ k ∣ kernelRight d x u)) :
    ∀ q k : ℕ, Nat.Prime q → ¬ q ∣ d → 0 < k →
      q ^ k ∣ kernelRight d x u → q ^ k ∣ boundaryProd x u := by
  intro q k hqP hq_ndvd_d _hk hqk_dvd_kernel
  exact (hNonExcBK q k hqP hq_ndvd_d).2 hqk_dvd_kernel

/--
`hNonExcVal`（valuation 等式）から、`hNonExcPowRev` を自動供給する wrapper。
-/
theorem nonExceptionalPowRev_of_padicValNat_eq_boundaryProd_kernelRight
    {d x u : ℕ}
    (hd2 : 2 ≤ d) (hx : 0 < x) (hu : 0 < u)
    (hNonExcVal : ∀ q : ℕ, Nat.Prime q → ¬ q ∣ d →
      padicValNat q (boundaryProd x u) = padicValNat q (kernelRight d x u)) :
    ∀ q k : ℕ, Nat.Prime q → ¬ q ∣ d → 0 < k →
      q ^ k ∣ kernelRight d x u → q ^ k ∣ boundaryProd x u := by
  have hNonExcBK :
      ∀ q k : ℕ, Nat.Prime q → ¬ q ∣ d →
        (q ^ k ∣ boundaryProd x u ↔ q ^ k ∣ kernelRight d x u) :=
    nonExceptionalBK_of_padicValNat_eq_boundaryProd_kernelRight
      (d := d) (x := x) (u := u) hd2 hx hu hNonExcVal
  exact nonExceptionalPowRev_of_nonExceptionalBK
    (d := d) (x := x) (u := u) hNonExcBK

/--
非例外層で `v_q(kernelRight) ≤ v_q(boundaryProd)` と `boundaryProd` 側 `¬dvd` があれば、
`kernelRight` 側 `¬dvd` を導出できる。
-/
theorem nonExceptionalNotDvd_kernelRight_of_padicValNat_le_boundaryProd_and_not_dvd_boundaryProd
    {d x u : ℕ}
    (hd2 : 2 ≤ d) (hx : 0 < x) (hu : 0 < u)
    (hNonExcLeRev :
      ∀ q : ℕ, Nat.Prime q → ¬ q ∣ d →
        padicValNat q (kernelRight d x u) ≤ padicValNat q (boundaryProd x u))
    (hNonExcNotDvdBoundaryProd :
      ∀ q : ℕ, Nat.Prime q → ¬ q ∣ d → ¬ q ∣ boundaryProd x u) :
    ∀ q : ℕ, Nat.Prime q → ¬ q ∣ d → ¬ q ∣ kernelRight d x u := by
  intro q hqP hq_ndvd_d hq_dvd_kernel
  have hBz : padicValNat q (boundaryProd x u) = 0 :=
    padicValNat.eq_zero_of_not_dvd (hNonExcNotDvdBoundaryProd q hqP hq_ndvd_d)
  have hK_le_zero : padicValNat q (kernelRight d x u) ≤ 0 := by
    calc
      padicValNat q (kernelRight d x u) ≤ padicValNat q (boundaryProd x u) :=
        hNonExcLeRev q hqP hq_ndvd_d
      _ = 0 := hBz
  have hKz : padicValNat q (kernelRight d x u) = 0 := Nat.le_zero.mp hK_le_zero
  haveI : Fact q.Prime := ⟨hqP⟩
  have hK0 : kernelRight d x u ≠ 0 := by
    simpa [kernelRight] using
      (GN_ne_zero_nat_of_two_le (d := d) (x := x) (u := u) hd2 hx hu)
  have h1le : 1 ≤ padicValNat q (kernelRight d x u) := by
    exact
      (padicValNat_dvd_iff_le (p := q) (a := kernelRight d x u) (n := 1) hK0).1
        (by simpa using hq_dvd_kernel)
  rw [hKz] at h1le
  exact Nat.not_succ_le_zero 0 h1le

/--
非例外層で `v_q(kernelRight) ≤ v_q(boundaryProd)` と `boundaryProd` 側 `¬dvd` があれば、
`hNonExcZero`（両側 0 化）を導出できる。
-/
theorem nonExceptionalZero_of_padicValNat_le_boundaryProd_and_not_dvd_boundaryProd
    {d x u : ℕ}
    (hd2 : 2 ≤ d) (hx : 0 < x) (hu : 0 < u)
    (hNonExcLeRev :
      ∀ q : ℕ, Nat.Prime q → ¬ q ∣ d →
        padicValNat q (kernelRight d x u) ≤ padicValNat q (boundaryProd x u))
    (hNonExcNotDvdBoundaryProd :
      ∀ q : ℕ, Nat.Prime q → ¬ q ∣ d → ¬ q ∣ boundaryProd x u) :
    ∀ q : ℕ, Nat.Prime q → ¬ q ∣ d →
      padicValNat q (boundaryProd x u) = 0 ∧
      padicValNat q (kernelRight d x u) = 0 := by
  intro q hqP hq_ndvd_d
  have hBz : padicValNat q (boundaryProd x u) = 0 :=
    padicValNat.eq_zero_of_not_dvd (hNonExcNotDvdBoundaryProd q hqP hq_ndvd_d)
  have hKnot : ¬ q ∣ kernelRight d x u :=
    nonExceptionalNotDvd_kernelRight_of_padicValNat_le_boundaryProd_and_not_dvd_boundaryProd
      (d := d) (x := x) (u := u) hd2 hx hu hNonExcLeRev hNonExcNotDvdBoundaryProd
      q hqP hq_ndvd_d
  exact ⟨hBz, padicValNat.eq_zero_of_not_dvd hKnot⟩

/--
非例外層で `boundaryRight/Left` 側の `¬dvd` と
`v_q(kernelRight) ≤ v_q(boundaryProd)` から `hNonExcZero` を導出する。
-/
theorem nonExceptionalZero_of_padicValNat_le_boundaryProd_and_not_dvd_boundarySides
    {d x u : ℕ}
    (hd2 : 2 ≤ d) (hx : 0 < x) (hu : 0 < u)
    (hNonExcLeRev :
      ∀ q : ℕ, Nat.Prime q → ¬ q ∣ d →
        padicValNat q (kernelRight d x u) ≤ padicValNat q (boundaryProd x u))
    (hNonExcNotDvdRight :
      ∀ q : ℕ, Nat.Prime q → ¬ q ∣ d → ¬ q ∣ boundaryRight x u)
    (hNonExcNotDvdLeft :
      ∀ q : ℕ, Nat.Prime q → ¬ q ∣ d → ¬ q ∣ boundaryLeft x u) :
    ∀ q : ℕ, Nat.Prime q → ¬ q ∣ d →
      padicValNat q (boundaryProd x u) = 0 ∧
      padicValNat q (kernelRight d x u) = 0 := by
  have hNonExcNotDvdBoundaryProd :
      ∀ q : ℕ, Nat.Prime q → ¬ q ∣ d → ¬ q ∣ boundaryProd x u :=
    nonExceptionalNotDvd_boundaryProd_of_not_dvd_boundarySides
      (d := d) (x := x) (u := u) hNonExcNotDvdRight hNonExcNotDvdLeft
  exact
    nonExceptionalZero_of_padicValNat_le_boundaryProd_and_not_dvd_boundaryProd
      (d := d) (x := x) (u := u) hd2 hx hu hNonExcLeRev hNonExcNotDvdBoundaryProd

/--
非例外層の具体 `¬dvd` 補題（`boundaryProd`/`kernelRight`）から `hNonExcZero` を自動導出する。
-/
theorem nonExceptionalZero_of_not_dvd_boundaryProd_and_kernelRight
    {d x u : ℕ}
    (hNonExcNotDvdBoundaryProd :
      ∀ q : ℕ, Nat.Prime q → ¬ q ∣ d → ¬ q ∣ boundaryProd x u)
    (hNonExcNotDvdKernelRight :
      ∀ q : ℕ, Nat.Prime q → ¬ q ∣ d → ¬ q ∣ kernelRight d x u) :
    ∀ q : ℕ, Nat.Prime q → ¬ q ∣ d →
      padicValNat q (boundaryProd x u) = 0 ∧
      padicValNat q (kernelRight d x u) = 0 := by
  intro q hqP hq_ndvd_d
  exact ⟨
    padicValNat.eq_zero_of_not_dvd (hNonExcNotDvdBoundaryProd q hqP hq_ndvd_d),
    padicValNat.eq_zero_of_not_dvd (hNonExcNotDvdKernelRight q hqP hq_ndvd_d)
  ⟩

/--
`hExcLe/hExcLeRev/hNonExcZero` を `GN` 側の具体 valuation/prime-divisibility 補題から自動導出し、
`m = n` へ接続する end-to-end 版。
-/
theorem unique_factorization_nat_via_boundaryProd_kernelRight_split_layers_e2e_autoGNVal
    {d x u m n : ℕ}
    (hm : m ≠ 0) (hn : n ≠ 0)
    (hd2 : 2 ≤ d) (hx : 0 < x) (hu : 0 < u)
    (hExcM : ∀ q k : ℕ, Nat.Prime q → q ∣ d →
      (q ^ k ∣ m ↔ q ^ k ∣ boundaryProd x u))
    (hExcK : ∀ q k : ℕ, Nat.Prime q → q ∣ d →
      (q ^ k ∣ n ↔ q ^ k ∣ kernelRight d x u))
    (hExcVal : ∀ q : ℕ, Nat.Prime q → q ∣ d →
      padicValNat q (boundaryProd x u) = padicValNat q (kernelRight d x u))
    (hNonExcM : ∀ q k : ℕ, Nat.Prime q → ¬ q ∣ d →
      (q ^ k ∣ m ↔ q ^ k ∣ boundaryProd x u))
    (hNonExcK : ∀ q k : ℕ, Nat.Prime q → ¬ q ∣ d →
      (q ^ k ∣ n ↔ q ^ k ∣ kernelRight d x u))
    (hNonExcNotDvdBoundaryProd :
      ∀ q : ℕ, Nat.Prime q → ¬ q ∣ d → ¬ q ∣ boundaryProd x u)
    (hNonExcNotDvdKernelRight :
      ∀ q : ℕ, Nat.Prime q → ¬ q ∣ d → ¬ q ∣ kernelRight d x u) :
    m = n := by
  have hExcLe :
      ∀ q : ℕ, Nat.Prime q → q ∣ d →
        padicValNat q (boundaryProd x u) ≤ padicValNat q (kernelRight d x u) :=
    exceptionalLe_of_padicValNat_eq_boundaryProd_kernelRight
      (d := d) (x := x) (u := u) hExcVal
  have hExcLeRev :
      ∀ q : ℕ, Nat.Prime q → q ∣ d →
        padicValNat q (kernelRight d x u) ≤ padicValNat q (boundaryProd x u) :=
    exceptionalLeRev_of_padicValNat_eq_boundaryProd_kernelRight
      (d := d) (x := x) (u := u) hExcVal
  have hNonExcZero :
      ∀ q : ℕ, Nat.Prime q → ¬ q ∣ d →
        padicValNat q (boundaryProd x u) = 0 ∧
        padicValNat q (kernelRight d x u) = 0 :=
    nonExceptionalZero_of_not_dvd_boundaryProd_and_kernelRight
      (d := d) (x := x) (u := u)
      hNonExcNotDvdBoundaryProd hNonExcNotDvdKernelRight
  exact unique_factorization_nat_via_boundaryProd_kernelRight_split_layers_e2e_autoBK_le_zero
    (d := d) (x := x) (u := u) (m := m) (n := n)
    hm hn hd2 hx hu
    hExcM hExcK hExcLe hExcLeRev
    hNonExcM hNonExcK hNonExcZero

/--
`autoGNVal` の弱化版:
非例外層の `kernelRight` 側は `¬dvd` を直接要求せず、
`v_q(kernelRight) ≤ v_q(boundaryProd)` と `boundaryProd` 側 `¬dvd` から自動供給する。
-/
theorem unique_factorization_nat_via_boundaryProd_kernelRight_split_layers_e2e_autoGNVal_weakKernel
    {d x u m n : ℕ}
    (hm : m ≠ 0) (hn : n ≠ 0)
    (hd2 : 2 ≤ d) (hx : 0 < x) (hu : 0 < u)
    (hExcM : ∀ q k : ℕ, Nat.Prime q → q ∣ d →
      (q ^ k ∣ m ↔ q ^ k ∣ boundaryProd x u))
    (hExcK : ∀ q k : ℕ, Nat.Prime q → q ∣ d →
      (q ^ k ∣ n ↔ q ^ k ∣ kernelRight d x u))
    (hExcVal : ∀ q : ℕ, Nat.Prime q → q ∣ d →
      padicValNat q (boundaryProd x u) = padicValNat q (kernelRight d x u))
    (hNonExcM : ∀ q k : ℕ, Nat.Prime q → ¬ q ∣ d →
      (q ^ k ∣ m ↔ q ^ k ∣ boundaryProd x u))
    (hNonExcK : ∀ q k : ℕ, Nat.Prime q → ¬ q ∣ d →
      (q ^ k ∣ n ↔ q ^ k ∣ kernelRight d x u))
    (hNonExcLeRev :
      ∀ q : ℕ, Nat.Prime q → ¬ q ∣ d →
        padicValNat q (kernelRight d x u) ≤ padicValNat q (boundaryProd x u))
    (hNonExcNotDvdBoundaryProd :
      ∀ q : ℕ, Nat.Prime q → ¬ q ∣ d → ¬ q ∣ boundaryProd x u) :
    m = n := by
  have hNonExcNotDvdKernelRight :
      ∀ q : ℕ, Nat.Prime q → ¬ q ∣ d → ¬ q ∣ kernelRight d x u :=
    nonExceptionalNotDvd_kernelRight_of_padicValNat_le_boundaryProd_and_not_dvd_boundaryProd
      (d := d) (x := x) (u := u) hd2 hx hu hNonExcLeRev hNonExcNotDvdBoundaryProd
  exact unique_factorization_nat_via_boundaryProd_kernelRight_split_layers_e2e_autoGNVal
    (d := d) (x := x) (u := u) (m := m) (n := n)
    hm hn hd2 hx hu
    hExcM hExcK hExcVal
    hNonExcM hNonExcK
    hNonExcNotDvdBoundaryProd hNonExcNotDvdKernelRight

/--
`autoGNVal_weakKernel` の境界 side 入力版:
非例外層 `boundaryRight/Left` 側 `¬dvd` から `boundaryProd` 側 `¬dvd` を自動生成して接続する。
-/
theorem
    unique_factorization_nat_via_boundaryProd_kernelRight_e2e_autoGNVal_weakKernel_boundarySides
    {d x u m n : ℕ}
    (hm : m ≠ 0) (hn : n ≠ 0)
    (hd2 : 2 ≤ d) (hx : 0 < x) (hu : 0 < u)
    (hExcM : ∀ q k : ℕ, Nat.Prime q → q ∣ d →
      (q ^ k ∣ m ↔ q ^ k ∣ boundaryProd x u))
    (hExcK : ∀ q k : ℕ, Nat.Prime q → q ∣ d →
      (q ^ k ∣ n ↔ q ^ k ∣ kernelRight d x u))
    (hExcVal : ∀ q : ℕ, Nat.Prime q → q ∣ d →
      padicValNat q (boundaryProd x u) = padicValNat q (kernelRight d x u))
    (hNonExcM : ∀ q k : ℕ, Nat.Prime q → ¬ q ∣ d →
      (q ^ k ∣ m ↔ q ^ k ∣ boundaryProd x u))
    (hNonExcK : ∀ q k : ℕ, Nat.Prime q → ¬ q ∣ d →
      (q ^ k ∣ n ↔ q ^ k ∣ kernelRight d x u))
    (hNonExcLeRev :
      ∀ q : ℕ, Nat.Prime q → ¬ q ∣ d →
        padicValNat q (kernelRight d x u) ≤ padicValNat q (boundaryProd x u))
    (hNonExcNotDvdRight :
      ∀ q : ℕ, Nat.Prime q → ¬ q ∣ d → ¬ q ∣ boundaryRight x u)
    (hNonExcNotDvdLeft :
      ∀ q : ℕ, Nat.Prime q → ¬ q ∣ d → ¬ q ∣ boundaryLeft x u) :
    m = n := by
  have hNonExcNotDvdBoundaryProd :
      ∀ q : ℕ, Nat.Prime q → ¬ q ∣ d → ¬ q ∣ boundaryProd x u :=
    nonExceptionalNotDvd_boundaryProd_of_not_dvd_boundarySides
      (d := d) (x := x) (u := u) hNonExcNotDvdRight hNonExcNotDvdLeft
  exact unique_factorization_nat_via_boundaryProd_kernelRight_split_layers_e2e_autoGNVal_weakKernel
    (d := d) (x := x) (u := u) (m := m) (n := n)
    hm hn hd2 hx hu
    hExcM hExcK hExcVal
    hNonExcM hNonExcK
    hNonExcLeRev hNonExcNotDvdBoundaryProd

/--
`autoGNVal_weakKernel` の facade 版:
非例外層の boundary 入口（`boundaryProd` / `boundarySides`）を統一して受ける。
-/
theorem
    unique_factorization_nat_via_boundaryProd_kernelRight_e2e_autoGNVal_weakKernel_boundaryFacade
    {d x u m n : ℕ}
    (hm : m ≠ 0) (hn : n ≠ 0)
    (hd2 : 2 ≤ d) (hx : 0 < x) (hu : 0 < u)
    (hExcM : ∀ q k : ℕ, Nat.Prime q → q ∣ d →
      (q ^ k ∣ m ↔ q ^ k ∣ boundaryProd x u))
    (hExcK : ∀ q k : ℕ, Nat.Prime q → q ∣ d →
      (q ^ k ∣ n ↔ q ^ k ∣ kernelRight d x u))
    (hExcVal : ∀ q : ℕ, Nat.Prime q → q ∣ d →
      padicValNat q (boundaryProd x u) = padicValNat q (kernelRight d x u))
    (hNonExcM : ∀ q k : ℕ, Nat.Prime q → ¬ q ∣ d →
      (q ^ k ∣ m ↔ q ^ k ∣ boundaryProd x u))
    (hNonExcK : ∀ q k : ℕ, Nat.Prime q → ¬ q ∣ d →
      (q ^ k ∣ n ↔ q ^ k ∣ kernelRight d x u))
    (hNonExcLeRev :
      ∀ q : ℕ, Nat.Prime q → ¬ q ∣ d →
        padicValNat q (kernelRight d x u) ≤ padicValNat q (boundaryProd x u))
    (hNonExcBoundary : NonExceptionalBoundaryEntrance d x u) :
    m = n := by
  have hNonExcNotDvdBoundaryProd :
      ∀ q : ℕ, Nat.Prime q → ¬ q ∣ d → ¬ q ∣ boundaryProd x u :=
    nonExceptionalNotDvd_boundaryProd_of_boundaryEntrance
      (d := d) (x := x) (u := u) hNonExcBoundary
  exact unique_factorization_nat_via_boundaryProd_kernelRight_split_layers_e2e_autoGNVal_weakKernel
    (d := d) (x := x) (u := u) (m := m) (n := n)
    hm hn hd2 hx hu
    hExcM hExcK hExcVal
    hNonExcM hNonExcK
    hNonExcLeRev hNonExcNotDvdBoundaryProd

/--
`hNonExcVal` 入力で、非例外層 boundary 入口を facade 化した最終 e2e wrapper。
-/
theorem
    unique_factorization_nat_via_boundaryProd_kernelRight_e2e_autoGNVal_nonExcVal_boundaryFacade
    {d x u m n : ℕ}
    (hm : m ≠ 0) (hn : n ≠ 0)
    (hd2 : 2 ≤ d) (hx : 0 < x) (hu : 0 < u)
    (hExcM : ∀ q k : ℕ, Nat.Prime q → q ∣ d →
      (q ^ k ∣ m ↔ q ^ k ∣ boundaryProd x u))
    (hExcK : ∀ q k : ℕ, Nat.Prime q → q ∣ d →
      (q ^ k ∣ n ↔ q ^ k ∣ kernelRight d x u))
    (hExcVal : ∀ q : ℕ, Nat.Prime q → q ∣ d →
      padicValNat q (boundaryProd x u) = padicValNat q (kernelRight d x u))
    (hNonExcM : ∀ q k : ℕ, Nat.Prime q → ¬ q ∣ d →
      (q ^ k ∣ m ↔ q ^ k ∣ boundaryProd x u))
    (hNonExcK : ∀ q k : ℕ, Nat.Prime q → ¬ q ∣ d →
      (q ^ k ∣ n ↔ q ^ k ∣ kernelRight d x u))
    (hNonExcVal : ∀ q : ℕ, Nat.Prime q → ¬ q ∣ d →
      padicValNat q (boundaryProd x u) = padicValNat q (kernelRight d x u))
    (hNonExcBoundary : NonExceptionalBoundaryEntrance d x u) :
    m = n := by
  have hNonExcLeRev :
      ∀ q : ℕ, Nat.Prime q → ¬ q ∣ d →
        padicValNat q (kernelRight d x u) ≤ padicValNat q (boundaryProd x u) := by
    intro q hqP hq_ndvd_d
    exact le_of_eq (hNonExcVal q hqP hq_ndvd_d).symm
  exact
    unique_factorization_nat_via_boundaryProd_kernelRight_e2e_autoGNVal_weakKernel_boundaryFacade
    (d := d) (x := x) (u := u) (m := m) (n := n)
    hm hn hd2 hx hu
    hExcM hExcK hExcVal
    hNonExcM hNonExcK
    hNonExcLeRev hNonExcBoundary

/--
`hNonExcBK` 入力で、非例外層 boundary 入口を facade 化した最終 e2e wrapper。
-/
theorem
    unique_factorization_nat_via_boundaryProd_kernelRight_e2e_autoGNVal_nonExcBK_boundaryFacade
    {d x u m n : ℕ}
    (hm : m ≠ 0) (hn : n ≠ 0)
    (hd2 : 2 ≤ d) (hx : 0 < x) (hu : 0 < u)
    (hExcM : ∀ q k : ℕ, Nat.Prime q → q ∣ d →
      (q ^ k ∣ m ↔ q ^ k ∣ boundaryProd x u))
    (hExcK : ∀ q k : ℕ, Nat.Prime q → q ∣ d →
      (q ^ k ∣ n ↔ q ^ k ∣ kernelRight d x u))
    (hExcVal : ∀ q : ℕ, Nat.Prime q → q ∣ d →
      padicValNat q (boundaryProd x u) = padicValNat q (kernelRight d x u))
    (hNonExcM : ∀ q k : ℕ, Nat.Prime q → ¬ q ∣ d →
      (q ^ k ∣ m ↔ q ^ k ∣ boundaryProd x u))
    (hNonExcK : ∀ q k : ℕ, Nat.Prime q → ¬ q ∣ d →
      (q ^ k ∣ n ↔ q ^ k ∣ kernelRight d x u))
    (hNonExcBK :
      ∀ q k : ℕ, Nat.Prime q → ¬ q ∣ d →
        (q ^ k ∣ boundaryProd x u ↔ q ^ k ∣ kernelRight d x u))
    (hNonExcBoundary : NonExceptionalBoundaryEntrance d x u) :
    m = n := by
  have hNonExcPowRev :
      ∀ q k : ℕ, Nat.Prime q → ¬ q ∣ d → 0 < k →
        q ^ k ∣ kernelRight d x u → q ^ k ∣ boundaryProd x u :=
    nonExceptionalPowRev_of_nonExceptionalBK
      (d := d) (x := x) (u := u) hNonExcBK
  have hNonExcLeRev :
      ∀ q : ℕ, Nat.Prime q → ¬ q ∣ d →
        padicValNat q (kernelRight d x u) ≤ padicValNat q (boundaryProd x u) :=
    nonExceptionalLeRev_of_primePow_kernelRight_to_boundaryProd
      (d := d) (x := x) (u := u) hd2 hx hu hNonExcPowRev
  exact
    unique_factorization_nat_via_boundaryProd_kernelRight_e2e_autoGNVal_weakKernel_boundaryFacade
    (d := d) (x := x) (u := u) (m := m) (n := n)
    hm hn hd2 hx hu
    hExcM hExcK hExcVal
    hNonExcM hNonExcK
    hNonExcLeRev hNonExcBoundary

/--
`hNonExcLeRev` 自動供給版（prime-power 連鎖入力）:
非例外層の kernel→boundary prime-power 補題（`k>0`）から `hNonExcLeRev` を構成する。
-/
theorem unique_factorization_nat_via_boundaryProd_kernelRight_e2e_autoGNVal_powChain_boundarySides
    {d x u m n : ℕ}
    (hm : m ≠ 0) (hn : n ≠ 0)
    (hd2 : 2 ≤ d) (hx : 0 < x) (hu : 0 < u)
    (hExcM : ∀ q k : ℕ, Nat.Prime q → q ∣ d →
      (q ^ k ∣ m ↔ q ^ k ∣ boundaryProd x u))
    (hExcK : ∀ q k : ℕ, Nat.Prime q → q ∣ d →
      (q ^ k ∣ n ↔ q ^ k ∣ kernelRight d x u))
    (hExcVal : ∀ q : ℕ, Nat.Prime q → q ∣ d →
      padicValNat q (boundaryProd x u) = padicValNat q (kernelRight d x u))
    (hNonExcM : ∀ q k : ℕ, Nat.Prime q → ¬ q ∣ d →
      (q ^ k ∣ m ↔ q ^ k ∣ boundaryProd x u))
    (hNonExcK : ∀ q k : ℕ, Nat.Prime q → ¬ q ∣ d →
      (q ^ k ∣ n ↔ q ^ k ∣ kernelRight d x u))
    (hNonExcPowRev :
      ∀ q k : ℕ, Nat.Prime q → ¬ q ∣ d → 0 < k →
        q ^ k ∣ kernelRight d x u → q ^ k ∣ boundaryProd x u)
    (hNonExcNotDvdRight :
      ∀ q : ℕ, Nat.Prime q → ¬ q ∣ d → ¬ q ∣ boundaryRight x u)
    (hNonExcNotDvdLeft :
      ∀ q : ℕ, Nat.Prime q → ¬ q ∣ d → ¬ q ∣ boundaryLeft x u) :
    m = n := by
  have hNonExcLeRev :
      ∀ q : ℕ, Nat.Prime q → ¬ q ∣ d →
        padicValNat q (kernelRight d x u) ≤ padicValNat q (boundaryProd x u) :=
    nonExceptionalLeRev_of_primePow_kernelRight_to_boundaryProd
      (d := d) (x := x) (u := u) hd2 hx hu hNonExcPowRev
  exact unique_factorization_nat_via_boundaryProd_kernelRight_e2e_autoGNVal_weakKernel_boundarySides
    (d := d) (x := x) (u := u) (m := m) (n := n)
    hm hn hd2 hx hu
    hExcM hExcK hExcVal
    hNonExcM hNonExcK
    hNonExcLeRev hNonExcNotDvdRight hNonExcNotDvdLeft

/--
`hNonExcPowRev` の自動供給版（`hNonExcVal` 入力）:
非例外層 valuation 等式から kernel→boundary の prime-power 連鎖を生成して接続する。
-/
theorem
    unique_factorization_nat_via_boundaryProd_kernelRight_e2e_autoGNVal_powChain_from_nonExcVal
    {d x u m n : ℕ}
    (hm : m ≠ 0) (hn : n ≠ 0)
    (hd2 : 2 ≤ d) (hx : 0 < x) (hu : 0 < u)
    (hExcM : ∀ q k : ℕ, Nat.Prime q → q ∣ d →
      (q ^ k ∣ m ↔ q ^ k ∣ boundaryProd x u))
    (hExcK : ∀ q k : ℕ, Nat.Prime q → q ∣ d →
      (q ^ k ∣ n ↔ q ^ k ∣ kernelRight d x u))
    (hExcVal : ∀ q : ℕ, Nat.Prime q → q ∣ d →
      padicValNat q (boundaryProd x u) = padicValNat q (kernelRight d x u))
    (hNonExcM : ∀ q k : ℕ, Nat.Prime q → ¬ q ∣ d →
      (q ^ k ∣ m ↔ q ^ k ∣ boundaryProd x u))
    (hNonExcK : ∀ q k : ℕ, Nat.Prime q → ¬ q ∣ d →
      (q ^ k ∣ n ↔ q ^ k ∣ kernelRight d x u))
    (hNonExcVal : ∀ q : ℕ, Nat.Prime q → ¬ q ∣ d →
      padicValNat q (boundaryProd x u) = padicValNat q (kernelRight d x u))
    (hNonExcNotDvdRight :
      ∀ q : ℕ, Nat.Prime q → ¬ q ∣ d → ¬ q ∣ boundaryRight x u)
    (hNonExcNotDvdLeft :
      ∀ q : ℕ, Nat.Prime q → ¬ q ∣ d → ¬ q ∣ boundaryLeft x u) :
    m = n := by
  have hNonExcPowRev :
      ∀ q k : ℕ, Nat.Prime q → ¬ q ∣ d → 0 < k →
        q ^ k ∣ kernelRight d x u → q ^ k ∣ boundaryProd x u :=
    nonExceptionalPowRev_of_padicValNat_eq_boundaryProd_kernelRight
      (d := d) (x := x) (u := u) hd2 hx hu hNonExcVal
  exact unique_factorization_nat_via_boundaryProd_kernelRight_e2e_autoGNVal_powChain_boundarySides
    (d := d) (x := x) (u := u) (m := m) (n := n)
    hm hn hd2 hx hu
    hExcM hExcK hExcVal
    hNonExcM hNonExcK
    hNonExcPowRev hNonExcNotDvdRight hNonExcNotDvdLeft

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
`q ∣ u` なら、`Nat.Coprime x u` の下で `q` は `GN d x u` を割らない。

これは `boundaryProd` 側（`x*u`）の非重複で `q ∣ u` 分岐を処理する補題。
-/
theorem prime_dvd_right_not_dvd_GN_of_coprime
    {d x u q : ℕ}
    (hd1 : 1 ≤ d) (hcop : Nat.Coprime x u)
    (hqP : Nat.Prime q) (hq_dvd_u : q ∣ u) :
    ¬ q ∣ GN d x u := by
  intro hq_dvd_GN
  have hd0 : d ≠ 0 := by omega
  have hq_dvd_xGN : q ∣ x * GN d x u := dvd_mul_of_dvd_right hq_dvd_GN x
  have hq_dvd_u_pow : q ∣ u ^ d :=
    dvd_trans hq_dvd_u (dvd_pow_self u hd0)
  have hq_dvd_rhs : q ∣ x * GN d x u + u ^ d :=
    Nat.dvd_add hq_dvd_xGN hq_dvd_u_pow
  have hq_dvd_sum_pow : q ∣ (x + u) ^ d := by
    simpa [cosmic_id_csr' (R := ℕ) d x u] using hq_dvd_rhs
  have hq_dvd_sum : q ∣ x + u := hqP.dvd_of_dvd_pow hq_dvd_sum_pow
  have hq_dvd_x : q ∣ x := by
    have hq_dvd_sub : q ∣ (x + u) - u := Nat.dvd_sub hq_dvd_sum hq_dvd_u
    simpa [Nat.add_sub_cancel] using hq_dvd_sub
  have hq_dvd_gcd : q ∣ Nat.gcd x u := Nat.dvd_gcd hq_dvd_x hq_dvd_u
  rw [hcop.gcd_eq_one] at hq_dvd_gcd
  exact Nat.Prime.not_dvd_one hqP hq_dvd_gcd

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

/--
`boundaryProd = x*u` についての prime-power 分解読み出し（prototype）。

`q^k ∣ x*u` は「`i+j=k` となる分割で `q^i ∣ x`, `q^j ∣ u`」と同値。
-/
theorem primePow_dvd_boundaryProd_iff_exists_split
    {x u q k : ℕ} (hqP : Nat.Prime q) (hx : 0 < x) (hu : 0 < u) :
    q ^ k ∣ boundaryProd x u ↔
      ∃ i j : ℕ, i + j = k ∧ q ^ i ∣ x ∧ q ^ j ∣ u := by
  haveI : Fact q.Prime := ⟨hqP⟩
  have hx0 : x ≠ 0 := Nat.ne_of_gt hx
  have hu0 : u ≠ 0 := Nat.ne_of_gt hu
  have hxu0 : x * u ≠ 0 := Nat.mul_ne_zero hx0 hu0
  have hmul : padicValNat q (x * u) = padicValNat q x + padicValNat q u :=
    padicValNat.mul (p := q) (a := x) (b := u) hx0 hu0
  constructor
  · intro hqk
    have hk_le_mul : k ≤ padicValNat q (x * u) :=
      (padicValNat_dvd_iff_le (p := q) (a := x * u) (n := k) hxu0).1
        (by simpa [boundaryProd] using hqk)
    have hk_le_sum : k ≤ padicValNat q x + padicValNat q u := by simpa [hmul] using hk_le_mul
    by_cases hkx : k ≤ padicValNat q x
    · refine ⟨k, 0, by simp, ?_, ?_⟩
      · exact (padicValNat_dvd_iff_le (p := q) (a := x) (n := k) hx0).2 hkx
      · simp
    · have hlt : padicValNat q x < k := lt_of_not_ge hkx
      refine ⟨padicValNat q x, k - padicValNat q x, by omega, ?_, ?_⟩
      · exact
          (padicValNat_dvd_iff_le (p := q) (a := x) (n := padicValNat q x) hx0).2 le_rfl
      · have hsub_le : k - padicValNat q x ≤ padicValNat q u :=
          (Nat.sub_le_iff_le_add'.2 hk_le_sum)
        exact
          (padicValNat_dvd_iff_le (p := q) (a := u) (n := k - padicValNat q x) hu0).2 hsub_le
  · rintro ⟨i, j, hij, hqi, hqj⟩
    have hi_le : i ≤ padicValNat q x :=
      (padicValNat_dvd_iff_le (p := q) (a := x) (n := i) hx0).1 hqi
    have hj_le : j ≤ padicValNat q u :=
      (padicValNat_dvd_iff_le (p := q) (a := u) (n := j) hu0).1 hqj
    have hk_le_sum : k ≤ padicValNat q x + padicValNat q u := by
      have hsum_le : i + j ≤ padicValNat q x + padicValNat q u := Nat.add_le_add hi_le hj_le
      simpa [hij] using hsum_le
    have hk_le_mul : k ≤ padicValNat q (x * u) := by simpa [hmul] using hk_le_sum
    exact (padicValNat_dvd_iff_le (p := q) (a := x * u) (n := k) hxu0).2 hk_le_mul

/--
`q ∤ d` 層での prime-power 非重複（boundaryProd vs kernelRight, `k>0` の入口）。

`q^k ∣ boundaryProd x u` なら `q ∤ kernelRight d x u`。
-/
theorem primePow_dvd_boundaryProd_not_dvd_kernelRight_of_coprime_of_not_dvd_exp
    {d x u q k : ℕ}
    (hd1 : 1 ≤ d) (hx : 0 < x) (_hu : 0 < u) (hcop : Nat.Coprime x u)
    (hqP : Nat.Prime q) (hq_ndvd_d : ¬ q ∣ d)
    (hk : 0 < k) (hqk_dvd_boundary : q ^ k ∣ boundaryProd x u) :
    ¬ q ∣ kernelRight d x u := by
  have hq_dvd_boundary : q ∣ boundaryProd x u := by
    exact dvd_trans (dvd_pow_self q (Nat.pos_iff_ne_zero.mp hk)) hqk_dvd_boundary
  have hq_dvd_prod : q ∣ x * u := by
    simpa [boundaryProd] using hq_dvd_boundary
  rcases hqP.dvd_mul.mp hq_dvd_prod with hq_dvd_x | hq_dvd_u
  · simpa [kernelRight] using
      (prime_dvd_left_not_dvd_GN_of_coprime_of_not_dvd_exp
        (d := d) (x := x) (u := u) hd1 hx hcop hqP hq_ndvd_d hq_dvd_x)
  · simpa [kernelRight] using
      (prime_dvd_right_not_dvd_GN_of_coprime
        (d := d) (x := x) (u := u) (q := q) hd1 hcop hqP hq_dvd_u)

/--
`q ∤ d` 層での prime-power 非重複（完全版）。

`q^k ∣ boundaryProd x u`（`k>0`）なら、任意の `l>0` について
`q^l ∤ kernelRight d x u`。
-/
theorem primePow_dvd_boundaryProd_not_primePow_dvd_kernelRight_of_coprime_of_not_dvd_exp
    {d x u q k l : ℕ}
    (hd1 : 1 ≤ d) (hx : 0 < x) (hu : 0 < u) (hcop : Nat.Coprime x u)
    (hqP : Nat.Prime q) (hq_ndvd_d : ¬ q ∣ d)
    (hk : 0 < k) (hl : 0 < l)
    (hqk_dvd_boundary : q ^ k ∣ boundaryProd x u) :
    ¬ q ^ l ∣ kernelRight d x u := by
  intro hql_dvd_kernel
  have hq_dvd_kernel : q ∣ kernelRight d x u := by
    exact dvd_trans (dvd_pow_self q (Nat.pos_iff_ne_zero.mp hl)) hql_dvd_kernel
  exact
    (primePow_dvd_boundaryProd_not_dvd_kernelRight_of_coprime_of_not_dvd_exp
      (d := d) (x := x) (u := u) (q := q) (k := k)
      hd1 hx hu hcop hqP hq_ndvd_d hk hqk_dvd_boundary) hq_dvd_kernel

/--
`hNonExcBK`（`boundaryProd ↔ kernelRight`）と GN 側非重複補題から、
非例外層の `boundaryProd` 側 `¬dvd` を抽出する。
-/
theorem nonExceptionalNotDvd_boundaryProd_of_nonExceptionalBK_of_coprime_of_not_dvd_exp
    {d x u : ℕ}
    (hd1 : 1 ≤ d) (hx : 0 < x) (hu : 0 < u) (hcop : Nat.Coprime x u)
    (hNonExcBK :
      ∀ q k : ℕ, Nat.Prime q → ¬ q ∣ d →
        (q ^ k ∣ boundaryProd x u ↔ q ^ k ∣ kernelRight d x u)) :
    ∀ q : ℕ, Nat.Prime q → ¬ q ∣ d → ¬ q ∣ boundaryProd x u := by
  intro q hqP hq_ndvd_d hq_dvd_boundary
  have hq1_dvd_boundary : q ^ 1 ∣ boundaryProd x u := by simpa using hq_dvd_boundary
  have hq1_dvd_kernel : q ^ 1 ∣ kernelRight d x u :=
    (hNonExcBK q 1 hqP hq_ndvd_d).1 hq1_dvd_boundary
  have hq_dvd_kernel : q ∣ kernelRight d x u := by simpa using hq1_dvd_kernel
  exact
    (primePow_dvd_boundaryProd_not_dvd_kernelRight_of_coprime_of_not_dvd_exp
      (d := d) (x := x) (u := u) (q := q) (k := 1)
      hd1 hx hu hcop hqP hq_ndvd_d (by decide) hq1_dvd_boundary) hq_dvd_kernel

/--
`hNonExcBK` から `hNonExcNotDvdBoundaryProd` を供給する短名 wrapper。
-/
theorem nonExceptionalNotDvd_boundaryProd_from_nonExcBK
    {d x u : ℕ}
    (hd1 : 1 ≤ d) (hx : 0 < x) (hu : 0 < u) (hcop : Nat.Coprime x u)
    (hNonExcBK :
      ∀ q k : ℕ, Nat.Prime q → ¬ q ∣ d →
        (q ^ k ∣ boundaryProd x u ↔ q ^ k ∣ kernelRight d x u)) :
    ∀ q : ℕ, Nat.Prime q → ¬ q ∣ d → ¬ q ∣ boundaryProd x u := by
  exact
    nonExceptionalNotDvd_boundaryProd_of_nonExceptionalBK_of_coprime_of_not_dvd_exp
      (d := d) (x := x) (u := u) hd1 hx hu hcop hNonExcBK

/--
`hNonExcVal` から `hNonExcNotDvdBoundaryProd` を供給する wrapper。
-/
theorem nonExceptionalNotDvd_boundaryProd_from_nonExcVal
    {d x u : ℕ}
    (hd2 : 2 ≤ d) (hx : 0 < x) (hu : 0 < u) (hcop : Nat.Coprime x u)
    (hNonExcVal : ∀ q : ℕ, Nat.Prime q → ¬ q ∣ d →
      padicValNat q (boundaryProd x u) = padicValNat q (kernelRight d x u)) :
    ∀ q : ℕ, Nat.Prime q → ¬ q ∣ d → ¬ q ∣ boundaryProd x u := by
  have hd1 : 1 ≤ d := Nat.le_trans (by decide : 1 ≤ 2) hd2
  have hNonExcBK :
      ∀ q k : ℕ, Nat.Prime q → ¬ q ∣ d →
        (q ^ k ∣ boundaryProd x u ↔ q ^ k ∣ kernelRight d x u) :=
    nonExceptionalBK_of_padicValNat_eq_boundaryProd_kernelRight
      (d := d) (x := x) (u := u) hd2 hx hu hNonExcVal
  exact
    nonExceptionalNotDvd_boundaryProd_from_nonExcBK
      (d := d) (x := x) (u := u) hd1 hx hu hcop hNonExcBK

/--
`boundaryProd` 側 `¬dvd` から、`boundaryRight/Left` 側 `¬dvd` を生成する。
-/
theorem nonExceptionalNotDvd_boundarySides_of_not_dvd_boundaryProd
    {d x u : ℕ}
    (hNonExcNotDvdBoundaryProd :
      ∀ q : ℕ, Nat.Prime q → ¬ q ∣ d → ¬ q ∣ boundaryProd x u) :
    (∀ q : ℕ, Nat.Prime q → ¬ q ∣ d → ¬ q ∣ boundaryRight x u) ∧
    (∀ q : ℕ, Nat.Prime q → ¬ q ∣ d → ¬ q ∣ boundaryLeft x u) := by
  constructor
  · intro q hqP hq_ndvd_d hq_dvd_right
    have hq_dvd_x : q ∣ x := by simpa [boundaryRight] using hq_dvd_right
    have hq_dvd_boundaryProd : q ∣ boundaryProd x u := by
      simpa [boundaryProd] using (dvd_mul_of_dvd_left hq_dvd_x u)
    exact (hNonExcNotDvdBoundaryProd q hqP hq_ndvd_d) hq_dvd_boundaryProd
  · intro q hqP hq_ndvd_d hq_dvd_left
    have hq_dvd_u : q ∣ u := by simpa [boundaryLeft] using hq_dvd_left
    have hq_dvd_boundaryProd : q ∣ boundaryProd x u := by
      simpa [boundaryProd] using (dvd_mul_of_dvd_right hq_dvd_u x)
    exact (hNonExcNotDvdBoundaryProd q hqP hq_ndvd_d) hq_dvd_boundaryProd

/--
`hNonExcBK` と GN 側非重複補題から、`hNonExcNotDvdRight/Left` を自動供給する wrapper。
-/
theorem nonExceptionalNotDvd_boundarySides_of_nonExceptionalBK_of_coprime_of_not_dvd_exp
    {d x u : ℕ}
    (hd1 : 1 ≤ d) (hx : 0 < x) (hu : 0 < u) (hcop : Nat.Coprime x u)
    (hNonExcBK :
      ∀ q k : ℕ, Nat.Prime q → ¬ q ∣ d →
        (q ^ k ∣ boundaryProd x u ↔ q ^ k ∣ kernelRight d x u)) :
    (∀ q : ℕ, Nat.Prime q → ¬ q ∣ d → ¬ q ∣ boundaryRight x u) ∧
    (∀ q : ℕ, Nat.Prime q → ¬ q ∣ d → ¬ q ∣ boundaryLeft x u) := by
  have hNonExcNotDvdBoundaryProd :
      ∀ q : ℕ, Nat.Prime q → ¬ q ∣ d → ¬ q ∣ boundaryProd x u :=
    nonExceptionalNotDvd_boundaryProd_from_nonExcBK
      (d := d) (x := x) (u := u) hd1 hx hu hcop hNonExcBK
  exact
    nonExceptionalNotDvd_boundarySides_of_not_dvd_boundaryProd
      (d := d) (x := x) (u := u) hNonExcNotDvdBoundaryProd

/--
`hNonExcVal`（valuation 等式）から `hNonExcBK` を経由し、
`hNonExcNotDvdRight/Left` を GN 側補題で自動供給する wrapper。
-/
theorem
    nonExceptionalNotDvd_boundarySides_from_nonExcVal
    {d x u : ℕ}
    (hd2 : 2 ≤ d) (hx : 0 < x) (hu : 0 < u) (hcop : Nat.Coprime x u)
    (hNonExcVal : ∀ q : ℕ, Nat.Prime q → ¬ q ∣ d →
      padicValNat q (boundaryProd x u) = padicValNat q (kernelRight d x u)) :
    (∀ q : ℕ, Nat.Prime q → ¬ q ∣ d → ¬ q ∣ boundaryRight x u) ∧
    (∀ q : ℕ, Nat.Prime q → ¬ q ∣ d → ¬ q ∣ boundaryLeft x u) := by
  have hNonExcNotDvdBoundaryProd :
      ∀ q : ℕ, Nat.Prime q → ¬ q ∣ d → ¬ q ∣ boundaryProd x u :=
    nonExceptionalNotDvd_boundaryProd_from_nonExcVal
      (d := d) (x := x) (u := u) hd2 hx hu hcop hNonExcVal
  exact
    nonExceptionalNotDvd_boundarySides_of_not_dvd_boundaryProd
      (d := d) (x := x) (u := u) hNonExcNotDvdBoundaryProd

/--
`hNonExcVal` 入力版の boundary-side 自動供給:
`hNonExcNotDvdRight/Left` を GN 側既存補題から内部生成して接続する。
-/
theorem
    unique_factorization_nat_via_boundaryProd_kernelRight_e2e_autoGNVal_nonExcVal_boundarySides
    {d x u m n : ℕ}
    (hm : m ≠ 0) (hn : n ≠ 0)
    (hd2 : 2 ≤ d) (hx : 0 < x) (hu : 0 < u) (hcop : Nat.Coprime x u)
    (hExcM : ∀ q k : ℕ, Nat.Prime q → q ∣ d →
      (q ^ k ∣ m ↔ q ^ k ∣ boundaryProd x u))
    (hExcK : ∀ q k : ℕ, Nat.Prime q → q ∣ d →
      (q ^ k ∣ n ↔ q ^ k ∣ kernelRight d x u))
    (hExcVal : ∀ q : ℕ, Nat.Prime q → q ∣ d →
      padicValNat q (boundaryProd x u) = padicValNat q (kernelRight d x u))
    (hNonExcM : ∀ q k : ℕ, Nat.Prime q → ¬ q ∣ d →
      (q ^ k ∣ m ↔ q ^ k ∣ boundaryProd x u))
    (hNonExcK : ∀ q k : ℕ, Nat.Prime q → ¬ q ∣ d →
      (q ^ k ∣ n ↔ q ^ k ∣ kernelRight d x u))
    (hNonExcVal : ∀ q : ℕ, Nat.Prime q → ¬ q ∣ d →
      padicValNat q (boundaryProd x u) = padicValNat q (kernelRight d x u)) :
    m = n := by
  have hNonExcBoundary : NonExceptionalBoundaryEntrance d x u := by
    obtain ⟨hNonExcNotDvdRight, hNonExcNotDvdLeft⟩ :=
      nonExceptionalNotDvd_boundarySides_from_nonExcVal
        (d := d) (x := x) (u := u) hd2 hx hu hcop hNonExcVal
    exact
      nonExceptionalBoundaryEntrance_of_not_dvd_boundarySides
        (d := d) (x := x) (u := u) hNonExcNotDvdRight hNonExcNotDvdLeft
  exact
    unique_factorization_nat_via_boundaryProd_kernelRight_e2e_autoGNVal_nonExcVal_boundaryFacade
      (d := d) (x := x) (u := u) (m := m) (n := n)
      hm hn hd2 hx hu
      hExcM hExcK hExcVal
      hNonExcM hNonExcK hNonExcVal
      hNonExcBoundary

/--
`hNonExcBK` から `hNonExcLeRev` と `hNonExcNotDvdBoundaryProd` を自動供給し、
weakKernel 入口へ接続する wrapper。
-/
theorem
    unique_factorization_nat_via_boundaryProd_kernelRight_e2e_autoGNVal_nonExcBK_boundaryProd
    {d x u m n : ℕ}
    (hm : m ≠ 0) (hn : n ≠ 0)
    (hd2 : 2 ≤ d) (hx : 0 < x) (hu : 0 < u) (hcop : Nat.Coprime x u)
    (hExcM : ∀ q k : ℕ, Nat.Prime q → q ∣ d →
      (q ^ k ∣ m ↔ q ^ k ∣ boundaryProd x u))
    (hExcK : ∀ q k : ℕ, Nat.Prime q → q ∣ d →
      (q ^ k ∣ n ↔ q ^ k ∣ kernelRight d x u))
    (hExcVal : ∀ q : ℕ, Nat.Prime q → q ∣ d →
      padicValNat q (boundaryProd x u) = padicValNat q (kernelRight d x u))
    (hNonExcM : ∀ q k : ℕ, Nat.Prime q → ¬ q ∣ d →
      (q ^ k ∣ m ↔ q ^ k ∣ boundaryProd x u))
    (hNonExcK : ∀ q k : ℕ, Nat.Prime q → ¬ q ∣ d →
      (q ^ k ∣ n ↔ q ^ k ∣ kernelRight d x u))
    (hNonExcBK :
      ∀ q k : ℕ, Nat.Prime q → ¬ q ∣ d →
        (q ^ k ∣ boundaryProd x u ↔ q ^ k ∣ kernelRight d x u)) :
    m = n := by
  have hd1 : 1 ≤ d := Nat.le_trans (by decide : 1 ≤ 2) hd2
  have hNonExcNotDvdBoundaryProd :
      ∀ q : ℕ, Nat.Prime q → ¬ q ∣ d → ¬ q ∣ boundaryProd x u :=
    nonExceptionalNotDvd_boundaryProd_from_nonExcBK
      (d := d) (x := x) (u := u) hd1 hx hu hcop hNonExcBK
  have hNonExcBoundary : NonExceptionalBoundaryEntrance d x u :=
    nonExceptionalBoundaryEntrance_of_not_dvd_boundaryProd
      (d := d) (x := x) (u := u) hNonExcNotDvdBoundaryProd
  exact
    unique_factorization_nat_via_boundaryProd_kernelRight_e2e_autoGNVal_nonExcBK_boundaryFacade
      (d := d) (x := x) (u := u) (m := m) (n := n)
      hm hn hd2 hx hu
      hExcM hExcK hExcVal
      hNonExcM hNonExcK hNonExcBK
      hNonExcBoundary

/--
`hNonExcVal` から `hNonExcLeRev` と `hNonExcNotDvdBoundaryProd` を自動供給し、
weakKernel 入口へ接続する wrapper。
-/
theorem
    unique_factorization_nat_via_boundaryProd_kernelRight_e2e_autoGNVal_nonExcVal_boundaryProd
    {d x u m n : ℕ}
    (hm : m ≠ 0) (hn : n ≠ 0)
    (hd2 : 2 ≤ d) (hx : 0 < x) (hu : 0 < u) (hcop : Nat.Coprime x u)
    (hExcM : ∀ q k : ℕ, Nat.Prime q → q ∣ d →
      (q ^ k ∣ m ↔ q ^ k ∣ boundaryProd x u))
    (hExcK : ∀ q k : ℕ, Nat.Prime q → q ∣ d →
      (q ^ k ∣ n ↔ q ^ k ∣ kernelRight d x u))
    (hExcVal : ∀ q : ℕ, Nat.Prime q → q ∣ d →
      padicValNat q (boundaryProd x u) = padicValNat q (kernelRight d x u))
    (hNonExcM : ∀ q k : ℕ, Nat.Prime q → ¬ q ∣ d →
      (q ^ k ∣ m ↔ q ^ k ∣ boundaryProd x u))
    (hNonExcK : ∀ q k : ℕ, Nat.Prime q → ¬ q ∣ d →
      (q ^ k ∣ n ↔ q ^ k ∣ kernelRight d x u))
    (hNonExcVal : ∀ q : ℕ, Nat.Prime q → ¬ q ∣ d →
      padicValNat q (boundaryProd x u) = padicValNat q (kernelRight d x u)) :
    m = n := by
  have hNonExcNotDvdBoundaryProd :
      ∀ q : ℕ, Nat.Prime q → ¬ q ∣ d → ¬ q ∣ boundaryProd x u :=
    nonExceptionalNotDvd_boundaryProd_from_nonExcVal
      (d := d) (x := x) (u := u) hd2 hx hu hcop hNonExcVal
  have hNonExcBoundary : NonExceptionalBoundaryEntrance d x u :=
    nonExceptionalBoundaryEntrance_of_not_dvd_boundaryProd
      (d := d) (x := x) (u := u) hNonExcNotDvdBoundaryProd
  exact
    unique_factorization_nat_via_boundaryProd_kernelRight_e2e_autoGNVal_nonExcVal_boundaryFacade
      (d := d) (x := x) (u := u) (m := m) (n := n)
      hm hn hd2 hx hu
      hExcM hExcK hExcVal
      hNonExcM hNonExcK hNonExcVal
      hNonExcBoundary

/--
`k ≤ v_q(boundaryProd)`（`k>0`）を入口にした `kernelRight` 側の valuation ゼロ化。

`q ∤ d` 層では、`boundaryProd` 側に現れた prime-power は
`kernelRight` 側 support に現れない。
-/
theorem padicValNat_kernelRight_eq_zero_of_pos_le_padicVal_boundaryProd_of_coprime_of_not_dvd_exp
    {d x u q k : ℕ}
    (hd1 : 1 ≤ d) (hx : 0 < x) (hu : 0 < u) (hcop : Nat.Coprime x u)
    (hqP : Nat.Prime q) (hq_ndvd_d : ¬ q ∣ d)
    (hk : 0 < k) (hk_le_boundary : k ≤ padicValNat q (boundaryProd x u)) :
    padicValNat q (kernelRight d x u) = 0 := by
  haveI : Fact q.Prime := ⟨hqP⟩
  have hB0 : boundaryProd x u ≠ 0 := Nat.mul_ne_zero (Nat.ne_of_gt hx) (Nat.ne_of_gt hu)
  have hqk_dvd_boundary : q ^ k ∣ boundaryProd x u :=
    (padicValNat_dvd_iff_le (p := q) (a := boundaryProd x u) (n := k) hB0).2 hk_le_boundary
  have hq_not_dvd_kernel :
      ¬ q ∣ kernelRight d x u :=
    primePow_dvd_boundaryProd_not_dvd_kernelRight_of_coprime_of_not_dvd_exp
      (d := d) (x := x) (u := u) (q := q) (k := k)
      hd1 hx hu hcop hqP hq_ndvd_d hk hqk_dvd_boundary
  exact padicValNat.eq_zero_of_not_dvd hq_not_dvd_kernel

/--
`k ≤ v_q(boundaryProd)`（`k>0`）なら、同じ `k` は `kernelRight` 側 valuation に載らない。

`k ≤ ...` 形 API での直接比較版。
-/
theorem not_le_padicValNat_kernelRight_of_pos_le_padicVal_boundaryProd_of_coprime_of_not_dvd_exp
    {d x u q k : ℕ}
    (hd1 : 1 ≤ d) (hx : 0 < x) (hu : 0 < u) (hcop : Nat.Coprime x u)
    (hqP : Nat.Prime q) (hq_ndvd_d : ¬ q ∣ d)
    (hk : 0 < k) (hk_le_boundary : k ≤ padicValNat q (boundaryProd x u)) :
    ¬ k ≤ padicValNat q (kernelRight d x u) := by
  have hK0 :
      padicValNat q (kernelRight d x u) = 0 :=
    padicValNat_kernelRight_eq_zero_of_pos_le_padicVal_boundaryProd_of_coprime_of_not_dvd_exp
      (d := d) (x := x) (u := u) (q := q) (k := k)
      hd1 hx hu hcop hqP hq_ndvd_d hk hk_le_boundary
  rw [hK0]
  exact Nat.not_le_of_gt hk

/--
`support` 比較 API:
`q ∤ d` 層で `boundaryProd` 側 support にある素数は
`kernelRight` 側 support には現れない。
-/
theorem support_boundaryProd_disjoint_kernelRight_of_coprime_of_not_dvd_exp
    {d x u q : ℕ}
    (hd2 : 2 ≤ d) (hx : 0 < x) (hu : 0 < u) (hcop : Nat.Coprime x u)
    (hq_ndvd_d : ¬ q ∣ d) :
    q ∈ (boundaryProd x u).factorization.support →
    q ∉ (kernelRight d x u).factorization.support := by
  intro hq_mem_boundary hq_mem_kernel
  have hqP : Nat.Prime q :=
    (DkMath.Basic.Nat.mem_support_factorization_iff.mp hq_mem_boundary).2.1
  have hB0 : boundaryProd x u ≠ 0 := Nat.mul_ne_zero (Nat.ne_of_gt hx) (Nat.ne_of_gt hu)
  have hq_dvd_boundary :
      q ∣ boundaryProd x u :=
    (prime_mem_support_iff_dvd (n := boundaryProd x u) (p := q) hB0 hqP).1 hq_mem_boundary
  have hq_not_dvd_kernel :
      ¬ q ∣ kernelRight d x u := by
    have hd1 : 1 ≤ d := Nat.le_trans (by decide : 1 ≤ 2) hd2
    have hq1_dvd_boundary : q ^ 1 ∣ boundaryProd x u := by simpa using hq_dvd_boundary
    exact
      primePow_dvd_boundaryProd_not_dvd_kernelRight_of_coprime_of_not_dvd_exp
        (d := d) (x := x) (u := u) (q := q) (k := 1)
        hd1 hx hu hcop hqP hq_ndvd_d (by decide) hq1_dvd_boundary
  have hK0 : kernelRight d x u ≠ 0 := by
    simpa [kernelRight] using
      (GN_ne_zero_nat_of_two_le (d := d) (x := x) (u := u) hd2 hx hu)
  have hq_dvd_kernel :
      q ∣ kernelRight d x u :=
    (prime_mem_support_iff_dvd (n := kernelRight d x u) (p := q) hK0 hqP).1 hq_mem_kernel
  exact hq_not_dvd_kernel hq_dvd_kernel

/-- `boundaryProd = x*u` の `q`-進付値は和に分解される（wrapper）。 -/
theorem padicValNat_boundaryProd_eq_add
    {x u q : ℕ} (hqP : Nat.Prime q) (hx : 0 < x) (hu : 0 < u) :
    padicValNat q (boundaryProd x u) =
      padicValNat q x + padicValNat q u := by
  haveI : Fact q.Prime := ⟨hqP⟩
  have hx0 : x ≠ 0 := Nat.ne_of_gt hx
  have hu0 : u ≠ 0 := Nat.ne_of_gt hu
  simpa [boundaryProd] using (padicValNat.mul (p := q) (a := x) (b := u) hx0 hu0)

/--
`boundaryProd = x*u` の prime-power 判定（不等式版 wrapper）。

`q^k ∣ boundaryProd x u` を `k ≤ v_q(x)+v_q(u)` に読み替える。
-/
theorem primePow_dvd_boundaryProd_iff_le_padicVal_sum
    {x u q k : ℕ} (hqP : Nat.Prime q) (hx : 0 < x) (hu : 0 < u) :
    q ^ k ∣ boundaryProd x u ↔
      k ≤ padicValNat q x + padicValNat q u := by
  haveI : Fact q.Prime := ⟨hqP⟩
  have hmul : padicValNat q (x * u) = padicValNat q x + padicValNat q u := by
    simpa [boundaryProd] using (padicValNat_boundaryProd_eq_add (q := q) hqP hx hu)
  have hA0 : boundaryProd x u ≠ 0 := by
    exact Nat.mul_ne_zero (Nat.ne_of_gt hx) (Nat.ne_of_gt hu)
  calc
    q ^ k ∣ boundaryProd x u ↔ k ≤ padicValNat q (boundaryProd x u) :=
      (padicValNat_dvd_iff_le (p := q) (a := boundaryProd x u) (n := k) hA0)
    _ ↔ k ≤ padicValNat q x + padicValNat q u := by
      simp [boundaryProd, hmul]

/--
`boundaryProd` と `kernelRight` の積に対する wrapper 形 valuation 加法。
-/
theorem padicValNat_mul_boundaryProd_kernelRight_eq_add_wrapper
    {d x u q : ℕ}
    (hd2 : 2 ≤ d) (hx : 0 < x) (hu : 0 < u) (hqP : Nat.Prime q) :
    padicValNat q (boundaryProd x u * kernelRight d x u) =
      padicValNat q (boundaryProd x u) + padicValNat q (kernelRight d x u) := by
  haveI : Fact q.Prime := ⟨hqP⟩
  have hA0 : boundaryProd x u ≠ 0 := by
    exact Nat.mul_ne_zero (Nat.ne_of_gt hx) (Nat.ne_of_gt hu)
  have hK0 : kernelRight d x u ≠ 0 := by
    simpa [kernelRight] using
      (GN_ne_zero_nat_of_two_le (d := d) (x := x) (u := u) hd2 hx hu)
  simpa [boundaryProd, kernelRight] using
    (padicValNat.mul (p := q) (a := boundaryProd x u) (b := kernelRight d x u) hA0 hK0)

end DkMath.NumberTheory
