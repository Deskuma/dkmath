/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CFBRC.Defs
import Mathlib

#print "file: DkMath.CFBRC.Basic"

/-! # CFBRC: Cosmic Formula Binomial Real Complex - Basic Theorems
-/

namespace DkMath.CFBRC

open scoped BigOperators

open DkMath.CosmicFormulaBinom

/--
整数係数多項式 `Φ` に対する shifted homogeneous evaluation:
`∑_{k=0}^{p-1} coeff(Φ,k) * (x+u)^k * u^(p-1-k)`。
-/
@[simp] def cyclotomicShiftedHomEval {R : Type _} [CommRing R]
    (p : ℕ) (Φ : Polynomial ℤ) (x u : R) : R :=
  ∑ k ∈ Finset.range p, (Φ.coeff k : R) * (x + u) ^ k * u ^ (p - 1 - k)

/--
`p` が素数のとき、`cyclotomicPrimeCore p x u` は
`Φ_p` の shifted homogeneous evaluation と一致する。
すなわち prime 円分多項式の係数が `0..p-1` で全て `1` になる事実を反映する。
-/
theorem cyclotomicPrimeCore_eq_shiftedHomEval_cyclotomic_of_prime
    {R : Type _} [CommRing R] {p : ℕ} (hp : Nat.Prime p) (x u : R) :
    cyclotomicPrimeCore p x u =
      cyclotomicShiftedHomEval p (Polynomial.cyclotomic p ℤ) x u := by
  have hΦ : Polynomial.cyclotomic p ℤ =
      ∑ i ∈ Finset.range p, (Polynomial.X : Polynomial ℤ) ^ i := by
    letI : Fact p.Prime := ⟨hp⟩
    simpa using (Polynomial.cyclotomic_prime ℤ p)
  have hcoeff : ∀ {k : ℕ}, k < p → (Polynomial.cyclotomic p ℤ).coeff k = 1 := by
    intro k hk
    rw [hΦ]
    simp [hk]
  unfold cyclotomicPrimeCore cyclotomicShiftedHomEval
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k < p := Finset.mem_range.mp hk
  rw [hcoeff hk']
  simp

/--
`cyclotomicPrimeCore` の 1 段漸化式。
幾何和 `∑_{k=0}^{p} (x+u)^k u^{p-k}` を
`u * (前段)` と末項 `(x+u)^p` に分解する。
-/
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

/--
Cosmic Formula 型の基本恒等式。
`(x+u)^p` を境界差 `x` と core の積
`x * cyclotomicPrimeCore p x u` と `u^p` の和で表す。
-/
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

/--
core 版と `GN` 版の Cosmic Formula を比較し、
`x` を掛けた形では両者が一致することを示す橋渡し補題。
-/
theorem mul_cyclotomicPrimeCore_eq_mul_GN
    {R : Type _} [CommSemiring R] [IsRightCancelAdd R] (p : ℕ) (x u : R) :
    x * cyclotomicPrimeCore p x u = x * GN p x u := by
  have h₁ : (x + u) ^ p = x * cyclotomicPrimeCore p x u + u ^ p :=
    add_pow_eq_mul_cyclotomicPrimeCore_add_gap p x u
  have h₂ : (x + u) ^ p = x * GN p x u + u ^ p := cosmic_id_csr' p x u
  have hcmp : x * cyclotomicPrimeCore p x u + u ^ p = x * GN p x u + u ^ p := h₁.symm.trans h₂
  exact add_right_cancel hcmp

/--
自然数で `x > 0` のとき、左因子消去により
`cyclotomicPrimeCore p x u = GN p x u` を得る。
-/
theorem cyclotomicPrimeCore_eq_GN_nat
    {p x u : ℕ} (hx : 0 < x) :
    cyclotomicPrimeCore p x u = GN p x u := by
  have hmul : x * cyclotomicPrimeCore p x u = x * GN p x u :=
    mul_cyclotomicPrimeCore_eq_mul_GN p x u
  exact Nat.eq_of_mul_eq_mul_left hx hmul

/--
`x > 0` の下での除法同値：
`q ∣ cyclotomicPrimeCore p x u` と `q ∣ GN p x u` は同値。
-/
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

/--
自然数での差冪分解：
`(x+u)^p - u^p = x * cyclotomicPrimeCore p x u`。
-/
lemma sub_eq_mul_cyclotomicPrimeCore_nat (p x u : ℕ) :
    (x + u) ^ p - u ^ p = x * cyclotomicPrimeCore p x u := by
  have hbig : (x + u) ^ p = x * cyclotomicPrimeCore p x u + u ^ p :=
    add_pow_eq_mul_cyclotomicPrimeCore_add_gap p x u
  have hpow : u ^ p ≤ (x + u) ^ p := by
    exact Nat.pow_le_pow_left (Nat.le_add_left u x) p
  omega

/--
素数 `q` について、
`q ∣ ((x+u)^p - u^p)` かつ `q ∤ x` なら `q ∣ cyclotomicPrimeCore p x u`。
差冪分解と素数の積除法判定を用いる。
-/
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
