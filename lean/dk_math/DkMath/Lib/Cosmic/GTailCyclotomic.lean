/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Cosmic.GTail
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

#print "file: DkMath.Lib.Cosmic.GTailCyclotomic"

/-!
## Cyclotomic bridge for the promoted `GTail` kernel

This file contains the algebraic part of the cyclotomic promotion audit.  It
does not import `DkMath.CFBRC` or any analytic machinery.  The divisor-product
identity is exposed independently, and the prime homogeneous cyclotomic shell
is connected to the `r = 1` `GTail` row.
-/

open scoped BigOperators

namespace DkMath.Lib.NumberTheory

noncomputable section

/-! The one-variable evaluation of the integer cyclotomic polynomial. -/
@[simp] def cyclotomicEval {R : Type _} [CommRing R]
    (m : ℕ) (X : R) : R :=
  Polynomial.eval₂ (Int.castRingHom R) X (Polynomial.cyclotomic m ℤ)

/-!
The product of the cyclotomic factors indexed by the proper nontrivial
divisors of `d`, evaluated in a commutative ring.
-/
theorem prod_cyclotomicEval_eq_geomSum {R : Type _} [CommRing R]
    {d : ℕ} (hd : 0 < d) (X : R) :
    (∏ m ∈ d.divisors.erase 1, cyclotomicEval m X) =
      ∑ i ∈ Finset.range d, X ^ i := by
  have hpoly :
      (∏ m ∈ d.divisors.erase 1, Polynomial.cyclotomic m ℤ) =
        ∑ i ∈ Finset.range d, (Polynomial.X : Polynomial ℤ) ^ i :=
    Polynomial.prod_cyclotomic_eq_geom_sum hd ℤ
  have hEval := congrArg (Polynomial.eval₂ (Int.castRingHom R) X) hpoly
  simpa [cyclotomicEval, Polynomial.eval₂_finsetProd, Polynomial.eval₂_finsetSum] using hEval

end

end DkMath.Lib.NumberTheory

namespace DkMath.CosmicFormula

noncomputable section

/-!
The homogeneous evaluation of an integer polynomial in the degree-`p` shell.
The range restriction is the same finite support used by the prime
cyclotomic polynomial.
-/
@[simp] def GTailCyclotomicHomEval {R : Type _} [CommRing R]
    (p : ℕ) (Φ : Polynomial ℤ) (x u : R) : R :=
  ∑ k ∈ Finset.range p, (Φ.coeff k : R) * (x + u) ^ k * u ^ (p - 1 - k)

/-!
The geometric shell attached to the power difference
`(x + u)^d - u^d`.
-/
@[simp] def GTailCyclotomicShell {R : Type _} [CommSemiring R]
    (d : ℕ) (x u : R) : R :=
  ∑ k ∈ Finset.range d, (x + u) ^ k * u ^ (d - 1 - k)

lemma GTailCyclotomicShell_succ {R : Type _} [CommSemiring R]
    (d : ℕ) (x u : R) :
    GTailCyclotomicShell (d + 1) x u =
      u * GTailCyclotomicShell d x u + (x + u) ^ d := by
  unfold GTailCyclotomicShell
  rw [Finset.sum_range_succ]
  rw [Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro k hk
    have hk' : k < d := Finset.mem_range.mp hk
    have hsub : d + 1 - 1 - k = d - 1 - k + 1 := by omega
    rw [hsub, pow_succ]
    ring
  · simp

theorem add_pow_eq_mul_GTailCyclotomicShell_add_gap
    {R : Type _} [CommSemiring R] (d : ℕ) (x u : R) :
    (x + u) ^ d = x * GTailCyclotomicShell d x u + u ^ d := by
  induction d with
  | zero =>
      simp [GTailCyclotomicShell]
  | succ d ih =>
      rw [pow_succ', ih, add_mul, mul_add, GTailCyclotomicShell_succ, pow_succ]
      rw [ih]
      ring

theorem GTail_one_eq_GTailCyclotomicShell_of_ne_zero
    {R : Type _} [Field R] {d : ℕ} (x u : R) (hx : x ≠ 0) :
    GTail d 1 x u = GTailCyclotomicShell d x u := by
  cases d with
  | zero =>
      simp [GTail, GTailCyclotomicShell]
  | succ d =>
      have htail :
          (x + u) ^ (d + 1) - u ^ (d + 1) = x * GTail (d + 1) 1 x u := by
        have h := higher_tail_eq_pow_mul_GTail (d + 1) 1 x u (by omega)
        simpa [pow_one, Nat.choose_zero_right, pow_zero, one_mul] using h
      have hshell :
          (x + u) ^ (d + 1) - u ^ (d + 1) =
            x * GTailCyclotomicShell (d + 1) x u := by
        rw [sub_eq_iff_eq_add]
        simpa [add_comm, add_left_comm, add_assoc] using
          (add_pow_eq_mul_GTailCyclotomicShell_add_gap (d + 1) x u)
      exact mul_left_cancel₀ hx (htail.symm.trans hshell)

/-! The Nat row and its integer homogeneous-shell realization. -/

theorem natCast_GTail_one_eq_GTailCyclotomicShell
    {p g u : ℕ} (hg : g ≠ 0) :
    ((GTail p 1 g u : ℕ) : ℤ) =
      GTailCyclotomicShell p (g : ℤ) (u : ℤ) := by
  have hq : GTail p 1 (g : ℚ) (u : ℚ) =
      GTailCyclotomicShell p (g : ℚ) (u : ℚ) :=
    GTail_one_eq_GTailCyclotomicShell_of_ne_zero
      (R := ℚ) (d := p) (g : ℚ) (u : ℚ) (by exact_mod_cast hg)
  have hcast : GTail p 1 (g : ℚ) (u : ℚ) =
      (GTail p 1 g u : ℚ) := by
    simp only [GTail]
  have hcast_shell :
      ((GTailCyclotomicShell p (g : ℤ) (u : ℤ) : ℤ) : ℚ) =
        GTailCyclotomicShell p (g : ℚ) (u : ℚ) := by
    simp only [GTailCyclotomicShell]
    push_cast
    rfl
  have hq' : (GTail p 1 g u : ℚ) =
      ((GTailCyclotomicShell p (g : ℤ) (u : ℤ) : ℤ) : ℚ) :=
    hcast.symm.trans (hq.trans hcast_shell.symm)
  have hcast_target :
      (((GTail p 1 g u : ℕ) : ℤ) : ℚ) =
        ((GTailCyclotomicShell p (g : ℤ) (u : ℤ) : ℤ) : ℚ) := by
    simpa using hq'
  exact (Int.cast_injective : Function.Injective (Int.cast : ℤ → ℚ)) hcast_target

theorem GTailCyclotomicHomEval_prime_eq_shell
    {R : Type _} [CommRing R] {p : ℕ} (hp : Nat.Prime p) (x u : R) :
    GTailCyclotomicHomEval p (Polynomial.cyclotomic p ℤ) x u =
      GTailCyclotomicShell p x u := by
  have hΦ : Polynomial.cyclotomic p ℤ =
      ∑ i ∈ Finset.range p, (Polynomial.X : Polynomial ℤ) ^ i := by
    let : Fact p.Prime := ⟨hp⟩
    simpa using (Polynomial.cyclotomic_prime ℤ p)
  have hcoeff : ∀ {k : ℕ}, k < p →
      (Polynomial.cyclotomic p ℤ).coeff k = 1 := by
    intro k hk
    rw [hΦ]
    simp [hk]
  unfold GTailCyclotomicHomEval GTailCyclotomicShell
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k < p := Finset.mem_range.mp hk
  rw [hcoeff hk']
  simp

/-! The prime row of `GTail` is the homogeneous prime cyclotomic shell. -/
theorem GTail_one_eq_cyclotomicHomEval_of_prime
    {R : Type _} [Field R] {p : ℕ} (hp : Nat.Prime p)
    (x u : R) (hx : x ≠ 0) :
    GTail p 1 x u =
      GTailCyclotomicHomEval p (Polynomial.cyclotomic p ℤ) x u := by
  exact (GTail_one_eq_GTailCyclotomicShell_of_ne_zero x u hx).trans
    (GTailCyclotomicHomEval_prime_eq_shell hp x u).symm

end

end DkMath.CosmicFormula
