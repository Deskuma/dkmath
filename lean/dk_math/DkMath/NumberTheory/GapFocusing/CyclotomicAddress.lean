/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Cosmic.GTailCyclotomic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import Mathlib.Data.Nat.Factorization.Basic

#print "file: DkMath.NumberTheory.GapFocusing.CyclotomicAddress"

/-! # Cyclotomic roots in prime characteristic

The cyclotomic roots at a positive degree are classified by the multiplicative
order and powers of the characteristic.  These statements concern divisibility
and roots only; they make no assertion about the valuation of an integer value.
-/

namespace DkMath.NumberTheory.GapFocusing

open Polynomial

/-- A cyclotomic root in prime characteristic occurs exactly at its
multiplicative order times a power of the characteristic.  The positivity of
the degree excludes the infinite-order and zero-element cases automatically. -/
theorem isRoot_cyclotomic_iff_prime_pow_mul_orderOf
    {R : Type*} [CommRing R] [IsDomain R] {q : ℕ} [hq : Fact q.Prime]
    [CharP R q] {n : ℕ} (hn : 0 < n) (z : R) :
    (cyclotomic n R).IsRoot z ↔ ∃ k : ℕ, n = orderOf z * q ^ k := by
  constructor
  · intro hroot
    obtain ⟨k, m, hqm, hnm⟩ :=
      Nat.exists_eq_pow_mul_and_not_dvd hn.ne' q hq.out.ne_one
    let : NeZero (m : R) := NeZero.of_not_dvd R (p := q) hqm
    have hprim : IsPrimitiveRoot z m := by
      apply (isRoot_cyclotomic_prime_pow_mul_iff_of_charP
        (R := R) (p := q) (k := k)).mp
      rwa [← hnm]
    exact ⟨k, hnm.trans (by rw [hprim.eq_orderOf, Nat.mul_comm])⟩
  · rintro ⟨k, hnk⟩
    have hr : orderOf z ≠ 0 := by
      intro hz
      rw [hz, zero_mul] at hnk
      exact hn.ne' hnk
    let : NeZero (orderOf z) := ⟨hr⟩
    let : NeZero ((orderOf z : ℕ) : R) := (IsPrimitiveRoot.orderOf z).neZero'
    rw [hnk, Nat.mul_comm]
    exact (isRoot_cyclotomic_prime_pow_mul_iff_of_charP
      (R := R) (p := q) (k := k)).mpr (IsPrimitiveRoot.orderOf z)

/-- Away from the characteristic in the degree, the root has exactly that
degree as multiplicative order. -/
theorem isRoot_cyclotomic_iff_orderOf_of_not_dvd
    {R : Type*} [CommRing R] [IsDomain R] {q : ℕ} [Fact q.Prime]
    [CharP R q] {n : ℕ} (hqn : ¬q ∣ n) (z : R) :
    (cyclotomic n R).IsRoot z ↔ orderOf z = n := by
  let : NeZero (n : R) := NeZero.of_not_dvd R (p := q) hqn
  rw [isRoot_cyclotomic_iff, IsPrimitiveRoot.iff_orderOf]

/-- One prime-characteristic inflation preserves the cyclotomic root set. -/
theorem isRoot_cyclotomic_mul_prime_iff
    {R : Type*} [CommRing R] [IsDomain R] {q : ℕ} [hq : Fact q.Prime]
    [CharP R q] (n : ℕ) (z : R) :
    (cyclotomic (n * q) R).IsRoot z ↔ (cyclotomic n R).IsRoot z := by
  by_cases hqn : q ∣ n
  · rw [cyclotomic_mul_prime_dvd_eq_pow R hqn, IsRoot.def, IsRoot.def, eval_pow]
    exact pow_eq_zero_iff hq.out.ne_zero
  · rw [cyclotomic_mul_prime_eq_pow_of_not_dvd R hqn,
      IsRoot.def, IsRoot.def, eval_pow]
    exact pow_eq_zero_iff (Nat.sub_ne_zero_of_lt hq.out.one_lt)

/-- Every further prime-power inflation preserves the cyclotomic root set. -/
theorem isRoot_cyclotomic_mul_prime_pow_iff
    {R : Type*} [CommRing R] [IsDomain R] {q : ℕ} [Fact q.Prime]
    [CharP R q] (n k : ℕ) (z : R) :
    (cyclotomic (n * q ^ k) R).IsRoot z ↔ (cyclotomic n R).IsRoot z := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, ← Nat.mul_assoc, isRoot_cyclotomic_mul_prime_iff, ih]

/-- Integer cyclotomic-value divisibility is exactly a root after reduction
modulo the prime. -/
theorem prime_dvd_cyclotomicEval_iff_isRoot
    {q : ℕ} [Fact q.Prime] (n : ℕ) (a : ℤ) :
    (q : ℤ) ∣ DkMath.Lib.NumberTheory.cyclotomicEval n a ↔
      (cyclotomic n (ZMod q)).IsRoot (a : ZMod q) := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp only [DkMath.Lib.NumberTheory.cyclotomicEval,
    Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic, IsRoot.def]
  change (Int.castRingHom (ZMod q)) (eval a (cyclotomic n ℤ)) = 0 ↔ _
  rw [← Polynomial.eval₂_at_apply, Polynomial.eval₂_eq_eval_map,
    Polynomial.map_cyclotomic]
  rfl

/-- Complete ordinary integer-evaluation address law.  There is no additional
exception at the prime two. -/
theorem prime_dvd_cyclotomicEval_iff_prime_pow_mul_orderOf
    {q : ℕ} [Fact q.Prime] {n : ℕ} (hn : 0 < n) (a : ℤ) :
    (q : ℤ) ∣ DkMath.Lib.NumberTheory.cyclotomicEval n a ↔
      ∃ k : ℕ, n = orderOf (a : ZMod q) * q ^ k := by
  rw [prime_dvd_cyclotomicEval_iff_isRoot,
    isRoot_cyclotomic_iff_prime_pow_mul_orderOf hn]

/-- An ordinary cyclotomic evaluation at a degree not divisible by the prime
is divisible by that prime exactly when the degree is the modular order. -/
theorem prime_dvd_cyclotomicEval_iff_orderOf_of_not_dvd
    {q : ℕ} [Fact q.Prime] {n : ℕ} (hqn : ¬q ∣ n) (a : ℤ) :
    (q : ℤ) ∣ DkMath.Lib.NumberTheory.cyclotomicEval n a ↔
      orderOf (a : ZMod q) = n := by
  rw [prime_dvd_cyclotomicEval_iff_isRoot,
    isRoot_cyclotomic_iff_orderOf_of_not_dvd hqn]

/-- Divisibility of an integer cyclotomic value is unchanged along the
prime-power degree inflation.  This concerns divisibility, not valuation. -/
theorem prime_dvd_cyclotomicEval_mul_prime_pow_iff
    {q : ℕ} [Fact q.Prime] (n k : ℕ) (a : ℤ) :
    (q : ℤ) ∣ DkMath.Lib.NumberTheory.cyclotomicEval (n * q ^ k) a ↔
      (q : ℤ) ∣ DkMath.Lib.NumberTheory.cyclotomicEval n a := by
  rw [prime_dvd_cyclotomicEval_iff_isRoot,
    prime_dvd_cyclotomicEval_iff_isRoot,
    isRoot_cyclotomic_mul_prime_pow_iff]

end DkMath.NumberTheory.GapFocusing
