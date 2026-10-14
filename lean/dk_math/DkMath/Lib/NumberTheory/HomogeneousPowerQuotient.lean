/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Algebra.DiffPow

#print "file: DkMath.Lib.NumberTheory.HomogeneousPowerQuotient"

namespace DkMath.Lib.NumberTheory

open scoped BigOperators
open Finset
open DkMath.Algebra.DiffPow

/-! The existing `DkMath.Algebra.DiffPow.diffPowSum` is the canonical
homogeneous power quotient. This alias gives the neutral NumberTheory layer a
stable name without introducing a second definition. -/

abbrev homogeneousPowerQuotient {R : Type*} [CommRing R]
    (x y : R) (n : ℕ) : R :=
  diffPowSum x y n

theorem pow_sub_pow_eq_gap_mul_homogeneous
    {R : Type*} [CommRing R] (x y : R) (n : ℕ) :
    x ^ n - y ^ n =
      (x - y) * homogeneousPowerQuotient x y n :=
  DkMath.Algebra.DiffPow.pow_sub_pow_factor x y n

/-- The homogeneous quotient is congruent to its last diagonal term modulo
the root gap. The exponent is arbitrary; no primality assumption is used. -/
theorem gap_dvd_homogeneous_sub_natCast_mul
    {R : Type*} [CommRing R] (x y : R) (n : ℕ) :
    x - y ∣
      homogeneousPowerQuotient x y n - (n : R) * y ^ (n - 1) := by
  rw [show homogeneousPowerQuotient x y n = diffPowSum x y n by rfl,
    diffPowSum_sub_const_mul]
  apply Finset.dvd_sum
  intro i hi
  have hpow : x ^ (n - 1 - i) - y ^ (n - 1 - i) =
      (x - y) * diffPowSum x y (n - 1 - i) :=
    DkMath.Algebra.DiffPow.pow_sub_pow_factor x y (n - 1 - i)
  have hle : i ≤ n - 1 := by
    exact Nat.le_pred_of_lt (Finset.mem_range.mp hi)
  have hsplit : n - 1 = (n - 1 - i) + i := by
    omega
  have hy : y ^ (n - 1) = y ^ (n - 1 - i) * y ^ i := by
    calc
      y ^ (n - 1) = y ^ ((n - 1 - i) + i) := congrArg (fun k => y ^ k) hsplit
      _ = y ^ (n - 1 - i) * y ^ i := by rw [pow_add]
  have hterm :
      x ^ (n - 1 - i) * y ^ i - y ^ (n - 1) =
        y ^ i * (x ^ (n - 1 - i) - y ^ (n - 1 - i)) := by
    rw [hy]
    ring
  rw [hterm, hpow]
  exact dvd_mul_of_dvd_right
    (dvd_mul_of_dvd_left (dvd_refl (x - y)) _) _

/-- A prime element common to the gap and the homogeneous quotient must divide
the exponent scalar, provided it does not divide the base y. -/
theorem prime_dvd_exponent_cast_of_dvd_gap_and_homogeneous
    {R : Type*} [CommRing R]
    (q x y : R) (n : ℕ)
    (hq : Prime q)
    (hgap : q ∣ x - y)
    (hquot : q ∣ homogeneousPowerQuotient x y n)
    (hy : ¬q ∣ y) :
    q ∣ (n : R) := by
  have hcong := gap_dvd_homogeneous_sub_natCast_mul x y n
  have hsub : q ∣
      homogeneousPowerQuotient x y n - (n : R) * y ^ (n - 1) :=
    hgap.trans hcong
  have hscalar : q ∣ (n : R) * y ^ (n - 1) := by
    have h := dvd_sub hquot hsub
    simpa [sub_sub_cancel] using h
  exact (hq.dvd_mul.mp hscalar).resolve_right
    (fun h => hy (hq.dvd_of_dvd_pow h))

/-- Coprime factors give the nondivisibility hypothesis needed by the prime
localization theorem. Thus common prime support is confined to the scalar
exponent. -/
theorem prime_dvd_exponent_cast_of_coprime_gap_and_homogeneous
    {R : Type*} [CommRing R]
    (q x y : R) (n : ℕ)
    (hq : Prime q)
    (hxy : IsCoprime x y)
    (hgap : q ∣ x - y)
    (hquot : q ∣ homogeneousPowerQuotient x y n) :
    q ∣ (n : R) := by
  apply prime_dvd_exponent_cast_of_dvd_gap_and_homogeneous q x y n hq hgap hquot
  intro hy
  have hx : q ∣ x := by
    simpa using dvd_add hgap hy
  exact hq.not_isUnit (hxy.isUnit_of_dvd' hx hy)

end DkMath.Lib.NumberTheory
