/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.GapFocusing.HomogeneousAddress

#print "file: DkMath.NumberTheory.GapFocusing.CyclotomicBoundary"

namespace DkMath.NumberTheory.GapFocusing

open Polynomial DkMath.CFBRC

/-- At a zero second coordinate, homogenization extracts the coefficient
at the chosen total degree. -/
theorem eval_homogenize_zero_second {R : Type*} [CommSemiring R]
    (p : R[X]) (n : ℕ) (a : R) :
    MvPolynomial.eval ![a, 0] (p.homogenize n) = p.coeff n * a ^ n := by
  simp only [homogenize, MvPolynomial.eval_sum,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have hterm (k : ℕ) :
      MvPolynomial.eval ![a, 0]
        (MvPolynomial.monomial (fun₀ | 0 => k | 1 => n - k) (p.coeff k)) =
      p.coeff k * (a ^ k * (0 : R) ^ (n - k)) := by
    rw [MvPolynomial.eval_monomial, Finsupp.prod_fintype, Fin.prod_univ_two] <;> simp
  simp_rw [hterm]
  rw [Finset.sum_eq_single n]
  · simp
  · intro k hk hkn
    have hk' : k < n := by
      have hk' := Finset.mem_range.mp hk
      omega
    simp [zero_pow (by omega : n - k ≠ 0)]
  · simp

/-- The zero anchor of the existing homogeneous cyclotomic evaluation is
the power determined by its degree, over every commutative ring. -/
theorem cyclotomicShiftedEval_zero_anchor {R : Type*} [CommRing R]
    (n : ℕ) (a : R) :
    cyclotomicShiftedEval n a 0 = a ^ n.totient := by
  unfold cyclotomicShiftedEval
  simp only [add_zero]
  rw [eval_homogenize_zero_second, coeff_map,
    (cyclotomic.monic n ℤ).coeff_natDegree, map_one, one_mul,
    natDegree_cyclotomic]

/-- If the denominator vanishes modulo the prime, a positive homogeneous
cyclotomic value vanishes exactly when the numerator also vanishes. -/
theorem dvd_cyclotomicShiftedEval_iff_dvd_first_of_dvd_second
    (q : ℕ) [Fact q.Prime] {n : ℕ} (hn : 0 < n) (a b : ℤ)
    (hb : (q : ℤ) ∣ b) :
    (q : ℤ) ∣ cyclotomicShiftedEval n (a - b) b ↔ (q : ℤ) ∣ a := by
  have hb0 : (b : ZMod q) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd b q).mpr hb
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd,
    ← ZMod.intCast_zmod_eq_zero_iff_dvd a q]
  change (Int.castRingHom (ZMod q)) (cyclotomicShiftedEval n (a - b) b) = 0 ↔ _
  rw [map_cyclotomicShiftedEval]
  change cyclotomicShiftedEval n ((a - b : ℤ) : ZMod q) (b : ZMod q) = 0 ↔ _
  rw [Int.cast_sub, hb0, sub_zero, cyclotomicShiftedEval_zero_anchor]
  exact pow_eq_zero_iff (Nat.totient_pos.mpr hn).ne'

/-- The denominator-vanishing address set is the entire nontrivial degree
set if both coordinates vanish, and is empty otherwise. -/
theorem primeLayerAddresses_of_dvd_second
    (q : ℕ) [Fact q.Prime] (a b : ℤ) (hb : (q : ℤ) ∣ b) :
    primeLayerAddresses q a b = {n | 1 < n ∧ (q : ℤ) ∣ a} := by
  ext n
  change (1 < n ∧ (q : ℤ) ∣ cyclotomicShiftedEval n (a - b) b) ↔
    (1 < n ∧ (q : ℤ) ∣ a)
  by_cases hn : 1 < n
  · rw [dvd_cyclotomicShiftedEval_iff_dvd_first_of_dvd_second q (by omega) a b hb]
  · simp [hn]

/-- A prime dividing only the second coordinate has no nontrivial address. -/
theorem primeLayerAddresses_eq_empty_of_dvd_second
    (q : ℕ) [Fact q.Prime] (a b : ℤ)
    (ha : ¬(q : ℤ) ∣ a) (hb : (q : ℤ) ∣ b) :
    primeLayerAddresses q a b = ∅ := by
  rw [primeLayerAddresses_of_dvd_second q a b hb]
  ext n
  simp [ha]

/-- A common coordinate prime divides every nontrivial homogeneous layer.
This is the coordinate ramification boundary outside the order ray. -/
theorem primeLayerAddresses_eq_nontrivial_of_dvd_coordinates
    (q : ℕ) [Fact q.Prime] (a b : ℤ)
    (ha : (q : ℤ) ∣ a) (hb : (q : ℤ) ∣ b) :
    primeLayerAddresses q a b = {n | 1 < n} := by
  rw [primeLayerAddresses_of_dvd_second q a b hb]
  ext n
  simp [ha]

/-- A prime dividing only the first coordinate has no nontrivial address. -/
theorem primeLayerAddresses_eq_empty_of_dvd_first
    (q : ℕ) [Fact q.Prime] (a b : ℤ)
    (ha : (q : ℤ) ∣ a) (hb : ¬(q : ℤ) ∣ b) :
    primeLayerAddresses q a b = ∅ := by
  have ha0 : (a : ZMod q) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd a q).mpr ha
  ext n
  rw [Set.mem_empty_iff_false]
  constructor
  · intro hn
    obtain ⟨hn1, k, hnk⟩ := (mem_primeLayerAddresses_iff q a b hb n).mp hn
    rw [ha0, zero_mul, orderOf_zero, zero_mul] at hnk
    omega
  · exact False.elim

end DkMath.NumberTheory.GapFocusing
