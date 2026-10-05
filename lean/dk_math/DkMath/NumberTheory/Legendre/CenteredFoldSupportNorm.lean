/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.CenteredOwnerFold
import Mathlib.NumberTheory.LegendreSymbol.Basic

#print "file: DkMath.NumberTheory.Legendre.CenteredFoldSupportNorm"

/-! Common fold support is controlled by the primitive consecutive-square norm. -/
namespace DkMath.NumberTheory.Legendre
open DkMath.NumberTheory.Primitive

/-- The sum of the two complete fold points, independent of pair index. -/
def centeredFoldNorm (n : ℕ) : ℕ := n ^ 2 + (n + 1) ^ 2

theorem centeredFoldNorm_odd (n : ℕ) : Odd (centeredFoldNorm n) := by
  refine ⟨n * (n + 1), ?_⟩
  unfold centeredFoldNorm
  ring

theorem centeredFoldNorm_eq_point_sum {n j : ℕ} (hj : j < n) :
    centeredFoldNorm n = (n ^ 2 + centeredLeftOffset n j) +
      (n ^ 2 + centeredRightOffset n j) := by
  have hs := centeredFoldPair_sum hj
  have he : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
  unfold centeredFoldNorm
  omega

theorem centeredFoldNorm_eq_twice_left_add_gap {n j : ℕ} (hj : j < n) :
    centeredFoldNorm n = 2 * (n ^ 2 + centeredLeftOffset n j) + (2 * j + 1) := by
  rw [centeredFoldNorm_eq_point_sum hj, centeredPoint_difference hj]
  omega

theorem prime_dvd_centeredFoldNorm_ne_two {n p : ℕ}
    (hd : p ∣ centeredFoldNorm n) : p ≠ 2 := by
  rintro rfl
  exact (centeredFoldNorm_odd n).not_two_dvd_nat hd

/-- The norm and internal gap completely determine common bounded support. -/
theorem mem_common_centered_support_iff_norm_and_gap {n j p : ℕ} (hj : j < n) :
    (p ∈ squareOffsetPrimeSupport n (centeredLeftOffset n j) ∧
      p ∈ squareOffsetPrimeSupport n (centeredRightOffset n j)) ↔
    p.Prime ∧ p ≤ n ∧ p ∣ centeredFoldNorm n ∧ p ∣ 2 * j + 1 := by
  rw [mem_common_squareOffsetPrimeSupport_iff hj]
  constructor
  · rintro ⟨hp, hpn, hl, hg⟩
    have hs := (centeredCommonDivisor_iff hj).mpr ⟨hl, hg⟩
    exact ⟨hp, hpn, by rw [centeredFoldNorm_eq_point_sum hj]; exact dvd_add hs.1 hs.2, hg⟩
  · rintro ⟨hp, hpn, hd, hg⟩
    have hsum : p ∣ (2 * j + 1) + 2 * (n ^ 2 + centeredLeftOffset n j) := by
      rw [Nat.add_comm, ← centeredFoldNorm_eq_twice_left_add_gap hj]
      exact hd
    have htw := (Nat.dvd_add_iff_right hg).mpr hsum
    have hl : p ∣ n ^ 2 + centeredLeftOffset n j := by
      rcases hp.dvd_mul.mp htw with h2 | hl
      · exact False.elim (prime_dvd_centeredFoldNorm_ne_two hd
          ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2))
      · exact hl
    exact ⟨hp, hpn, hl, hg⟩

theorem prime_dvd_centeredFoldNorm_not_dvd_succ {n p : ℕ} (hp : p.Prime)
    (hd : p ∣ centeredFoldNorm n) : ¬p ∣ n + 1 := by
  intro hs
  have hsq : p ∣ (n + 1) ^ 2 := dvd_pow hs (by decide : 2 ≠ 0)
  have hn2 : p ∣ n ^ 2 := (Nat.dvd_add_left hsq).mp hd
  have hn : p ∣ n := hp.dvd_of_dvd_pow hn2
  exact hp.not_dvd_one ((Nat.dvd_add_iff_right hn).mpr hs)

/-- The primitive sum of consecutive squares admits only primes 1 mod 4. -/
theorem prime_dvd_centeredFoldNorm_mod_four {n p : ℕ} (hp : p.Prime)
    (hd : p ∣ centeredFoldNorm n) : p % 4 = 1 := by
  let : Fact p.Prime := ⟨hp⟩
  have hsucc : ((n + 1 : ℕ) : ZMod p) ≠ 0 := by
    intro hz
    exact prime_dvd_centeredFoldNorm_not_dvd_succ hp hd
      ((ZMod.natCast_eq_zero_iff (n + 1) p).mp hz)
  have hz : (n : ZMod p) ^ 2 + ((n + 1 : ℕ) : ZMod p) ^ 2 = 0 := by
    have h := (ZMod.natCast_eq_zero_iff (centeredFoldNorm n) p).mpr hd
    simpa [centeredFoldNorm] using h
  have hnot3 := ZMod.mod_four_ne_three_of_sq_eq_neg_sq' hsucc (eq_neg_of_add_eq_zero_left hz)
  have hodd := (hp.mod_two_eq_one_iff_ne_two).mpr (prime_dvd_centeredFoldNorm_ne_two hd)
  omega

theorem common_centered_support_mod_four {n j p : ℕ} (hj : j < n)
    (hl : p ∈ squareOffsetPrimeSupport n (centeredLeftOffset n j))
    (hr : p ∈ squareOffsetPrimeSupport n (centeredRightOffset n j)) : p % 4 = 1 := by
  have h := (mem_common_centered_support_iff_norm_and_gap hj).mp ⟨hl, hr⟩
  exact prime_dvd_centeredFoldNorm_mod_four h.1 h.2.2.1

noncomputable def centeredCommonSupportIndices (n p : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range n).filter (fun j =>
    p ∈ squareOffsetPrimeSupport n (centeredLeftOffset n j) ∧
    p ∈ squareOffsetPrimeSupport n (centeredRightOffset n j))

/-- Actual common-support addresses are either the complete gap capacity or empty. -/
theorem centeredCommonSupportIndices_eq_capacity {n p : ℕ} (hp : p.Prime) :
    centeredCommonSupportIndices n p =
      if p ≤ n ∧ p ∣ centeredFoldNorm n then centeredOwnerGapCapacityIndices n p else ∅ := by
  classical
  ext j
  rw [centeredCommonSupportIndices, Finset.mem_filter, Finset.mem_range]
  by_cases hn : p ≤ n ∧ p ∣ centeredFoldNorm n
  · rw [ite_eq_left hn, mem_centeredOwnerGapCapacityIndices]
    constructor
    · rintro ⟨hj, hs⟩
      exact ⟨hj, ((mem_common_centered_support_iff_norm_and_gap hj).mp hs).2.2.2⟩
    · rintro ⟨hj, hg⟩
      exact ⟨hj, (mem_common_centered_support_iff_norm_and_gap hj).mpr ⟨hp, hn.1, hn.2, hg⟩⟩
  · rw [ite_eq_right hn]
    simp only [Finset.notMem_empty, iff_false]
    rintro ⟨hj, hs⟩
    have h := (mem_common_centered_support_iff_norm_and_gap hj).mp hs
    exact hn ⟨h.2.1, h.2.2.1⟩

theorem centeredCommonSupportIndices_card {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    (centeredCommonSupportIndices n p).card =
      if p ≤ n ∧ p ∣ centeredFoldNorm n then (n + (p - 1) / 2) / p else 0 := by
  classical
  rw [centeredCommonSupportIndices_eq_capacity hp]
  split_ifs <;> simp [centeredOwnerGapCapacityIndices_card hp hp2]

/-- Consecutive fold norms are coprime. This concerns common support, not cover propagation. -/
theorem centeredFoldNorm_succ_coprime (n : ℕ) :
    Nat.Coprime (centeredFoldNorm n) (centeredFoldNorm (n + 1)) := by
  apply Nat.coprime_of_dvd
  intro p hp hd hs
  have he : centeredFoldNorm (n + 1) = centeredFoldNorm n + 4 * (n + 1) := by
    unfold centeredFoldNorm
    ring
  rw [he] at hs
  have hprod := (Nat.dvd_add_iff_right hd).mpr hs
  rcases hp.dvd_mul.mp hprod with h4 | hsucc
  · have h2 : p ∣ 2 := hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by norm_num; exact h4)
    exact prime_dvd_centeredFoldNorm_ne_two hd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
  · exact prime_dvd_centeredFoldNorm_not_dvd_succ hp hd hsucc

/-- No prime is common to a fold pair in each of two consecutive shells, for any pair indices. -/
theorem common_centered_support_no_successor {n j k p : ℕ} (hj : j < n) (hk : k < n + 1)
    (h0 : p ∈ squareOffsetPrimeSupport n (centeredLeftOffset n j) ∧
      p ∈ squareOffsetPrimeSupport n (centeredRightOffset n j)) :
    ¬(p ∈ squareOffsetPrimeSupport (n + 1) (centeredLeftOffset (n + 1) k) ∧
      p ∈ squareOffsetPrimeSupport (n + 1) (centeredRightOffset (n + 1) k)) := by
  intro h1
  have a := (mem_common_centered_support_iff_norm_and_gap hj).mp h0
  have b := (mem_common_centered_support_iff_norm_and_gap hk).mp h1
  have hbad := ((centeredFoldNorm_succ_coprime n).coprime_dvd_left a.2.2.1).eq_one_of_dvd b.2.2.1
  exact a.1.ne_one hbad


/-- Exact gcd, including multiplicity and the fresh-prime branch. -/
theorem centeredPair_gcd_eq_norm_gap {n j : ℕ} (hj : j < n) :
    Nat.gcd (n ^ 2 + centeredLeftOffset n j) (n ^ 2 + centeredRightOffset n j) =
      Nat.gcd (centeredFoldNorm n) (2 * j + 1) := by
  rw [centeredPoint_difference hj, Nat.gcd_self_add_right,
    centeredFoldNorm_eq_twice_left_add_gap hj, Nat.gcd_add_self_left]
  exact ((DkMath.Gnomon.oddGnomon_odd j).coprime_two_left.gcd_mul_left_cancel _).symm

theorem centeredFoldNorm_pos (n : ℕ) : 0 < centeredFoldNorm n := by
  unfold centeredFoldNorm
  positivity

theorem centeredPair_gcd_dvd_norm {n j : ℕ} (hj : j < n) :
    Nat.gcd (n ^ 2 + centeredLeftOffset n j) (n ^ 2 + centeredRightOffset n j) ∣
      centeredFoldNorm n := by
  rw [centeredPair_gcd_eq_norm_gap hj]
  exact Nat.gcd_dvd_left _ _

theorem centeredPair_gcd_dvd_gap {n j : ℕ} (hj : j < n) :
    Nat.gcd (n ^ 2 + centeredLeftOffset n j) (n ^ 2 + centeredRightOffset n j) ∣
      2 * j + 1 := by
  rw [centeredPair_gcd_eq_norm_gap hj]
  exact Nat.gcd_dvd_right _ _

theorem prime_dvd_centeredPair_gcd_mod_four {n j p : ℕ} (hj : j < n) (hp : p.Prime)
    (hd : p ∣ Nat.gcd (n ^ 2 + centeredLeftOffset n j) (n ^ 2 + centeredRightOffset n j)) :
    p % 4 = 1 :=
  prime_dvd_centeredFoldNorm_mod_four hp (dvd_trans hd (centeredPair_gcd_dvd_norm hj))

theorem centeredPair_gcd_odd {n j : ℕ} (hj : j < n) :
    Odd (Nat.gcd (n ^ 2 + centeredLeftOffset n j) (n ^ 2 + centeredRightOffset n j)) := by
  apply Nat.not_even_iff_odd.mp
  intro he
  exact (centeredFoldNorm_odd n).not_two_dvd_nat
    (dvd_trans he.two_dvd (centeredPair_gcd_dvd_norm hj))

theorem prime_dvd_centeredPair_gcd_lt_twice {n j p : ℕ} (hj : j < n)
    (hd : p ∣ Nat.gcd (n ^ 2 + centeredLeftOffset n j) (n ^ 2 + centeredRightOffset n j)) :
    p < 2 * n := by
  have hle := Nat.le_of_dvd (by omega : 0 < 2 * j + 1)
    (dvd_trans hd (centeredPair_gcd_dvd_gap hj))
  omega

/-- Old-support disjointness retains the 1-or-single-fresh-prime alternative. -/
theorem centeredPair_oldSupport_disjoint_iff {n j : ℕ} (hj : j < n) :
    Disjoint (squareOffsetPrimeSupport n (centeredLeftOffset n j))
      (squareOffsetPrimeSupport n (centeredRightOffset n j)) ↔
    Nat.gcd (centeredFoldNorm n) (2 * j + 1) = 1 ∨
      ((Nat.gcd (centeredFoldNorm n) (2 * j + 1)).Prime ∧
        n < Nat.gcd (centeredFoldNorm n) (2 * j + 1)) := by
  have hlt : centeredLeftOffset n j < centeredRightOffset n j := by
    dsimp [centeredLeftOffset, centeredRightOffset]; omega
  simpa [centeredPair_gcd_eq_norm_gap hj] using
    disjoint_squareOffsetPrimeSupport_iff_gcd_eq_one_or_fresh_prime
      (squareOffset_centeredLeftOffset hj) (squareOffset_centeredRightOffset hj) hlt


/-- Fixed cyclotomic shape from the existing prime-power geometric-sum API. -/
theorem centeredFold_cyclotomic_four_shape :
    Polynomial.cyclotomic 4 ℤ = Polynomial.X ^ 2 + 1 := by
  have h := Polynomial.cyclotomic_prime_pow_eq_geom_sum (R := ℤ) (n := 1) Nat.prime_two
  norm_num [Finset.sum_range_succ] at h
  simpa [add_comm] using h

/-- Homogeneous Phi_4 at consecutive coordinates, using the existing shifted evaluator. -/
theorem centeredFoldNorm_eq_cyclotomic_four (n : ℕ) :
    (centeredFoldNorm n : ℤ) = DkMath.CFBRC.cyclotomicShiftedEval 4 (1 : ℤ) n := by
  simp [DkMath.CFBRC.cyclotomicShiftedEval, centeredFold_cyclotomic_four_shape,
    Polynomial.homogenize_add, Polynomial.homogenize_X_pow, centeredFoldNorm]
  ring

/-- Inverse orientation has the same homogeneous norm. -/
theorem centeredFoldNorm_eq_cyclotomic_four_inverse (n : ℕ) :
    (centeredFoldNorm n : ℤ) = DkMath.CFBRC.cyclotomicShiftedEval 4 (-1 : ℤ) ((n + 1 : ℕ) : ℤ) := by
  simp [DkMath.CFBRC.cyclotomicShiftedEval, centeredFold_cyclotomic_four_shape,
    Polynomial.homogenize_add, Polynomial.homogenize_X_pow, centeredFoldNorm]

/-- The ratio n/(n+1) has square -1 in the residue field. -/
theorem prime_dvd_centeredFoldNorm_ratio_sq {n p : ℕ} (hp : p.Prime)
    (hd : p ∣ centeredFoldNorm n) :
    DkMath.NumberTheory.GapFocusing.primeRatio p n ((n + 1 : ℕ) : ℤ) ^ 2 = -1 := by
  let : Fact p.Prime := ⟨hp⟩
  have hb : ((n + 1 : ℕ) : ZMod p) ≠ 0 := by
    intro hz
    exact prime_dvd_centeredFoldNorm_not_dvd_succ hp hd
      ((ZMod.natCast_eq_zero_iff (n + 1) p).mp hz)
  have hz : (n : ZMod p) ^ 2 + ((n + 1 : ℕ) : ZMod p) ^ 2 = 0 := by
    have h := (ZMod.natCast_eq_zero_iff (centeredFoldNorm n) p).mpr hd
    simpa [centeredFoldNorm] using h
  have he : DkMath.NumberTheory.GapFocusing.primeRatio p n ((n + 1 : ℕ) : ℤ) =
      (n : ZMod p) / ((n + 1 : ℕ) : ZMod p) := by
    simp [DkMath.NumberTheory.GapFocusing.primeRatio, div_eq_mul_inv]
  rw [he, div_pow]
  apply (div_eq_iff (pow_ne_zero _ hb)).mpr
  linear_combination hz

/-- Existing primeOrder API supplies the exact order-four address without a field extension. -/
theorem prime_dvd_centeredFoldNorm_order_four {n p : ℕ} (hp : p.Prime)
    (hd : p ∣ centeredFoldNorm n) :
    DkMath.NumberTheory.GapFocusing.primeOrder p n ((n + 1 : ℕ) : ℤ) = 4 := by
  let : Fact p.Prime := ⟨hp⟩
  have hb : ¬(p : ℤ) ∣ ((n + 1 : ℕ) : ℤ) := by
    exact_mod_cast prime_dvd_centeredFoldNorm_not_dvd_succ hp hd
  have hp4 : ¬p ∣ 4 := by
    intro h4
    have h2 := hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by norm_num; exact h4)
    exact prime_dvd_centeredFoldNorm_ne_two hd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
  have h := DkMath.NumberTheory.GapFocusing.dvd_cyclotomicShiftedEval_iff_primeOrder_eq_of_not_dvd
    p 4 n ((n + 1 : ℕ) : ℤ) hb hp4
  have hsub : (n : ℤ) - ((n + 1 : ℕ) : ℤ) = -1 := by omega
  rw [hsub, ← centeredFoldNorm_eq_cyclotomic_four_inverse n, Int.natCast_dvd_natCast] at h
  exact h.mp hd

end DkMath.NumberTheory.Legendre
