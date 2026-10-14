/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.CenteredFoldSupportNorm
import DkMath.NumberTheory.PrimorialUniverse.FinitePrimeSynchronization
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.GCD.BigOperators

#print "file: DkMath.NumberTheory.Legendre.CenteredFoldGcdAggregate"

/-! Exact odd-product, visible norm and common-divisor multiplicity aggregates. -/
namespace DkMath.NumberTheory.Legendre
open DkMath.NumberTheory.Primitive DkMath.NumberTheory.PrimorialUniverse
open scoped BigOperators

/-- Reuse the existing double factorial, with an empty product at zero. -/
abbrev centeredOddGapProduct (n : ℕ) : ℕ := Nat.doubleFactorial (2 * n - 1)

@[simp] theorem centeredOddGapProduct_zero : centeredOddGapProduct 0 = 1 := rfl

theorem centeredOddGapProduct_pos (n : ℕ) : 0 < centeredOddGapProduct n :=
  Nat.doubleFactorial_pos _

theorem centeredOddGapProduct_succ (n : ℕ) :
    centeredOddGapProduct (n + 1) = centeredOddGapProduct n * (2 * n + 1) := by
  cases n with
  | zero => rfl
  | succ n =>
    change Nat.doubleFactorial (2 * (n + 1 + 1) - 1) =
      Nat.doubleFactorial (2 * (n + 1) - 1) * (2 * (n + 1) + 1)
    have he : 2 * (n + 1 + 1) - 1 = (2 * (n + 1) - 1) + 2 := by omega
    rw [he, Nat.doubleFactorial_add_two]
    have hs : 2 * (n + 1) - 1 + 2 = 2 * (n + 1) + 1 := by omega
    rw [hs, Nat.mul_comm]

theorem centeredOddGapProduct_eq_prod (n : ℕ) :
    centeredOddGapProduct n = ∏ j ∈ Finset.range n, (2 * j + 1) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [centeredOddGapProduct_succ, Finset.prod_range_succ, ih]

theorem centeredOddGapProduct_eq_internalGaps_prod (n : ℕ) :
    centeredOddGapProduct n = (centeredInternalGaps n).prod id := by
  rw [centeredInternalGaps, Finset.prod_image]
  · exact centeredOddGapProduct_eq_prod n
  · intro a _ b _ he
    exact DkMath.Gnomon.oddGnomon_injective he

/-- Every odd prime below the width occurs literally as an internal gap. -/
theorem prime_dvd_centeredOddGapProduct_iff {n p : ℕ} (hp : p.Prime) :
    p ∣ centeredOddGapProduct n ↔ p ≠ 2 ∧ p < 2 * n := by
  rw [centeredOddGapProduct_eq_prod, hp.prime.dvd_finsetProd_iff]
  constructor
  · rintro ⟨j, hj, hd⟩
    have hj := Finset.mem_range.mp hj
    refine ⟨?_, ?_⟩
    · rintro rfl
      exact (DkMath.Gnomon.oddGnomon_odd j).not_two_dvd_nat hd
    · have hle := Nat.le_of_dvd (by omega : 0 < 2 * j + 1) hd
      omega
  · rintro ⟨hp2, hpn⟩
    obtain ⟨j, he⟩ := hp.odd_of_ne_two hp2
    refine ⟨j, Finset.mem_range.mpr (by omega), ?_⟩
    rw [← he]

/-- The existing prime universe, filtered to its odd part; no second primorial API. -/
theorem centeredOddGapProduct_primeFactors (n : ℕ) :
    (centeredOddGapProduct n).primeFactors =
      (primeScalesUpTo (2 * n - 1)).erase 2 := by
  ext p
  rw [Nat.mem_primeFactors, Finset.mem_erase, mem_primeScalesUpTo]
  have hne := (centeredOddGapProduct_pos n).ne'
  constructor
  · rintro ⟨hp, hd, _⟩
    obtain ⟨hp2, hpn⟩ := (prime_dvd_centeredOddGapProduct_iff hp).mp hd
    exact ⟨hp2, hp, by omega⟩
  · rintro ⟨hp2, hp, hpn⟩
    have hn : 0 < n := by have := hp.two_le; omega
    exact ⟨hp, (prime_dvd_centeredOddGapProduct_iff hp).mpr ⟨hp2, by omega⟩, hne⟩

theorem centeredOddGapProduct_radical_eq_primorial (n : ℕ) :
    (centeredOddGapProduct n).primeFactors.prod id =
      finitePrimeBasisProduct ((primeScalesUpTo (2 * n - 1)).erase 2) := by
  rw [centeredOddGapProduct_primeFactors]
  rfl

/-- Exact visible norm divisor, retaining capped prime-power multiplicities. -/
def centeredNormGapGcd (n : ℕ) : ℕ := Nat.gcd (centeredFoldNorm n) (centeredOddGapProduct n)

theorem centeredNormGapGcd_pos (n : ℕ) : 0 < centeredNormGapGcd n :=
  Nat.gcd_pos_of_pos_left _ (centeredFoldNorm_pos n)

theorem centeredNormGapGcd_dvd_norm (n : ℕ) : centeredNormGapGcd n ∣ centeredFoldNorm n :=
  Nat.gcd_dvd_left _ _

theorem prime_dvd_centeredNormGapGcd_iff {n p : ℕ} (hp : p.Prime) :
    p ∣ centeredNormGapGcd n ↔ p ∣ centeredFoldNorm n ∧ p ≠ 2 ∧ p < 2 * n := by
  rw [centeredNormGapGcd, Nat.dvd_gcd_iff, prime_dvd_centeredOddGapProduct_iff hp]

/-- Exact prime support union, including fresh primes above n. -/
theorem prime_dvd_centeredNormGapGcd_iff_exists_pair {n p : ℕ} (hp : p.Prime) :
    p ∣ centeredNormGapGcd n ↔ ∃ j < n,
      p ∣ Nat.gcd (n ^ 2 + centeredLeftOffset n j) (n ^ 2 + centeredRightOffset n j) := by
  rw [centeredNormGapGcd, Nat.dvd_gcd_iff, centeredOddGapProduct_eq_prod,
    hp.prime.dvd_finsetProd_iff]
  constructor
  · rintro ⟨hn, j, hj, hg⟩
    exact ⟨j, Finset.mem_range.mp hj, by
      rw [centeredPair_gcd_eq_norm_gap (Finset.mem_range.mp hj)]
      exact Nat.dvd_gcd hn hg⟩
  · rintro ⟨j, hj, hd⟩
    rw [centeredPair_gcd_eq_norm_gap hj, Nat.dvd_gcd_iff] at hd
    exact ⟨hd.1, j, Finset.mem_range.mpr hj, hd.2⟩

theorem old_prime_dvd_centeredNormGapGcd_iff {n p : ℕ} (hp : p.Prime) :
    p ≤ n ∧ p ∣ centeredNormGapGcd n ↔ (centeredCommonSupportIndices n p).Nonempty := by
  classical
  rw [prime_dvd_centeredNormGapGcd_iff_exists_pair hp]
  constructor
  · rintro ⟨hpn, j, hj, hd⟩
    rw [centeredPair_gcd_eq_norm_gap hj, Nat.dvd_gcd_iff] at hd
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj,
      (mem_common_centered_support_iff_norm_and_gap hj).mpr ⟨hp, hpn, hd.1, hd.2⟩⟩⟩
  · rintro ⟨j, hj⟩
    obtain ⟨hj, hs⟩ := Finset.mem_filter.mp hj
    have hj := Finset.mem_range.mp hj
    have h := (mem_common_centered_support_iff_norm_and_gap hj).mp hs
    exact ⟨h.2.1, j, hj, by rw [centeredPair_gcd_eq_norm_gap hj]; exact Nat.dvd_gcd h.2.2.1 h.2.2.2⟩

/-- A visible fresh prime is a complete-point divisor but is outside the old support basis. -/
theorem fresh_prime_centered_pair_packet {n p : ℕ} (hp : p.Prime)
    (hd : p ∣ centeredNormGapGcd n) (hf : n < p) :
    ∃ j < n,
      p ∣ Nat.gcd (n ^ 2 + centeredLeftOffset n j) (n ^ 2 + centeredRightOffset n j) ∧
      p ∉ squareOffsetPrimeSupport n (centeredLeftOffset n j) ∧
      p ∉ squareOffsetPrimeSupport n (centeredRightOffset n j) ∧ p % 4 = 1 ∧ p < 2 * n := by
  obtain ⟨j, hj, hg⟩ := (prime_dvd_centeredNormGapGcd_iff_exists_pair hp).mp hd
  refine ⟨j, hj, hg, ?_, ?_, prime_dvd_centeredPair_gcd_mod_four hj hp hg,
    prime_dvd_centeredPair_gcd_lt_twice hj hg⟩
  · intro h; exact (not_le_of_gt hf) (mem_squareOffsetPrimeSupport.mp h).2.1
  · intro h; exact (not_le_of_gt hf) (mem_squareOffsetPrimeSupport.mp h).2.1

/-- Positive anchors have a finite exact composite detector; n=0 is excluded. -/
theorem centeredFoldNorm_prime_iff_normGapGcd_eq_one {n : ℕ} (hn : 0 < n) :
    (centeredFoldNorm n).Prime ↔ centeredNormGapGcd n = 1 := by
  have hge : 2 * n ≤ centeredFoldNorm n := by unfold centeredFoldNorm; nlinarith
  constructor
  · intro hp
    have hc : Nat.Coprime (centeredFoldNorm n) (centeredOddGapProduct n) := by
      apply hp.coprime_iff_not_dvd.mpr
      intro hd
      exact (not_lt_of_ge hge) ((prime_dvd_centeredOddGapProduct_iff hp).mp hd).2
    exact hc
  · intro he
    by_cases hn1 : n = 1
    · subst n; norm_num [centeredFoldNorm]
    by_contra hnp
    have hn2 : 2 ≤ n := by omega
    have hne : centeredFoldNorm n ≠ 1 := by unfold centeredFoldNorm; nlinarith
    have hp := Nat.minFac_prime hne
    have hd := Nat.minFac_dvd (centeredFoldNorm n)
    have hsq := Nat.minFac_sq_le_self (centeredFoldNorm_pos n) hnp
    have hmul := Nat.mul_le_mul_left n hn2
    have hnorm : centeredFoldNorm n < (2 * n) ^ 2 := by unfold centeredFoldNorm; nlinarith
    have hlt : (centeredFoldNorm n).minFac < 2 * n := by nlinarith
    have hg := (prime_dvd_centeredNormGapGcd_iff hp).mpr
      ⟨hd, prime_dvd_centeredFoldNorm_ne_two hd, hlt⟩
    rw [he] at hg
    exact hp.not_dvd_one hg

theorem centeredNormGapGcd_eq_one_iff_all_pairs (n : ℕ) :
    centeredNormGapGcd n = 1 ↔ ∀ j < n,
      Nat.gcd (n ^ 2 + centeredLeftOffset n j) (n ^ 2 + centeredRightOffset n j) = 1 := by
  change Nat.Coprime (centeredFoldNorm n) (centeredOddGapProduct n) ↔ _
  rw [centeredOddGapProduct_eq_prod, Nat.coprime_prod_right_iff]
  simp only [Finset.mem_range, Nat.Coprime]
  constructor
  · intro h j hj; rw [centeredPair_gcd_eq_norm_gap hj]; exact h j hj
  · intro h j hj; rw [← centeredPair_gcd_eq_norm_gap hj]; exact h j hj

theorem centeredFoldNorm_prime_iff_all_pairs {n : ℕ} (hn : 0 < n) :
    (centeredFoldNorm n).Prime ↔ ∀ j < n,
      Nat.gcd (n ^ 2 + centeredLeftOffset n j) (n ^ 2 + centeredRightOffset n j) = 1 := by
  rw [centeredFoldNorm_prime_iff_normGapGcd_eq_one hn, centeredNormGapGcd_eq_one_iff_all_pairs]

/-- Multiplicity across seats, distinct from the gcd of the norm and the whole gap product. -/
def centeredFoldGcdProduct (n : ℕ) : ℕ :=
  ∏ j ∈ Finset.range n,
    Nat.gcd (n ^ 2 + centeredLeftOffset n j) (n ^ 2 + centeredRightOffset n j)

theorem centeredFoldGcdProduct_eq_norm_gaps (n : ℕ) :
    centeredFoldGcdProduct n = ∏ j ∈ Finset.range n, Nat.gcd (centeredFoldNorm n) (2 * j + 1) := by
  apply Finset.prod_congr rfl
  intro j hj
  exact centeredPair_gcd_eq_norm_gap (Finset.mem_range.mp hj)

theorem centeredFoldGcdProduct_pos (n : ℕ) : 0 < centeredFoldGcdProduct n := by
  rw [centeredFoldGcdProduct_eq_norm_gaps]
  exact Finset.prod_pos fun _ _ => Nat.gcd_pos_of_pos_left _ (centeredFoldNorm_pos n)

theorem centeredFoldGcdProduct_dvd_norm_pow (n : ℕ) :
    centeredFoldGcdProduct n ∣ (centeredFoldNorm n) ^ n := by
  rw [centeredFoldGcdProduct_eq_norm_gaps]
  have h := Finset.prod_dvd_prod_of_dvd
    (fun j => Nat.gcd (centeredFoldNorm n) (2 * j + 1)) (fun _ => centeredFoldNorm n)
    (s := Finset.range n) (fun _ _ => Nat.gcd_dvd_left _ _)
  simpa using h

theorem centeredFoldGcdProduct_dvd_oddGapProduct (n : ℕ) :
    centeredFoldGcdProduct n ∣ centeredOddGapProduct n := by
  rw [centeredFoldGcdProduct_eq_norm_gaps, centeredOddGapProduct_eq_prod]
  exact Finset.prod_dvd_prod_of_dvd _ _ (fun _ _ => Nat.gcd_dvd_right _ _)

/-- Factorization coordinates hold for every p, and preserve capped multiplicities. -/
theorem centeredFoldGcdProduct_factorization (n p : ℕ) :
    (centeredFoldGcdProduct n).factorization p =
      ∑ j ∈ Finset.range n, min ((centeredFoldNorm n).factorization p) ((2 * j + 1).factorization p) := by
  rw [centeredFoldGcdProduct_eq_norm_gaps,
    Nat.factorization_prod_apply (fun _ _ => (Nat.gcd_pos_of_pos_left _ (centeredFoldNorm_pos n)).ne')]
  apply Finset.sum_congr rfl
  intro j _
  rw [Nat.factorization_gcd (centeredFoldNorm_pos n).ne' (by omega : 2 * j + 1 ≠ 0)]
  rfl

theorem centeredNormGapGcd_factorization (n p : ℕ) :
    (centeredNormGapGcd n).factorization p =
      min ((centeredFoldNorm n).factorization p) ((centeredOddGapProduct n).factorization p) := by
  rw [centeredNormGapGcd, Nat.factorization_gcd (centeredFoldNorm_pos n).ne'
    (centeredOddGapProduct_pos n).ne']
  rfl

theorem centeredFoldGcdProduct_padicVal {n p : ℕ} (hp : p.Prime) :
    padicValNat p (centeredFoldGcdProduct n) =
      ∑ j ∈ Finset.range n, min (padicValNat p (centeredFoldNorm n)) (padicValNat p (2 * j + 1)) := by
  simpa only [Nat.factorization_def _ hp] using centeredFoldGcdProduct_factorization n p

theorem centeredNormGapGcd_padicVal {n p : ℕ} (hp : p.Prime) :
    padicValNat p (centeredNormGapGcd n) =
      min (padicValNat p (centeredFoldNorm n)) (padicValNat p (centeredOddGapProduct n)) := by
  simpa only [Nat.factorization_def _ hp] using centeredNormGapGcd_factorization n p

theorem centeredOddGapProduct_factorization (n p : ℕ) :
    (centeredOddGapProduct n).factorization p = ∑ j ∈ Finset.range n, (2 * j + 1).factorization p := by
  rw [centeredOddGapProduct_eq_prod]
  exact Nat.factorization_prod_apply (fun _ _ => by omega)

theorem centeredOddGapProduct_padicVal {n p : ℕ} (hp : p.Prime) :
    padicValNat p (centeredOddGapProduct n) = ∑ j ∈ Finset.range n, padicValNat p (2 * j + 1) := by
  simpa only [Nat.factorization_def _ hp] using centeredOddGapProduct_factorization n p

/-- Existing factorial/double-factorial splitting, including the empty product. -/
theorem factorial_twice_eq_even_mul_centeredOddGapProduct (n : ℕ) :
    (2 * n).factorial = (2 ^ n * n.factorial) * centeredOddGapProduct n := by
  cases n with
  | zero => rfl
  | succ n =>
    have he : (2 * (n + 1) - 1) + 1 = 2 * (n + 1) := by omega
    have h := Nat.factorial_eq_mul_doubleFactorial (2 * (n + 1) - 1)
    rw [he, Nat.doubleFactorial_two_mul] at h
    exact h

theorem centeredOddGapProduct_factorization_factorial (n p : ℕ) :
    (centeredOddGapProduct n).factorization p = (2 * n).factorial.factorization p -
      (n * (2 : ℕ).factorization p + n.factorial.factorization p) := by
  have he := congrArg (fun a : ℕ => a.factorization p)
    (factorial_twice_eq_even_mul_centeredOddGapProduct n)
  rw [Nat.factorization_mul (mul_ne_zero (pow_ne_zero _ (by decide)) (Nat.factorial_ne_zero _))
    (centeredOddGapProduct_pos n).ne',
    Nat.factorization_mul (pow_ne_zero _ (by decide)) (Nat.factorial_ne_zero _),
    Nat.factorization_pow] at he
  simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at he
  omega

theorem centeredNormGapGcd_succ_coprime (n : ℕ) :
    Nat.Coprime (centeredNormGapGcd n) (centeredNormGapGcd (n + 1)) :=
  ((centeredFoldNorm_succ_coprime n).coprime_dvd_left (centeredNormGapGcd_dvd_norm n)).coprime_dvd_right
    (centeredNormGapGcd_dvd_norm (n + 1))

theorem centeredFoldGcdProduct_succ_coprime (n : ℕ) :
    Nat.Coprime (centeredFoldGcdProduct n) (centeredFoldGcdProduct (n + 1)) :=
  (((centeredFoldNorm_succ_coprime n).pow n (n + 1)).coprime_dvd_left
    (centeredFoldGcdProduct_dvd_norm_pow n)).coprime_dvd_right
    (centeredFoldGcdProduct_dvd_norm_pow (n + 1))


theorem centeredOddGapProduct_padicVal_factorial {n p : ℕ} (hp : p.Prime) :
    padicValNat p (centeredOddGapProduct n) = padicValNat p (2 * n).factorial -
      (n * padicValNat p 2 + padicValNat p n.factorial) := by
  simpa only [Nat.factorization_def _ hp] using centeredOddGapProduct_factorization_factorial n p

theorem centeredOddGapProduct_padicVal_factorial_odd {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    padicValNat p (centeredOddGapProduct n) =
      padicValNat p (2 * n).factorial - padicValNat p n.factorial := by
  have h2 : padicValNat p 2 = 0 := by
    rw [← Nat.factorization_def _ hp, Nat.prime_two.factorization]
    simp [hp2.symm]
  rw [centeredOddGapProduct_padicVal_factorial hp, h2, Nat.mul_zero, Nat.zero_add]


theorem centeredFoldGcdProduct_eq_one_iff_all_pairs (n : ℕ) :
    centeredFoldGcdProduct n = 1 ↔ ∀ j < n,
      Nat.gcd (n ^ 2 + centeredLeftOffset n j) (n ^ 2 + centeredRightOffset n j) = 1 := by
  constructor
  · intro he j hj
    apply Nat.eq_one_of_dvd_one
    rw [← he]
    exact Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr hj)
  · intro h
    exact Finset.prod_eq_one (fun j hj => h j (Finset.mem_range.mp hj))

theorem centeredFoldGcdProduct_eq_one_iff_normGapGcd_eq_one (n : ℕ) :
    centeredFoldGcdProduct n = 1 ↔ centeredNormGapGcd n = 1 := by
  rw [centeredFoldGcdProduct_eq_one_iff_all_pairs, centeredNormGapGcd_eq_one_iff_all_pairs]

theorem prime_dvd_centeredFoldGcdProduct_iff {n p : ℕ} (hp : p.Prime) :
    p ∣ centeredFoldGcdProduct n ↔ p ∣ centeredNormGapGcd n := by
  rw [centeredFoldGcdProduct, hp.prime.dvd_finsetProd_iff,
    prime_dvd_centeredNormGapGcd_iff_exists_pair hp]
  simp only [Finset.mem_range]

end DkMath.NumberTheory.Legendre
