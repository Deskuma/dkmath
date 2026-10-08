/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.CenteredFoldGcdAggregate
import DkMathTest.NumberTheory.LegendreCenteredFoldRegression

#print "file: DkMathTest.NumberTheory.LegendreFoldGcdRegression"

namespace DkMathTest.LegendreFoldGcdRegression
open DkMath.NumberTheory.Legendre DkMath.NumberTheory.Primitive

/-- The first gap always gives coprime complete points. -/
theorem gap_one {n : ℕ} (hn : 0 < n) :
    Nat.gcd (n ^ 2 + centeredLeftOffset n 0) (n ^ 2 + centeredRightOffset n 0) = 1 := by
  rw [centeredPair_gcd_eq_norm_gap hn]
  simp

theorem empty_boundary : centeredFoldNorm 0 = 1 ∧ centeredOddGapProduct 0 = 1 ∧
    centeredNormGapGcd 0 = 1 ∧ centeredFoldGcdProduct 0 = 1 ∧ ¬(centeredFoldNorm 0).Prime := by
  decide +kernel

theorem prime_one_two : centeredFoldNorm 1 = 5 ∧ centeredFoldNorm 2 = 13 ∧
    (centeredFoldNorm 1).Prime ∧ (centeredFoldNorm 2).Prime ∧
    centeredNormGapGcd 1 = 1 ∧ centeredNormGapGcd 2 = 1 := by
  decide +kernel

theorem fresh_three : centeredFoldNorm 3 = 25 ∧ centeredNormGapGcd 3 = 5 ∧
    Nat.gcd (3 ^ 2 + centeredLeftOffset 3 2) (3 ^ 2 + centeredRightOffset 3 2) = 5 ∧
    centeredFoldGcdProduct 3 = 5 ∧
    3 < 5 ∧ 5 < 2 * 3 := by
  decide +kernel

theorem old_six : centeredFoldNorm 6 = 85 ∧ centeredNormGapGcd 6 = 5 ∧
    Nat.gcd (6 ^ 2 + centeredLeftOffset 6 2) (6 ^ 2 + centeredRightOffset 6 2) = 5 ∧
    centeredFoldGcdProduct 6 = 5 ∧ 5 ≤ 6 := by
  decide +kernel

theorem repeated_twenty_one : centeredFoldNorm 21 = 925 ∧
    Nat.gcd (21 ^ 2 + centeredLeftOffset 21 12) (21 ^ 2 + centeredRightOffset 21 12) = 25 ∧
    centeredNormGapGcd 21 = 925 ∧ centeredFoldGcdProduct 21 = 115625 := by
  decide +kernel

/-- A gcd above n can still contain an old prime, rather than be a fresh prime. -/
theorem large_gcd_with_old_support :
    21 < Nat.gcd (21 ^ 2 + centeredLeftOffset 21 12) (21 ^ 2 + centeredRightOffset 21 12) ∧
    5 ∈ squareOffsetPrimeSupport 21 (centeredLeftOffset 21 12) ∧
    5 ∈ squareOffsetPrimeSupport 21 (centeredRightOffset 21 12) := by
  refine ⟨by rw [repeated_twenty_one.2.1]; decide, ?_⟩
  rw [mem_squareOffsetPrimeSupport, mem_squareOffsetPrimeSupport]
  norm_num [centeredLeftOffset, centeredRightOffset]

/-- Smallest diagnostic failure of equality between the two aggregates. -/
theorem aggregate_difference_eight :
    centeredNormGapGcd 8 = 5 ∧ centeredFoldGcdProduct 8 = 25 ∧
    centeredNormGapGcd 8 ≠ centeredFoldGcdProduct 8 := by
  decide +kernel

theorem eight_valuation_difference : padicValNat 5 (centeredNormGapGcd 8) = 1 ∧
    padicValNat 5 (centeredFoldGcdProduct 8) = 2 := by
  rw [aggregate_difference_eight.1, aggregate_difference_eight.2.1]
  constructor
  · rw [← Nat.factorization_def _ Nat.prime_five, Nat.prime_five.factorization, Finsupp.single_eq_same]
  · change padicValNat 5 ((5 : ℕ) ^ 2) = 2
    rw [← Nat.factorization_def _ Nat.prime_five, Nat.prime_five.factorization_pow, Finsupp.single_eq_same]

theorem prime_support_small : (centeredOddGapProduct 0).primeFactors = ∅ ∧
    (centeredOddGapProduct 1).primeFactors = ∅ ∧
    (centeredOddGapProduct 3).primeFactors = {3, 5} := by
  rw [centeredOddGapProduct_primeFactors, centeredOddGapProduct_primeFactors,
    centeredOddGapProduct_primeFactors]
  decide +kernel

/-- The fresh prime is visible to the aggregate, although bounded common support excludes it. -/
theorem fresh_three_packet : ∃ j < 3,
    5 ∣ Nat.gcd (3 ^ 2 + centeredLeftOffset 3 j) (3 ^ 2 + centeredRightOffset 3 j) ∧
    5 ∉ squareOffsetPrimeSupport 3 (centeredLeftOffset 3 j) ∧
    5 ∉ squareOffsetPrimeSupport 3 (centeredRightOffset 3 j) ∧ 5 % 4 = 1 ∧ 5 < 2 * 3 :=
  fresh_prime_centered_pair_packet (by decide) (by rw [fresh_three.2.1]) (by decide)

/-- A covered subfamily with gcd one; this is not a full-cover shell counterexample. -/
theorem covered_coprime_four : (centeredFoldNorm 4).Prime ∧
    (∀ j < 4, Nat.gcd (4 ^ 2 + centeredLeftOffset 4 j) (4 ^ 2 + centeredRightOffset 4 j) = 1) ∧
    SquareOffsetCovered 4 (centeredLeftOffset 4 0) ∧
    SquareOffsetCovered 4 (centeredRightOffset 4 0) := by
  have hp : (centeredFoldNorm 4).Prime := by norm_num [centeredFoldNorm]
  refine ⟨hp, (centeredFoldNorm_prime_iff_all_pairs (by decide)).mp hp, ?_, ?_⟩
  · exact ⟨2, mem_primeScalesUpTo.mpr ⟨by decide, by decide⟩,
      by norm_num [SquareOffsetForbiddenBy, centeredLeftOffset]⟩
  · exact ⟨3, mem_primeScalesUpTo.mpr ⟨by decide, by decide⟩,
      by norm_num [SquareOffsetForbiddenBy, centeredRightOffset]⟩

/-- Three whole pairs are covered while all five fold gcds are one. -/
theorem covered_coprime_five_family : ∀ j ∈ ({2, 3, 4} : Finset ℕ),
    SquareOffsetCovered 5 (centeredLeftOffset 5 j) ∧
    SquareOffsetCovered 5 (centeredRightOffset 5 j) ∧
    Nat.gcd (5 ^ 2 + centeredLeftOffset 5 j) (5 ^ 2 + centeredRightOffset 5 j) = 1 := by
  classical
  intro j hj
  have hjs : j = 2 ∨ j = 3 ∨ j = 4 := by simpa only [Finset.mem_insert, Finset.mem_singleton] using hj
  have hjn : j < 5 := by omega
  refine ⟨?_, ?_, (centeredFoldNorm_prime_iff_all_pairs (by decide)).mp
    (by norm_num [centeredFoldNorm]) j hjn⟩
  · by_contra hc
    have he := mem_escapingSquareOffsets.mpr ⟨squareOffset_centeredLeftOffset hjn, hc⟩
    rw [DkMathTest.LegendreResidueCoverCalibration.near_miss_five_escape] at he
    simp only [Finset.mem_insert, Finset.mem_singleton, centeredLeftOffset] at he
    omega
  · by_contra hc
    have he := mem_escapingSquareOffsets.mpr ⟨squareOffset_centeredRightOffset hjn, hc⟩
    rw [DkMathTest.LegendreResidueCoverCalibration.near_miss_five_escape] at he
    simp only [Finset.mem_insert, Finset.mem_singleton, centeredRightOffset] at he
    omega

theorem prime_norm_297 : (centeredFoldNorm 297).Prime ∧ centeredNormGapGcd 297 = 1 ∧
    centeredFoldGcdProduct 297 = 1 := by
  have hp : (centeredFoldNorm 297).Prime := by norm_num [centeredFoldNorm]
  have he := (centeredFoldNorm_prime_iff_normGapGcd_eq_one (by decide)).mp hp
  exact ⟨hp, he, (centeredFoldGcdProduct_eq_one_iff_normGapGcd_eq_one 297).mpr he⟩

/-- This records a small valuation certificate, without evaluating the large odd product. -/
theorem visible1031 : 5 ∣ centeredNormGapGcd 1031 ∧ 61 ∣ centeredNormGapGcd 1031 ∧
    ¬6977 ∣ centeredNormGapGcd 1031 ∧ centeredNormGapGcd 1031 ≠ 1 := by
  have h5 : 5 ∣ centeredNormGapGcd 1031 :=
    (prime_dvd_centeredNormGapGcd_iff (by decide)).mpr ⟨by norm_num [centeredFoldNorm], by decide, by decide⟩
  refine ⟨h5, ?_, ?_, ?_⟩
  · exact (prime_dvd_centeredNormGapGcd_iff (by decide)).mpr
      ⟨by norm_num [centeredFoldNorm], by decide, by decide⟩
  · intro hd
    have h := (prime_dvd_centeredNormGapGcd_iff (by norm_num : Nat.Prime 6977)).mp hd
    omega
  · intro he; rw [he] at h5; exact Nat.prime_five.not_dvd_one h5

theorem cyclotomic_fresh_address : DkMath.NumberTheory.GapFocusing.primeOrder 5 3 4 = 4 ∧
    DkMath.NumberTheory.GapFocusing.primeRatio 5 3 4 ^ 2 = -1 := by
  exact ⟨prime_dvd_centeredFoldNorm_order_four (n := 3) (by decide) (by norm_num [centeredFoldNorm]),
    prime_dvd_centeredFoldNorm_ratio_sq (n := 3) (by decide) (by norm_num [centeredFoldNorm])⟩

theorem aggregate_successor_separation :
    Nat.Coprime (centeredNormGapGcd 21) (centeredNormGapGcd 22) ∧
    Nat.Coprime (centeredFoldGcdProduct 21) (centeredFoldGcdProduct 22) :=
  ⟨centeredNormGapGcd_succ_coprime 21, centeredFoldGcdProduct_succ_coprime 21⟩


/-- The empty shell refutes an unqualified full-cover-implies-nontrivial-gcd rule. -/
theorem zero_full_cover_counterexample : SquareOffsetsFullyCovered 0 ∧
    centeredNormGapGcd 0 = 1 ∧ centeredFoldGcdProduct 0 = 1 := by
  refine ⟨?_, empty_boundary.2.2.1, empty_boundary.2.2.2.1⟩
  intro r hr
  dsimp [SquareOffset] at hr
  omega


/-- Consecutive separation does not imply pairwise separation or a unique first appearance. -/
theorem nonconsecutive_prime_reappears :
    5 ∣ centeredNormGapGcd 3 ∧ 5 ∣ centeredNormGapGcd 6 ∧
    ¬Nat.Coprime (centeredNormGapGcd 3) (centeredNormGapGcd 6) := by
  rw [fresh_three.2.1, old_six.2.1]
  decide


/-- A prime norm and trivial gcd aggregate do not imply full coverage. -/
theorem prime_norm_does_not_force_full_cover : (centeredFoldNorm 5).Prime ∧
    centeredNormGapGcd 5 = 1 ∧ ¬SquareOffsetsFullyCovered 5 := by
  have hp : (centeredFoldNorm 5).Prime := by norm_num [centeredFoldNorm]
  refine ⟨hp, (centeredFoldNorm_prime_iff_normGapGcd_eq_one (by decide)).mp hp, ?_⟩
  intro hf
  have he : 4 ∈ escapingSquareOffsets 5 := by
    rw [DkMathTest.LegendreResidueCoverCalibration.near_miss_five_escape]
    decide
  have h := mem_escapingSquareOffsets.mp he
  exact h.2 (hf 4 h.1)

end DkMathTest.LegendreFoldGcdRegression
