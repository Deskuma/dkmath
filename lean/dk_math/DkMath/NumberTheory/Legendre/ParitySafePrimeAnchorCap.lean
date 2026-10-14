/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.ParitySafeCanonicalRoughCount
import Mathlib.Data.Nat.Sqrt

#print "file: DkMath.NumberTheory.Legendre.ParitySafePrimeAnchorCap"

namespace DkMath.NumberTheory.Legendre
open scoped BigOperators

theorem primeAnchorTwoPrimeWaveUpper_eq_count {n q : ℕ} (hn : n.Prime) (hne : n ≠ 2)
    (hq : q ∈ squareAnchorOddActivePrimes n) :
    paritySafeTwoPrimeWaveUpper n q = primeAnchorProductWaveCount n q := by
  have hqo := (mem_squareAnchorOddActivePrimes.mp hq).1.odd_of_ne_two
    (mem_squareAnchorOddActivePrimes.mp hq).2.2.2
  have hcop : Nat.Coprime n q :=
    ((mem_squareAnchorOddActivePrimes.mp hq).1.coprime_iff_not_dvd.mpr
      (mem_squareAnchorOddActivePrimes.mp hq).2.2.1).symm
  have hw : paritySafeActiveWaveOffsets n q = paritySafeProductWaveOffsets n q := by
    ext r
    simp only [mem_paritySafeActiveWaveOffsets,paritySafeProductWaveOffsets,Finset.mem_filter, SquareOffsetForbiddenBy]
  have hcard : (paritySafeActiveWaveOffsets n q).card = primeAnchorProductWaveCount n q := by
    rw [hw]
    exact paritySafeProductWave_card_eq_count hn (hn.odd_of_ne_two hne) hqo hcop
  apply Nat.le_antisymm
  · have hle := paritySafeTwoPrimeWaveUpper_le_waveUpper n q
    have hle' : paritySafeWaveUpper n q ≤ paritySafeDivisorWaveUpper n q n := by
      unfold paritySafeWaveUpper paritySafeQuotientWaveUpper
      rw [hn.primeFactors]
      have he : ({n}:Finset ℕ).erase 2 = {n} := by
        ext a; simp only [Finset.mem_erase,Finset.mem_singleton]; omega
      rw [he, Finset.fold_singleton]
      exact (min_le_right _ _).trans (min_le_left _ _)
    apply (hle.trans hle').trans
    have hdelta : paritySafeOddMultipleFloorDelta (n ^ 2) (n ^ 2 + 2 * n) q =
        paritySafeOddQuotientUpper n q := by
      unfold paritySafeOddMultipleFloorDelta paritySafeOddQuotientUpper
      rw [show 2 * q = q * 2 by omega]
      simp only [← Nat.div_div_eq_div_mul]
      have hAB : n ^ 2 / q ≤ (n ^ 2 + 2 * n) / q := Nat.div_le_div_right (by omega)
      omega
    have heq : paritySafeDivisorWaveUpper n q n = primeAnchorProductWaveCount n q := by
      unfold paritySafeDivisorWaveUpper primeAnchorProductWaveCount
      rw [hdelta]
      congr 1
      unfold paritySafeOddMultipleFloorDelta
      simp only [Nat.div_div_eq_div_mul, Nat.mul_left_comm, Nat.mul_comm, Nat.mul_assoc]
    exact heq.le
  · rw [← hcard]
    exact paritySafeActiveWave_card_le_twoPrimeWaveUpper hq

/-- For an odd prime anchor, the structural wave cap is exact; this is not assumed for other anchors. -/
theorem primeAnchorTwoPrimeWaveUpper_eq_card {n q : ℕ} (hn : n.Prime) (hne : n ≠ 2)
    (hq : q ∈ squareAnchorOddActivePrimes n) :
    paritySafeTwoPrimeWaveUpper n q = (paritySafeActiveWaveOffsets n q).card := by
  rw [primeAnchorTwoPrimeWaveUpper_eq_count hn hne hq]
  have he : paritySafeActiveWaveOffsets n q = paritySafeProductWaveOffsets n q := by
    ext r
    simp only [mem_paritySafeActiveWaveOffsets,paritySafeProductWaveOffsets,
      Finset.mem_filter,SquareOffsetForbiddenBy]
  rw [he]
  symm
  exact paritySafeProductWave_card_eq_count hn (hn.odd_of_ne_two hne)
    ((mem_squareAnchorOddActivePrimes.mp hq).1.odd_of_ne_two
      (mem_squareAnchorOddActivePrimes.mp hq).2.2.2)
    ((mem_squareAnchorOddActivePrimes.mp hq).1.coprime_iff_not_dvd.mpr
      (mem_squareAnchorOddActivePrimes.mp hq).2.2.1).symm

/-- Exactness of B2 at an odd prime anchor is derived by summing the proved pointwise identity. -/
theorem primeAnchorTwoPrimeUpper_eq_incidence {n : ℕ} (hn : n.Prime) (hne : n ≠ 2) :
    paritySafeTwoPrimeIncidenceUpper n = paritySafeIncidenceCount n := by
  classical
  unfold paritySafeTwoPrimeIncidenceUpper paritySafeIncidenceCount
  exact Finset.sum_congr rfl (fun q hq => primeAnchorTwoPrimeWaveUpper_eq_card hn hne hq)

/-- Prime-anchor cancellation retains covered seats and tail; its cap slack is proved zero. -/
theorem primeAnchorRemainingCap_eq_covered_tail {n : ℕ} (hn : n.Prime) (hne : n ≠ 2) (P : ℕ) :
    canonicalRemainingCap n P = (paritySafeCoveredCandidates n).card + (canonicalRootTail n P).card := by
  rw [canonicalRemainingCap_eq_covered_tail_slack,primeAnchorTwoPrimeUpper_eq_incidence hn hne,
    Nat.sub_self,Nat.add_zero]

/-- Exact prime-anchor head cancellation and the direct rough currency are equivalent. -/
theorem primeAnchorRemainingCap_lt_iff_rough {n : ℕ} (hn : n.Prime) (hne : n ≠ 2) (P : ℕ) :
    canonicalRemainingCap n P < (squareAnchorOddPointCoprimeOffsets n).card ↔
      (∑ q ∈ squareAnchorOddActivePrimes n, (canonicalRoughWave n P q).card) <
        (canonicalRoughCandidates n P).card := by
  rw [remainingCap_lt_iff_rough_currency,primeAnchorTwoPrimeUpper_eq_incidence hn hne,
    Nat.sub_self,Nat.add_zero]

/-- The structural B2 versus head comparison is the exact min-free rough comparison at odd primes. -/
theorem primeAnchorHead_gap_iff_rough {n : ℕ} (hn : n.Prime) (hne : n ≠ 2) (P : ℕ) :
    paritySafeTwoPrimeIncidenceUpper n < (squareAnchorOddPointCoprimeOffsets n).card +
      (canonicalRootHead n P).card ↔
      (∑ q ∈ squareAnchorOddActivePrimes n, (canonicalRoughWave n P q).card) <
        (canonicalRoughCandidates n P).card := by
  rw [← remainingCap_lt_candidate_iff]
  exact primeAnchorRemainingCap_lt_iff_rough hn hne P

/-- An independently specified sqrt cutoff has a four-label product above the shell endpoint. -/
theorem sqrtCutoff_power_four_gt (n : ℕ) :
    n ^ 2 + 2 * n < (Nat.sqrt n + 1) ^ 4 := by
  have h := Nat.succ_le_succ_sqrt' n
  calc
    n ^ 2 + 2 * n < (n + 1) ^ 2 := by nlinarith
    _ ≤ ((Nat.sqrt n + 1) ^ 2) ^ 2 := by
      simpa only [Nat.pow_two] using Nat.mul_self_le_mul_self h
    _ = (Nat.sqrt n + 1) ^ 4 := by ring

/-- No rough candidate at cutoff floor(sqrt n) has four distinct active support labels. -/
theorem sqrtCutoff_support_card_le_three {n r : ℕ}
    (hr : r ∈ canonicalRoughCandidates n (Nat.sqrt n)) :
    (paritySafeActiveSupport n r).card ≤ 3 := by
  apply rough_support_card_le (L := Nat.sqrt n + 1) hr
  · intro a ha hgt; omega
  · omega
  · exact sqrtCutoff_power_four_gt n

/-- The sqrt cutoff gives a uniform elementary tail multiplicity bound, without a demand claim. -/
theorem sqrtCutoff_tail_card_le_two_mul (n : ℕ) :
    (canonicalRootTail n (Nat.sqrt n)).card ≤ 2 * (canonicalRoughCandidates n (Nat.sqrt n)).card := by
  have h := canonicalRootTail_card_le_rough_mul (n := n) (P := Nat.sqrt n)
    (L := Nat.sqrt n + 1) (K := 3) (by intro a ha hgt; omega) (by omega)
    (sqrtCutoff_power_four_gt n)
  simpa only [show (3:ℕ)-1=2 by decide,Nat.mul_comm] using h

end DkMath.NumberTheory.Legendre
