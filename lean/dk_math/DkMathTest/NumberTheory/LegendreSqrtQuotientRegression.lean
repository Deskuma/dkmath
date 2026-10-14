/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.ParitySafeSqrtQuotientConservation
import DkMathTest.NumberTheory.LegendreSqrtRoughCensusRegression

#print "file: DkMathTest.NumberTheory.LegendreSqrtQuotientRegression"

namespace DkMathTest.LegendreSqrtQuotientRegression
open DkMath.NumberTheory.Legendre DkMathTest.LegendreBlockLocalization
open DkMathTest.LegendreSqrtRoughCensusRegression
set_option maxRecDepth 100000

/-- A reduced quotient need not reconstruct a rough seat, even at a prime anchor. -/
theorem rejected_eleven_packet :
    5 ∈ roughActiveLabels 11 (Nat.sqrt 11) ∧
    27 ∈ sqrtRoughQuotientFiber 11 5 ∧ ¬Nat.Prime 27 ∧
    3 ≤ Nat.sqrt 11 ∧ Nat.Prime 3 ∧ 3 ∣ 27 := by
  simp only [roughActiveLabels, oddActive_eq_filter_range,
    sqrtRoughQuotientFiber, paritySafeReducedQuotientInterval, Finset.mem_filter]
  decide +kernel

theorem rejected_eleven : 27 ∈ sqrtRoughRejectedFiber 11 5 :=
  (sqrt_quotient_rejected_iff_small_prime rejected_eleven_packet.1
    rejected_eleven_packet.2.1).mpr
      ⟨3, rejected_eleven_packet.2.2.2.2.1, rejected_eleven_packet.2.2.2.2.2,
        rejected_eleven_packet.2.2.2.1⟩


/-- The uncorrected raw conservation law is false at the smallest rejected anchor. -/
theorem uncorrected_conservation_eleven_false :
    (∑ p ∈ roughActiveLabels 11 (Nat.sqrt 11), (sqrtRoughQuotientFiber 11 p).card) ≠
      (sqrtRoughCrossKeys 11).card + (sqrtRoughCubeKeys 11).card +
      2 * (sqrtRoughRepeatedKeys 11).card + 3 * (sqrtRoughTripleProductsInShell 11).card := by
  have hpos := Finset.card_pos.mpr ⟨27, rejected_eleven⟩
  have hle := Finset.single_le_sum
    (fun p (_hp : p ∈ roughActiveLabels 11 (Nat.sqrt 11)) =>
      Nat.zero_le (sqrtRoughRejectedFiber 11 p).card) rejected_eleven_packet.1
  have hcon := sqrt_quotient_conservation 11
  omega

/-- Minimal natural anchor with two rough supported owners; the odd prime example is 13. -/
theorem repeated_eight_key : ((3, 5), true) ∈ sqrtRoughRepeatedKeys 8 := by
  simp only [sqrtRoughRepeatedKeys, sqrtRepeatedProduct]
  decide +kernel

theorem repeated_eight_quotients :
    25 ∈ sqrtRoughRoutedFiber 8 3 ∧ 15 ∈ sqrtRoughRoutedFiber 8 5 := by
  have h := sqrt_repeated_owner_quotients repeated_eight_key
  exact ⟨h.1, h.2.2.2.1⟩

theorem repeated_thirteen_quotients :
    35 ∈ sqrtRoughRoutedFiber 13 5 ∧ 25 ∈ sqrtRoughRoutedFiber 13 7 := by
  have h := sqrt_repeated_owner_quotients repeated_lower_key
  exact ⟨h.1, h.2.2.2.1⟩

theorem repeated_thirteen_owner_count :
    ((roughActiveLabels 13 (Nat.sqrt 13)).filter
      (fun p => ∃ q ∈ sqrtRoughRoutedFiber 13 p, p * q = 175)).card = 2 :=
  sqrt_repeated_quotient_owner_multiplicity repeated_lower_key

theorem triple_nineteen_quotients :
    77 ∈ sqrtRoughRoutedFiber 19 5 ∧ 55 ∈ sqrtRoughRoutedFiber 19 7 ∧
      35 ∈ sqrtRoughRoutedFiber 19 11 := by
  have h := sqrt_triple_owner_quotients triple_key_nineteen
  exact ⟨h.1, h.2.2.2.1, h.2.2.2.2.2.2.1⟩

theorem empty_zero_quotient_sum :
    (∑ p ∈ roughActiveLabels 0 (Nat.sqrt 0), (sqrtRoughQuotientFiber 0 p).card) = 0 := by
  simp only [roughActiveLabels, oddActive_eq_filter_range]
  decide +kernel


/-- Bounded minimality check for the first rejected class; it is not an endpoint proof. -/
theorem no_small_prime_rejection_before_eleven : ∀ n ∈ Finset.range 11,
    ∀ p ∈ Finset.Icc 3 n, p.Prime → Nat.sqrt n < p → ¬p ∣ n →
    ∀ q ∈ Finset.Ioc (n ^ 2 / p) ((n ^ 2 + 2 * n) / p), Nat.Coprime (2 * n) q →
    ∀ u ∈ Finset.Icc 2 (Nat.sqrt n), u.Prime → ¬u ∣ q := by
  decide +kernel

theorem rejected_eleven_is_minimal {n : ℕ} (hn : n < 11) :
    ∀ p ∈ roughActiveLabels n (Nat.sqrt n), sqrtRoughRejectedFiber n p = ∅ := by
  intro p hp
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro q hq
  have hpA := mem_squareAnchorOddActivePrimes.mp (Finset.mem_filter.mp hp).1
  have hp3 : 3 ≤ p := by have := hpA.1.two_le; omega
  have hqQ := (Finset.mem_filter.mp hq).1
  obtain ⟨u, hu, hd, hcut⟩ := (sqrt_quotient_rejected_iff_small_prime hp hqQ).mp hq
  exact no_small_prime_rejection_before_eleven n (Finset.mem_range.mpr hn)
    p (Finset.mem_Icc.mpr ⟨hp3, hpA.2.1⟩) hpA.1 (Finset.mem_filter.mp hp).2 hpA.2.2.1
    q (Finset.mem_filter.mp hqQ).1 (Finset.mem_filter.mp hqQ).2
    u (Finset.mem_Icc.mpr ⟨hu.two_le, hcut⟩) hu hd

/-- Before anchor 8, no reduced shell point has two distinct rough owners. -/
theorem no_multiple_owners_before_eight : ∀ n ∈ Finset.range 8,
    ∀ r ∈ Finset.Icc 1 (2 * n), Nat.Coprime (2 * n) (n ^ 2 + r) →
    ∀ p ∈ Finset.Icc 3 n, p.Prime → Nat.sqrt n < p → ¬p ∣ n → p ∣ n ^ 2 + r →
    ∀ q ∈ Finset.Icc 3 n, q.Prime → Nat.sqrt n < q → ¬q ∣ n → q ∣ n ^ 2 + r → p = q := by
  decide +kernel

/-- Before prime anchor 13, no reduced shell point has two distinct rough owners. -/
theorem no_prime_multiple_owners_before_thirteen : ∀ n ∈ Finset.range 13, n.Prime →
    ∀ r ∈ Finset.Icc 1 (2 * n), Nat.Coprime (2 * n) (n ^ 2 + r) →
    ∀ p ∈ Finset.Icc 3 n, p.Prime → Nat.sqrt n < p → ¬p ∣ n → p ∣ n ^ 2 + r →
    ∀ q ∈ Finset.Icc 3 n, q.Prime → Nat.sqrt n < q → ¬q ∣ n → q ∣ n ^ 2 + r → p = q := by
  decide +kernel

end DkMathTest.LegendreSqrtQuotientRegression
