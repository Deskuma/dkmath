/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.ParitySafeSqrtCompositeRouting

#print "file: DkMath.NumberTheory.Legendre.ParitySafeSqrtQuotientConservation"

/-! Exact conservation includes rejected small-prime quotients. No incidence ledger is duplicated. -/

namespace DkMath.NumberTheory.Legendre
open scoped BigOperators

theorem sqrt_cross_fiber_eq_routed_prime_filter {n p : ℕ}
    (hp : p ∈ roughActiveLabels n (Nat.sqrt n)) :
    sqrtRoughCrossFiber n p = (sqrtRoughRoutedFiber n p).filter Nat.Prime := by
  classical
  rw [sqrt_cross_fiber_eq_quotient_prime_filter hp]
  ext q
  simp only [sqrtRoughRoutedFiber, Finset.mem_filter]
  constructor
  · intro hq
    have hc : q ∈ sqrtRoughCrossFiber n p := by
      rw [sqrt_cross_fiber_eq_quotient_prime_filter hp]
      exact Finset.mem_filter.mpr hq
    exact ⟨⟨hq.1, (Finset.mem_filter.mp
      (sqrt_cross_offset_packet (mem_sqrtRoughCrossKeys_fiber.mpr ⟨hp, hc⟩)).1).1⟩, hq.2⟩
  · rintro ⟨⟨h, _⟩, hp⟩; exact ⟨h, hp⟩

theorem sqrt_rejected_quotient_not_prime {n p q : ℕ}
    (hp : p ∈ roughActiveLabels n (Nat.sqrt n)) (hq : q ∈ sqrtRoughRejectedFiber n p) :
    ¬q.Prime := by
  intro hprime
  obtain ⟨hq, hnot⟩ := Finset.mem_filter.mp hq
  have hc : q ∈ sqrtRoughCrossFiber n p := by
    rw [sqrt_cross_fiber_eq_quotient_prime_filter hp]
    exact Finset.mem_filter.mpr ⟨hq, hprime⟩
  exact hnot (Finset.mem_filter.mp
    (sqrt_cross_offset_packet (mem_sqrtRoughCrossKeys_fiber.mpr ⟨hp, hc⟩)).1).1

/-- The additional rejected class is disjoint from all routed census quotients. -/
theorem sqrt_quotient_routed_rejected_partition (n p : ℕ) :
    Disjoint (sqrtRoughRoutedFiber n p) (sqrtRoughRejectedFiber n p) ∧
    sqrtRoughQuotientFiber n p = sqrtRoughRoutedFiber n p ∪ sqrtRoughRejectedFiber n p ∧
    (sqrtRoughQuotientFiber n p).card =
      (sqrtRoughRoutedFiber n p).card + (sqrtRoughRejectedFiber n p).card := by
  classical
  unfold sqrtRoughRoutedFiber sqrtRoughRejectedFiber
  refine ⟨?_, ?_, ?_⟩
  · exact Finset.disjoint_left.mpr (fun q hq hr => (Finset.mem_filter.mp hr).2 (Finset.mem_filter.mp hq).2)
  · ext q; simp only [Finset.mem_union, Finset.mem_filter]; tauto
  · exact (Finset.card_filter_add_card_filter_not _).symm

/-- Exact per-owner composite correction: routing plus small-prime rejection. -/
theorem sqrt_composite_fiber_corrected_partition {n p : ℕ}
    (hp : p ∈ roughActiveLabels n (Nat.sqrt n)) :
    sqrtRoughCompositeFiber n p =
      (sqrtRoughRoutedFiber n p).filter (fun q => ¬q.Prime) ∪ sqrtRoughRejectedFiber n p ∧
    Disjoint ((sqrtRoughRoutedFiber n p).filter (fun q => ¬q.Prime)) (sqrtRoughRejectedFiber n p) := by
  classical
  constructor
  · ext q
    simp only [sqrtRoughCompositeFiber, sqrtRoughRoutedFiber, Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hq, hc⟩
      by_cases hr : p * q - n ^ 2 ∈ canonicalRoughCandidates n (Nat.sqrt n)
      · exact Or.inl ⟨⟨hq, hr⟩, hc⟩
      · exact Or.inr (Finset.mem_filter.mpr ⟨hq, hr⟩)
    · rintro (⟨⟨hq, _⟩, hc⟩ | hq)
      · exact ⟨hq, hc⟩
      · exact ⟨(Finset.mem_filter.mp hq).1, sqrt_rejected_quotient_not_prime hp hq⟩
  · exact (sqrt_quotient_routed_rejected_partition n p).1.mono_left (Finset.filter_subset ..)

/-- The rough subcarrier is exactly existing rough incidence, with no new currency. -/
theorem sqrt_routed_quotient_sum_eq_rough_incidence (n : ℕ) :
    (∑ p ∈ roughActiveLabels n (Nat.sqrt n), (sqrtRoughRoutedFiber n p).card) =
      ∑ p ∈ squareAnchorOddActivePrimes n, (canonicalRoughWave n (Nat.sqrt n) p).card := by
  classical
  have hsum : (∑ p ∈ roughActiveLabels n (Nat.sqrt n), (sqrtRoughRoutedFiber n p).card) =
      ∑ p ∈ roughActiveLabels n (Nat.sqrt n), (canonicalRoughWave n (Nat.sqrt n) p).card :=
    Finset.sum_congr rfl (fun p hp => sqrt_routed_fiber_card_eq_rough_wave hp)
  rw [hsum]
  apply Finset.sum_subset (Finset.filter_subset ..)
  intro p hp hnot
  have hpLe : p ≤ Nat.sqrt n := by
    by_contra h
    exact hnot (Finset.mem_filter.mpr ⟨hp, by omega⟩)
  have he : canonicalRoughWave n (Nat.sqrt n) p = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro r hr
    obtain ⟨hr, hd⟩ := Finset.mem_filter.mp hr
    exact (Finset.mem_filter.mp hr).2 p hp hpLe hd
  rw [he, Finset.card_empty]

/-- The complete raw quotient law: rejection is essential, not an endpoint correction. -/
theorem sqrt_quotient_conservation (n : ℕ) :
    (∑ p ∈ roughActiveLabels n (Nat.sqrt n), (sqrtRoughQuotientFiber n p).card) =
      (sqrtRoughCrossKeys n).card + (sqrtRoughCubeKeys n).card +
      2 * (sqrtRoughRepeatedKeys n).card + 3 * (sqrtRoughTripleProductsInShell n).card +
      ∑ p ∈ roughActiveLabels n (Nat.sqrt n), (sqrtRoughRejectedFiber n p).card := by
  have he := Finset.sum_congr rfl (fun p (_hp : p ∈ roughActiveLabels n (Nat.sqrt n)) =>
    (sqrt_quotient_routed_rejected_partition n p).2.2)
  rw [Finset.sum_add_distrib, sqrt_routed_quotient_sum_eq_rough_incidence, sqrt_product_incidence] at he
  omega

/-- On rough quotients the composite part is precisely the weighted existing census. -/
theorem sqrt_routed_composite_sum (n : ℕ) :
    (∑ p ∈ roughActiveLabels n (Nat.sqrt n),
      ((sqrtRoughRoutedFiber n p).filter (fun q => ¬q.Prime)).card) =
      (sqrtRoughCubeKeys n).card + 2 * (sqrtRoughRepeatedKeys n).card +
      3 * (sqrtRoughTripleProductsInShell n).card := by
  classical
  have he := Finset.sum_congr rfl (fun p (hp : p ∈ roughActiveLabels n (Nat.sqrt n)) =>
    show (sqrtRoughCrossFiber n p).card +
      ((sqrtRoughRoutedFiber n p).filter (fun q => ¬q.Prime)).card =
      (sqrtRoughRoutedFiber n p).card from by
        rw [sqrt_cross_fiber_eq_routed_prime_filter hp]
        exact Finset.card_filter_add_card_filter_not Nat.Prime)
  rw [Finset.sum_add_distrib, ← sqrt_cross_count_eq_fiber_sum,
    sqrt_routed_quotient_sum_eq_rough_incidence, sqrt_product_incidence] at he
  omega

/-- Nat-safe isolation, including every composite quotient in the exact reduced window. -/
theorem sqrt_cross_add_composite_eq_total (n : ℕ) :
    (sqrtRoughCrossKeys n).card +
      (∑ p ∈ roughActiveLabels n (Nat.sqrt n), (sqrtRoughCompositeFiber n p).card) =
      ∑ p ∈ roughActiveLabels n (Nat.sqrt n), (sqrtRoughQuotientFiber n p).card := by
  rw [sqrt_cross_count_eq_fiber_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun p hp => (sqrt_quotient_prime_composite_partition hp).2.2.symm)

theorem sqrt_composite_sum_corrected (n : ℕ) :
    (∑ p ∈ roughActiveLabels n (Nat.sqrt n), (sqrtRoughCompositeFiber n p).card) =
      (sqrtRoughCubeKeys n).card + 2 * (sqrtRoughRepeatedKeys n).card +
      3 * (sqrtRoughTripleProductsInShell n).card +
      ∑ p ∈ roughActiveLabels n (Nat.sqrt n), (sqrtRoughRejectedFiber n p).card := by
  have h := sqrt_cross_add_composite_eq_total n
  rw [sqrt_quotient_conservation] at h
  omega


/-- The exact residual is Cross; additive conservation precedes Nat subtraction. -/
theorem sqrt_cross_eq_total_sub_routing (n : ℕ) :
    (sqrtRoughCrossKeys n).card =
      (∑ p ∈ roughActiveLabels n (Nat.sqrt n), (sqrtRoughQuotientFiber n p).card) -
        ((sqrtRoughCubeKeys n).card + 2 * (sqrtRoughRepeatedKeys n).card +
          3 * (sqrtRoughTripleProductsInShell n).card +
          ∑ p ∈ roughActiveLabels n (Nat.sqrt n), (sqrtRoughRejectedFiber n p).card) := by
  have := sqrt_quotient_conservation n
  omega

/-- Every structural composite lower bound gives an additive Cross upper bound. -/
theorem sqrt_cross_bound_of_composite_lower {n L : ℕ}
    (hL : L ≤ ∑ p ∈ roughActiveLabels n (Nat.sqrt n), (sqrtRoughCompositeFiber n p).card) :
    (sqrtRoughCrossKeys n).card + L ≤
      ∑ p ∈ roughActiveLabels n (Nat.sqrt n), (sqrtRoughQuotientFiber n p).card := by
  have := sqrt_cross_add_composite_eq_total n
  omega

/-- The known census mass gives a sharper capacity whenever that mass is positive. -/
theorem sqrt_cross_bound_of_rejected_lower {n J : ℕ}
    (hJ : J ≤ ∑ p ∈ roughActiveLabels n (Nat.sqrt n), (sqrtRoughRejectedFiber n p).card) :
    (sqrtRoughCrossKeys n).card + (sqrtRoughCubeKeys n).card +
      2 * (sqrtRoughRepeatedKeys n).card + 3 * (sqrtRoughTripleProductsInShell n).card + J ≤
      ∑ p ∈ roughActiveLabels n (Nat.sqrt n), (sqrtRoughQuotientFiber n p).card := by
  have := sqrt_quotient_conservation n
  omega


/-- A finite set of verified small primes supplies rejection lower bounds directly from quotients. -/
theorem sqrt_rejected_card_lower_of_small_primes {n p : ℕ}
    (hp : p ∈ roughActiveLabels n (Nat.sqrt n)) (S : Finset ℕ)
    (hS : ∀ u ∈ S, u.Prime ∧ u ≤ Nat.sqrt n) :
    ((sqrtRoughQuotientFiber n p).filter (fun q => ∃ u ∈ S, u ∣ q)).card ≤
      (sqrtRoughRejectedFiber n p).card := by
  classical
  apply Finset.card_le_card
  intro q hq
  obtain ⟨hq, u, hu, hd⟩ := Finset.mem_filter.mp hq
  exact (sqrt_quotient_rejected_iff_small_prime hp hq).mpr
    ⟨u, (hS u hu).1, hd, (hS u hu).2⟩

theorem sqrt_cross_le_total (n : ℕ) :
    (sqrtRoughCrossKeys n).card ≤
      ∑ p ∈ roughActiveLabels n (Nat.sqrt n), (sqrtRoughQuotientFiber n p).card := by
  have := sqrt_cross_add_composite_eq_total n
  omega

/-- Subtraction is exposed only after additive conservation guarantees its order condition. -/
theorem sqrt_cross_card_le_capacity_sub_routing {n J : ℕ}
    (hJ : J ≤ ∑ p ∈ roughActiveLabels n (Nat.sqrt n), (sqrtRoughRejectedFiber n p).card) :
    (sqrtRoughCrossKeys n).card ≤
      (∑ p ∈ roughActiveLabels n (Nat.sqrt n), (sqrtRoughQuotientFiber n p).card) -
        ((sqrtRoughCubeKeys n).card + 2 * (sqrtRoughRepeatedKeys n).card +
          3 * (sqrtRoughTripleProductsInShell n).card + J) := by
  have := sqrt_cross_bound_of_rejected_lower hJ
  omega

/-- A finite routing budget plugs directly into the existing prime-seat consumer. -/
theorem prime_squareCell_of_quotient_routing_budget {n J : ℕ} (hn : 0 < n)
    (hJ : J ≤ ∑ p ∈ roughActiveLabels n (Nat.sqrt n), (sqrtRoughRejectedFiber n p).card)
    (hbudget : (∑ p ∈ roughActiveLabels n (Nat.sqrt n), (sqrtRoughQuotientFiber n p).card) <
      (canonicalRoughCandidates n (Nat.sqrt n)).card + (sqrtRoughRepeatedKeys n).card +
        2 * (sqrtRoughTripleProductsInShell n).card + J) :
    ∃ p, p.Prime ∧ SquareCell n p := by
  apply prime_squareCell_of_sqrt_factorization_census hn
  have := sqrt_cross_bound_of_rejected_lower hJ
  omega

/-- Two finite geometric owner ranges; the exact sum retains each owner's endpoint carry. -/
theorem sqrt_quotient_sum_split_owner_range (n : ℕ) (f : ℕ → ℕ) :
    (∑ p ∈ roughActiveLabels n (Nat.sqrt n), f p) =
      (∑ p ∈ (roughActiveLabels n (Nat.sqrt n)).filter (fun p => p ≤ 2 * Nat.sqrt n), f p) +
      ∑ p ∈ (roughActiveLabels n (Nat.sqrt n)).filter (fun p => 2 * Nat.sqrt n < p), f p := by
  classical
  simpa only [not_le] using
    (Finset.sum_filter_add_sum_filter_not (roughActiveLabels n (Nat.sqrt n))
      (fun p => p ≤ 2 * Nat.sqrt n) f).symm

theorem primeAnchor_quotient_range_eq_floor {n : ℕ} (hn : n.Prime) (hne : n ≠ 2)
    (s : Finset ℕ) (hs : s ⊆ roughActiveLabels n (Nat.sqrt n)) :
    (∑ p ∈ s, (sqrtRoughQuotientFiber n p).card) = ∑ p ∈ s, primeAnchorProductWaveCount n p :=
  Finset.sum_congr rfl (fun _p hp => primeAnchor_quotient_fiber_card_eq_floor hn hne (hs hp))

/-- Elementary odd-prime spacing gives an exact odd-interval capacity before composite routing. -/
theorem sqrt_cross_fiber_card_le_odd_span {n p : ℕ}
    (hp : p ∈ roughActiveLabels n (Nat.sqrt n)) :
    (sqrtRoughCrossFiber n p).card ≤
      (((n ^ 2 + 2 * n) / p + 1) / 2) - ((max n (n ^ 2 / p) + 1) / 2) := by
  classical
  rw [← Nat.card_Ico]
  apply Finset.card_le_card_of_injOn (fun q => q / 2)
  · intro q hq
    have hw := mem_sqrtRoughCrossFiber.mp hq
    have hc := (mem_sqrtRoughQuotientFiber hp).mp (Finset.mem_filter.mp
      (by rw [← sqrt_cross_fiber_eq_quotient_prime_filter hp]; exact hq :
        q ∈ (sqrtRoughQuotientFiber n p).filter Nat.Prime)).1
    obtain ⟨k, hk⟩ := (coprime_two_mul_iff_coprime_and_odd.mp hc.2.2.2).2
    apply Finset.mem_Ico.mpr
    dsimp only
    omega
  · intro q hq s hs he
    have hqP := (mem_sqrtRoughCrossFiber.mp hq).1
    have hsP := (mem_sqrtRoughCrossFiber.mp hs).1
    have hn := mem_squareAnchorOddActivePrimes.mp (Finset.mem_filter.mp hp).1
    have hn2 := hn.1.two_le
    have hqN := (mem_sqrtRoughCrossFiber.mp hq).2.1
    have hsN := (mem_sqrtRoughCrossFiber.mp hs).2.1
    obtain ⟨a, ha⟩ := hqP.odd_of_ne_two (by omega)
    obtain ⟨b, hb⟩ := hsP.odd_of_ne_two (by omega)
    dsimp only at he
    omega

end DkMath.NumberTheory.Legendre
