/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.ParitySafeSqrtRoughCensus

#print "file: DkMath.NumberTheory.Legendre.ParitySafeSqrtCrossQuotient"

/-! Exact reduced quotients. The owner is rough; its quotient need not be rough. -/

namespace DkMath.NumberTheory.Legendre
open scoped BigOperators

noncomputable abbrev sqrtRoughQuotientFiber (n p : ℕ) : Finset ℕ :=
  paritySafeReducedQuotientInterval n p

noncomputable def sqrtRoughCompositeFiber (n p : ℕ) : Finset ℕ :=
  (sqrtRoughQuotientFiber n p).filter (fun q => ¬q.Prime)

/-- The extra filter needed to route a reduced quotient into the existing rough census. -/
noncomputable def sqrtRoughRoutedFiber (n p : ℕ) : Finset ℕ :=
  (sqrtRoughQuotientFiber n p).filter
    (fun q => p * q - n ^ 2 ∈ canonicalRoughCandidates n (Nat.sqrt n))

/-- Reduced quotients rejected by a small prime factor; these are not census seats. -/
noncomputable def sqrtRoughRejectedFiber (n p : ℕ) : Finset ℕ :=
  (sqrtRoughQuotientFiber n p).filter
    (fun q => p * q - n ^ 2 ∉ canonicalRoughCandidates n (Nat.sqrt n))

theorem sqrt_quotient_gt_anchor {n p q : ℕ}
    (hp : p ∈ roughActiveLabels n (Nat.sqrt n))
    (hq : q ∈ sqrtRoughQuotientFiber n p) : n < q := by
  have hi := paritySafeReducedQuotientInterval_mem_wave (Finset.mem_filter.mp hp).1 hq
  have hh := paritySafeActiveWaveOffsets_quotient_properties (Finset.mem_filter.mp hp).1 hi.1
  simpa only [hi.2] using hh.1

/-- Membership includes all three quotient endpoints and the exact coprimality restriction. -/
theorem mem_sqrtRoughQuotientFiber {n p q : ℕ}
    (hp : p ∈ roughActiveLabels n (Nat.sqrt n)) :
    q ∈ sqrtRoughQuotientFiber n p ↔
      n < q ∧ n ^ 2 / p < q ∧ q ≤ (n ^ 2 + 2 * n) / p ∧ Nat.Coprime (2 * n) q := by
  constructor
  · intro hq
    exact ⟨sqrt_quotient_gt_anchor hp hq,
      (Finset.mem_Ioc.mp (Finset.mem_filter.mp hq).1).1,
      (Finset.mem_Ioc.mp (Finset.mem_filter.mp hq).1).2, (Finset.mem_filter.mp hq).2⟩
  · rintro ⟨_, hlo, hhi, hc⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hlo, hhi⟩, hc⟩

theorem sqrt_quotient_ne_zero_ne_one {n p q : ℕ}
    (hp : p ∈ roughActiveLabels n (Nat.sqrt n)) (hq : q ∈ sqrtRoughQuotientFiber n p) :
    q ≠ 0 ∧ q ≠ 1 := by
  have hn := mem_squareAnchorOddActivePrimes.mp (Finset.mem_filter.mp hp).1
  have hg := sqrt_quotient_gt_anchor hp hq
  have := hn.1.two_le
  omega

theorem sqrt_cross_fiber_eq_quotient_prime_filter {n p : ℕ}
    (hp : p ∈ roughActiveLabels n (Nat.sqrt n)) :
    sqrtRoughCrossFiber n p = (sqrtRoughQuotientFiber n p).filter Nat.Prime := by
  classical
  rw [sqrt_cross_fiber_eq_reduced_quotient_filter hp]
  ext q
  simp only [Finset.mem_filter]
  exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, sqrt_quotient_gt_anchor hp h.1⟩⟩

theorem sqrt_quotient_prime_composite_partition {n p : ℕ}
    (hp : p ∈ roughActiveLabels n (Nat.sqrt n)) :
    Disjoint (sqrtRoughCrossFiber n p) (sqrtRoughCompositeFiber n p) ∧
      sqrtRoughQuotientFiber n p = sqrtRoughCrossFiber n p ∪ sqrtRoughCompositeFiber n p ∧
      (sqrtRoughQuotientFiber n p).card =
        (sqrtRoughCrossFiber n p).card + (sqrtRoughCompositeFiber n p).card := by
  classical
  rw [sqrt_cross_fiber_eq_quotient_prime_filter hp, sqrtRoughCompositeFiber]
  refine ⟨?_, ?_, ?_⟩
  · exact Finset.disjoint_left.mpr (fun q hq hc => (Finset.mem_filter.mp hc).2 (Finset.mem_filter.mp hq).2)
  · ext q; simp only [Finset.mem_union, Finset.mem_filter]; tauto
  · exact (Finset.card_filter_add_card_filter_not (s := sqrtRoughQuotientFiber n p) Nat.Prime).symm

/-- The seat packet does not assert roughness or singleton support. -/
theorem sqrt_quotient_seat_packet {n p q : ℕ}
    (hp : p ∈ roughActiveLabels n (Nat.sqrt n)) (hq : q ∈ sqrtRoughQuotientFiber n p) :
    SquareOffset n (p * q - n ^ 2) ∧
      Nat.Coprime (2 * n) (n ^ 2 + (p * q - n ^ 2)) ∧
      n ^ 2 + (p * q - n ^ 2) = p * q ∧
      p ∈ paritySafeActiveSupport n (p * q - n ^ 2) ∧
      squareOffsetSupportQuotient n p (p * q - n ^ 2) = q := by
  have hw := paritySafeReducedQuotientInterval_mem_wave (Finset.mem_filter.mp hp).1 hq
  have hc := mem_paritySafeActiveWaveOffsets.mp hw.1
  have hs := mem_squareAnchorOddPointCoprimeOffsets_iff_reducedResidue.mp hc.1
  have hm := (mem_paritySafeReducedQuotientInterval_iff
    (mem_squareAnchorOddActivePrimes.mp (Finset.mem_filter.mp hp).1).1.pos).mp hq
  refine ⟨hs.1, hs.2, by omega, ?_, hw.2⟩
  exact mem_paritySafeActiveSupport_iff_dvd.mpr ⟨(Finset.mem_filter.mp hp).1, hc.2⟩

theorem sqrt_quotient_seat_rough_iff {n p q : ℕ}
    (hp : p ∈ roughActiveLabels n (Nat.sqrt n)) (hq : q ∈ sqrtRoughQuotientFiber n p) :
    p * q - n ^ 2 ∈ canonicalRoughCandidates n (Nat.sqrt n) ↔
      ∀ u, u.Prime → u ∣ q → Nat.sqrt n < u := by
  have hs := sqrt_quotient_seat_packet hp hq
  constructor
  · intro hr u hu hd
    apply sqrt_rough_prime_divisor_gt hr hu
    rw [hs.2.2.1]
    exact dvd_mul_of_dvd_right hd p
  · intro hf
    apply sqrt_rough_of_reduced_point hs.1 hs.2.1
    intro u hu hd
    rw [hs.2.2.1] at hd
    rcases hu.dvd_mul.mp hd with hup | huq
    · have he := (Nat.prime_dvd_prime_iff_eq hu
        (mem_squareAnchorOddActivePrimes.mp (Finset.mem_filter.mp hp).1).1).mp hup
      simpa only [he] using (Finset.mem_filter.mp hp).2
    · exact hf u hu huq

theorem sqrt_quotient_rejected_iff_small_prime {n p q : ℕ}
    (hp : p ∈ roughActiveLabels n (Nat.sqrt n)) (hq : q ∈ sqrtRoughQuotientFiber n p) :
    q ∈ sqrtRoughRejectedFiber n p ↔ ∃ u, u.Prime ∧ u ∣ q ∧ u ≤ Nat.sqrt n := by
  classical
  simp only [sqrtRoughRejectedFiber, Finset.mem_filter, hq, true_and,
    sqrt_quotient_seat_rough_iff hp hq]
  push Not
  rfl

theorem sqrt_quotient_below_empty_above_eq {n p : ℕ}
    (hp : p ∈ roughActiveLabels n (Nat.sqrt n)) :
    (sqrtRoughQuotientFiber n p).filter (fun q => q ≤ n) = ∅ ∧
      (sqrtRoughQuotientFiber n p).filter (fun q => n < q) = sqrtRoughQuotientFiber n p := by
  classical
  constructor
  · apply Finset.eq_empty_iff_forall_notMem.mpr
    intro q hq
    have h := Finset.mem_filter.mp hq
    have := sqrt_quotient_gt_anchor hp h.1
    omega
  · exact Finset.filter_eq_self.mpr (fun q hq => sqrt_quotient_gt_anchor hp hq)

/-- Exact odd floor count, with the anchor exclusion retained. -/
theorem primeAnchor_quotient_fiber_card_eq_floor {n p : ℕ} (hn : n.Prime) (hne : n ≠ 2)
    (hp : p ∈ roughActiveLabels n (Nat.sqrt n)) :
    (sqrtRoughQuotientFiber n p).card = primeAnchorProductWaveCount n p := by
  have hpA := activePrime_reducedResidue_packet (Finset.mem_filter.mp hp).1
  rw [← card_paritySafeActiveWaveOffsets_eq_reducedQuotientInterval (Finset.mem_filter.mp hp).1]
  have he : paritySafeActiveWaveOffsets n p = paritySafeProductWaveOffsets n p := by
    ext r
    simp only [mem_paritySafeActiveWaveOffsets_iff_dvd, paritySafeProductWaveOffsets, Finset.mem_filter]
  rw [he, paritySafeProductWave_card_eq_count hn (hn.odd_of_ne_two hne)
    (hpA.1.odd_of_ne_two hpA.2.2.2.1)
    (hpA.2.2.2.2.coprime_dvd_left (dvd_mul_left n 2))]

end DkMath.NumberTheory.Legendre
