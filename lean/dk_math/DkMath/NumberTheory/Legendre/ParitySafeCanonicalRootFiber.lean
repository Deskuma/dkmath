/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.ParitySafeSupportExcessQuotient
import DkMath.NumberTheory.Legendre.PairOverlap

#print "file: DkMath.NumberTheory.Legendre.ParitySafeCanonicalRootFiber"

/-! Reindex the existing exact quotient incidence by its least actual support
prime. Product waves always retain the actual candidate condition. -/

namespace DkMath.NumberTheory.Legendre
open scoped BigOperators

/-- The existing incidence expressed in actual support rather than quotient support. -/
theorem mem_canonicalIncidence_iff {n r q : ℕ} :
    (r, q) ∈ paritySafeCanonicalQuotientCoSupportIncidences n ↔
      r ∈ squareAnchorOddPointCoprimeOffsets n ∧
      q ∈ paritySafeActiveSupport n r ∧ q ≠ paritySafeCanonicalSupportPrime n r := by
  classical
  constructor
  · intro h
    have hc := (Finset.mem_product.mp (Finset.mem_filter.mp h).1).1
    have hp := paritySafeCanonicalSupportPrime_packet hc
    have he := (Finset.mem_filter.mp h).2
    rw [erase_squareQuotientSupport_eq_erase_offsetSupport hp.2.2.1,
      squareOffsetAnchorNondivisorSupport_eq_paritySafeActiveSupport_of_candidate hp.1] at he
    exact ⟨hp.1, (Finset.mem_erase.mp he).2, (Finset.mem_erase.mp he).1⟩
  · rintro ⟨hr, hq, hne⟩
    have hc := mem_paritySafeCoveredCandidates.mpr ⟨hr, ⟨q, hq⟩⟩
    have hp := paritySafeCanonicalSupportPrime_packet hc
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨hc, (mem_paritySafeActiveSupport_iff_dvd.mp hq).1⟩, ?_⟩
    rw [erase_squareQuotientSupport_eq_erase_offsetSupport hp.2.2.1,
      squareOffsetAnchorNondivisorSupport_eq_paritySafeActiveSupport_of_candidate hr]
    exact Finset.mem_erase.mpr ⟨hne, hq⟩

/-- Least-support ownership, including the empty-support default boundary. -/
theorem canonicalSupport_eq_iff_minimal {n r p : ℕ} (hp : 0 < p) :
    paritySafeCanonicalSupportPrime n r = p ↔
      p ∈ paritySafeActiveSupport n r ∧ ∀ a ∈ paritySafeActiveSupport n r, p ≤ a := by
  classical
  by_cases h : (paritySafeActiveSupport n r).Nonempty
  · simp only [paritySafeCanonicalSupportPrime, dite_eq_left h]
    exact Finset.min'_eq_iff _ h p
  · have he := Finset.not_nonempty_iff_eq_empty.mp h
    simp [paritySafeCanonicalSupportPrime, he, Nat.ne_of_gt hp |>.symm]

/-- Divisibility form of the generic finite smaller-active-prime sieve. -/
theorem canonicalSupport_eq_iff_no_smaller {n r p : ℕ}
    (hp : p ∈ squareAnchorOddActivePrimes n) :
    paritySafeCanonicalSupportPrime n r = p ↔
      p ∣ n ^ 2 + r ∧ ∀ a ∈ squareAnchorOddActivePrimes n, a < p → ¬a ∣ n ^ 2 + r := by
  have hpPos := (mem_squareAnchorOddActivePrimes.mp hp).1.pos
  rw [canonicalSupport_eq_iff_minimal hpPos]
  constructor
  · rintro ⟨hs, hmin⟩
    refine ⟨(mem_paritySafeActiveSupport_iff_dvd.mp hs).2, ?_⟩
    intro a ha hlt hd
    have := hmin a (mem_paritySafeActiveSupport_iff_dvd.mpr ⟨ha, hd⟩)
    omega
  · rintro ⟨hd, hsmall⟩
    refine ⟨mem_paritySafeActiveSupport_iff_dvd.mpr ⟨hp, hd⟩, ?_⟩
    intro a ha
    have hs := mem_paritySafeActiveSupport_iff_dvd.mp ha
    by_contra hn
    exact hsmall a hs.1 (by omega) hs.2

/-- Each existing canonical edge is ordered strictly away from its minimum root. -/
theorem canonicalIncidence_root_lt {n r q : ℕ}
    (h : (r, q) ∈ paritySafeCanonicalQuotientCoSupportIncidences n) :
    paritySafeCanonicalSupportPrime n r < q := by
  have hh := mem_canonicalIncidence_iff.mp h
  have hc := mem_paritySafeCoveredCandidates.mpr ⟨hh.1, ⟨q, hh.2.1⟩⟩
  have hp := paritySafeCanonicalSupportPrime_packet hc
  have hmin := (canonicalSupport_eq_iff_minimal
    (mem_squareAnchorOddActivePrimes.mp hp.2.2.2).1.pos).mp rfl
  have := hmin.2 q hh.2.1
  omega

/-- A filter of the established exact incidence, with no new excess ledger. -/
noncomputable def canonicalRootFiber (n p : ℕ) : Finset (ℕ × ℕ) :=
  (paritySafeCanonicalQuotientCoSupportIncidences n).filter
    (fun i => paritySafeCanonicalSupportPrime n i.1 = p)

/-- Candidate product-wave hits; raw square-wave counts need this filter. -/
noncomputable def paritySafeProductWaveOffsets (n m : ℕ) : Finset ℕ :=
  (squareAnchorOddPointCoprimeOffsets n).filter (fun r => m ∣ n ^ 2 + r)

/-- Seats of an ordered pair surviving the finite smaller-prime sieve. -/
noncomputable def canonicalRootPairOffsets (n p q : ℕ) : Finset ℕ :=
  (paritySafeProductWaveOffsets n (p * q)).filter
    (fun r => ∀ a ∈ squareAnchorOddActivePrimes n, a < p → ¬a ∣ n ^ 2 + r)

/-- Exact partition of the original support excess by canonical root. -/
theorem supportExcess_eq_sum_canonicalRootFiber (n : ℕ) :
    paritySafeSupportExcess n = ∑ p ∈ squareAnchorOddActivePrimes n,
      (canonicalRootFiber n p).card := by
  classical
  rw [← paritySafeCanonicalQuotientCoSupportIncidences_card_eq_supportExcess]
  symm
  simp only [canonicalRootFiber]
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  congr 1
  apply Finset.filter_eq_self.mpr
  intro i hi
  exact (paritySafeCanonicalQuotientCoSupportIncidence_packet hi).2.1

/-- Any finite root selection charges at most the existing excess. -/
theorem sum_canonicalRootFiber_le_excess (n : ℕ) (R : Finset ℕ) :
    (∑ p ∈ R, (canonicalRootFiber n p).card) ≤ paritySafeSupportExcess n := by
  classical
  simp only [canonicalRootFiber]
  rw [Finset.sum_card_fiberwise_eq_card_filter,
    ← paritySafeCanonicalQuotientCoSupportIncidences_card_eq_supportExcess]
  exact Finset.card_le_card (Finset.filter_subset _ _)

/-- Distinct root filters cannot share an incidence. -/
theorem canonicalRootFiber_disjoint (n : ℕ) {p s : ℕ} (hne : p ≠ s) :
    Disjoint (canonicalRootFiber n p) (canonicalRootFiber n s) := by
  classical
  apply Finset.disjoint_left.mpr
  intro i hi hj
  exact hne ((Finset.mem_filter.mp hi).2.symm.trans (Finset.mem_filter.mp hj).2)

/-- Exact bridge from the finite product sieve to an old canonical incidence. -/
theorem mem_canonicalRootPairOffsets_iff {n p q r : ℕ}
    (hp : p ∈ squareAnchorOddActivePrimes n) (hq : q ∈ squareAnchorOddActivePrimes n)
    (hpq : p < q) :
    r ∈ canonicalRootPairOffsets n p q ↔ (r, q) ∈ canonicalRootFiber n p := by
  classical
  have hcop : Nat.Coprime p q := (mem_squareAnchorOddActivePrimes.mp hp).1.coprime_iff_not_dvd.mpr
    (by intro hd; have he := (Nat.dvd_prime (mem_squareAnchorOddActivePrimes.mp hq).1).mp hd
        rcases he with he | he <;> have := (mem_squareAnchorOddActivePrimes.mp hp).1.two_le <;> omega)
  simp only [canonicalRootPairOffsets, paritySafeProductWaveOffsets, canonicalRootFiber,
    Finset.mem_filter, mem_canonicalIncidence_iff]
  constructor
  · rintro ⟨⟨hr, hd⟩, hs⟩
    have hpdiv := dvd_trans (dvd_mul_right p q) hd
    have hqdiv := dvd_trans (dvd_mul_left q p) hd
    have hroot := (canonicalSupport_eq_iff_no_smaller hp).mpr ⟨hpdiv, hs⟩
    exact ⟨⟨hr, mem_paritySafeActiveSupport_iff_dvd.mpr ⟨hq, hqdiv⟩, by omega⟩, hroot⟩
  · rintro ⟨⟨hr, hqs, _⟩, hroot⟩
    have hh := (canonicalSupport_eq_iff_no_smaller hp).mp hroot
    exact ⟨⟨hr, hcop.mul_dvd_of_dvd_of_dvd hh.1
      (mem_paritySafeActiveSupport_iff_dvd.mp hqs).2⟩, hh.2⟩

/-- The root fiber is the sum of all secondary active labels, without truncation. -/
theorem canonicalRootFiber_card_eq_sum_pairs {n p : ℕ}
    (hp : p ∈ squareAnchorOddActivePrimes n) :
    (canonicalRootFiber n p).card =
      ∑ q ∈ (squareAnchorOddActivePrimes n).filter (fun q => p < q),
        (canonicalRootPairOffsets n p q).card := by
  classical
  let Q := (squareAnchorOddActivePrimes n).filter (fun q => p < q)
  have hf := Finset.card_eq_sum_card_fiberwise (s := canonicalRootFiber n p)
    (t := Q) (f := Prod.snd) (by
      intro i hi
      have hh := Finset.mem_filter.mp hi
      exact Finset.mem_filter.mpr ⟨(paritySafeCanonicalQuotientCoSupportIncidence_packet hh.1).2.2.1,
        hh.2 ▸ canonicalIncidence_root_lt hh.1⟩)
  rw [hf]
  apply Finset.sum_congr rfl
  intro q hq
  have hq' := Finset.mem_filter.mp hq
  symm
  apply Finset.card_bij (fun r _ => (r, q))
  · intro r hr
    exact Finset.mem_filter.mpr ⟨(mem_canonicalRootPairOffsets_iff hp hq'.1 hq'.2).mp hr, rfl⟩
  · intro a ha b hb he
    exact congrArg Prod.fst he
  · intro i hi
    have h := Finset.mem_filter.mp hi
    refine ⟨i.1, ?_, ?_⟩
    · apply (mem_canonicalRootPairOffsets_iff hp hq'.1 hq'.2).mpr
      rcases i with ⟨a, b⟩
      dsimp at h ⊢
      rw [← h.2]
      exact h.1
    · exact Prod.ext rfl h.2.symm

/-- Finer ordered root/secondary-label decomposition of the existing excess. -/
theorem supportExcess_eq_sum_canonicalRootPairs (n : ℕ) :
    paritySafeSupportExcess n = ∑ p ∈ squareAnchorOddActivePrimes n,
      ∑ q ∈ (squareAnchorOddActivePrimes n).filter (fun q => p < q),
        (canonicalRootPairOffsets n p q).card := by
  rw [supportExcess_eq_sum_canonicalRootFiber]
  apply Finset.sum_congr rfl
  intro p hp
  exact canonicalRootFiber_card_eq_sum_pairs hp

/-- The raw carry budget bounds candidate waves; equality requires retaining corrections. -/
theorem paritySafeProductWave_card_le_div_add_carry {n m : ℕ} (hm : 0 < m) :
    (paritySafeProductWaveOffsets n m).card ≤ 2 * n / m + squareWaveCarry n m := by
  rw [← card_squareWaveOffsets_eq_div_add_carry hm]
  apply Finset.card_le_card
  intro r hr
  obtain ⟨hc, hd⟩ := Finset.mem_filter.mp hr
  exact mem_squareWaveOffsets.mpr
    ⟨(mem_squareAnchorOddPointCoprimeOffsets_iff_reducedResidue.mp hc).1, hd⟩

/-- Candidate pair overlaps are the existing product wave with candidate filtering. -/
theorem paritySafeProductWave_eq_filtered_pairOverlap {n p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    paritySafeProductWaveOffsets n (p * q) =
      (squarePrimePairOverlapOffsets n p q).filter
        (fun r => r ∈ squareAnchorOddPointCoprimeOffsets n) := by
  classical
  rw [squarePrimePairOverlapOffsets_eq_squareWaveOffsets_product hp hq hne]
  ext r
  simp only [paritySafeProductWaveOffsets, Finset.mem_filter, mem_squareWaveOffsets]
  have hc := mem_squareAnchorOddPointCoprimeOffsets_iff_reducedResidue (n := n) (r := r)
  tauto

/-- A supported star uses at most the local support excess, with any supported root. -/
theorem supportedStar_card_le_localExcess {n r p : ℕ} (Q : Finset ℕ)
    (hp : p ∈ paritySafeActiveSupport n r) (hQ : Q ⊆ paritySafeActiveSupport n r)
    (hne : p ∉ Q) : Q.card ≤ (paritySafeActiveSupport n r).card - 1 := by
  classical
  rw [← Finset.card_erase_of_mem hp]
  apply Finset.card_le_card
  intro q hq
  exact Finset.mem_erase.mpr ⟨by intro he; subst q; exact hne hq, hQ hq⟩

end DkMath.NumberTheory.Legendre
