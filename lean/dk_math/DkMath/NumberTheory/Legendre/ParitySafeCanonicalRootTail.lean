/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.ParitySafeCanonicalRootCharge
import Mathlib.Algebra.Order.BigOperators.Group.Finset

#print "file: DkMath.NumberTheory.Legendre.ParitySafeCanonicalRootTail"

/-! Complementary filters of the old excess incidence. Rough seats retain empty
support, whereas tail edges retain canonical erasure. Remaining cap also retains
covered seats and the slack between B2 and actual incidence. -/

namespace DkMath.NumberTheory.Legendre
open scoped BigOperators

noncomputable def canonicalRootHead (n P : ℕ) : Finset (ℕ × ℕ) :=
  (paritySafeCanonicalQuotientCoSupportIncidences n).filter
    (fun i => paritySafeCanonicalSupportPrime n i.1 ≤ P)

noncomputable def canonicalRootTail (n P : ℕ) : Finset (ℕ × ℕ) :=
  (paritySafeCanonicalQuotientCoSupportIncidences n).filter
    (fun i => P < paritySafeCanonicalSupportPrime n i.1)

/-- Rough candidates include prime seats and other seats with empty active support. -/
noncomputable def canonicalRoughCandidates (n P : ℕ) : Finset ℕ :=
  (squareAnchorOddPointCoprimeOffsets n).filter
    (fun r => ∀ a ∈ squareAnchorOddActivePrimes n, a ≤ P → ¬a ∣ n ^ 2 + r)

/-- Exact head/tail partition of the already established E incidence. -/
theorem supportExcess_eq_head_add_tail (n P : ℕ) :
    paritySafeSupportExcess n = (canonicalRootHead n P).card + (canonicalRootTail n P).card := by
  classical
  rw [← paritySafeCanonicalQuotientCoSupportIncidences_card_eq_supportExcess]
  have h := Finset.card_filter_add_card_filter_not
    (s := paritySafeCanonicalQuotientCoSupportIncidences n)
    (fun i => paritySafeCanonicalSupportPrime n i.1 ≤ P)
  simpa only [canonicalRootHead, canonicalRootTail, Nat.not_le] using h.symm

/-- Head charge is the sum of the existing root fibers at the cutoff. -/
theorem canonicalRootHead_card_eq_root_sum (n P : ℕ) :
    (canonicalRootHead n P).card =
      ∑ p ∈ (squareAnchorOddActivePrimes n).filter (fun p => p ≤ P),
        (canonicalRootFiber n p).card := by
  classical
  simp only [canonicalRootFiber]
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  congr 1
  ext i
  simp only [canonicalRootHead, Finset.mem_filter]
  constructor
  · rintro ⟨hi, hP⟩
    exact ⟨hi, (paritySafeCanonicalQuotientCoSupportIncidence_packet hi).2.1, hP⟩
  · rintro ⟨hi, _, hP⟩; exact ⟨hi, hP⟩

/-- Covered support is essential: the total default root0 does not describe empty rough seats. -/
theorem canonicalRoot_gt_iff_rough {n r P : ℕ} (hc : r ∈ paritySafeCoveredCandidates n) :
    P < paritySafeCanonicalSupportPrime n r ↔
      ∀ a ∈ squareAnchorOddActivePrimes n, a ≤ P → ¬a ∣ n ^ 2 + r := by
  have hp := paritySafeCanonicalSupportPrime_packet hc
  have hmin := (canonicalSupport_eq_iff_minimal
    (mem_squareAnchorOddActivePrimes.mp hp.2.2.2).1.pos).mp rfl
  constructor
  · intro hgt a ha hle hd
    have := hmin.2 a (mem_paritySafeActiveSupport_iff_dvd.mpr ⟨ha, hd⟩)
    omega
  · intro hr
    by_contra hnot
    exact hr _ hp.2.2.2 (by omega)
      (mem_paritySafeActiveSupport_iff_dvd.mp hp.2.1).2

/-- A non-root support label is exactly a label with a smaller supported active prime. -/
theorem supportLabel_ne_root_iff_smaller {n r q : ℕ}
    (hq : q ∈ paritySafeActiveSupport n r) :
    q ≠ paritySafeCanonicalSupportPrime n r ↔
      ∃ a ∈ squareAnchorOddActivePrimes n, a < q ∧ a ∣ n ^ 2 + r := by
  classical
  have hn : (paritySafeActiveSupport n r).Nonempty := ⟨q, hq⟩
  have hmem : paritySafeCanonicalSupportPrime n r ∈ paritySafeActiveSupport n r := by
    rw [paritySafeCanonicalSupportPrime, dite_eq_left hn]
    exact Finset.min'_mem _ hn
  have hp := mem_paritySafeActiveSupport_iff_dvd.mp hmem
  have hmin := (canonicalSupport_eq_iff_minimal
    (mem_squareAnchorOddActivePrimes.mp hp.1).1.pos).mp rfl
  constructor
  · intro hne
    exact ⟨_, hp.1, by have := hmin.2 q hq; omega, hp.2⟩
  · rintro ⟨a, ha, hlt, hd⟩ hEq
    have := hmin.2 a (mem_paritySafeActiveSupport_iff_dvd.mpr ⟨ha, hd⟩)
    omega

/-- Exact min-free tail membership. Omitting the smaller-label field counts the erased root. -/
theorem mem_canonicalRootTail_iff {n P r q : ℕ} :
    (r,q) ∈ canonicalRootTail n P ↔
      r ∈ canonicalRoughCandidates n P ∧ q ∈ paritySafeActiveSupport n r ∧
        ∃ a ∈ squareAnchorOddActivePrimes n, a < q ∧ a ∣ n ^ 2 + r := by
  classical
  simp only [canonicalRootTail, Finset.mem_filter, mem_canonicalIncidence_iff]
  constructor
  · rintro ⟨⟨hr, hq, hne⟩, hgt⟩
    have hc := mem_paritySafeCoveredCandidates.mpr ⟨hr, ⟨q,hq⟩⟩
    exact ⟨Finset.mem_filter.mpr ⟨hr, (canonicalRoot_gt_iff_rough hc).mp hgt⟩,
      hq, (supportLabel_ne_root_iff_smaller hq).mp hne⟩
  · rintro ⟨hr, hq, hsmall⟩
    have hh := Finset.mem_filter.mp hr
    have hc := mem_paritySafeCoveredCandidates.mpr ⟨hh.1, ⟨q,hq⟩⟩
    exact ⟨⟨hh.1, hq, (supportLabel_ne_root_iff_smaller hq).mpr hsmall⟩,
      (canonicalRoot_gt_iff_rough hc).mpr hh.2⟩

/-- Head-owned seats at one secondary label, before summing any Nat difference. -/
noncomputable def canonicalHeadAtQ (n P q : ℕ) : Finset ℕ :=
  (paritySafeActiveWaveOffsets n q).filter
    (fun r => paritySafeCanonicalSupportPrime n r < q ∧ paritySafeCanonicalSupportPrime n r ≤ P)

noncomputable def canonicalTailAtQ (n P q : ℕ) : Finset ℕ :=
  (paritySafeActiveWaveOffsets n q).filter
    (fun r => paritySafeCanonicalSupportPrime n r < q ∧ P < paritySafeCanonicalSupportPrime n r)

private theorem headAtQ_mem_iff {n P q r : ℕ}
    (hqa : q ∈ squareAnchorOddActivePrimes n) :
    r ∈ canonicalHeadAtQ n P q ↔ (r,q) ∈ canonicalRootHead n P := by
  classical
  simp only [canonicalHeadAtQ, canonicalRootHead, Finset.mem_filter,
    mem_paritySafeActiveWaveOffsets, mem_canonicalIncidence_iff]
  constructor
  · rintro ⟨⟨hr,hq⟩, hlt,hP⟩
    exact ⟨⟨hr,mem_paritySafeActiveSupport_iff_dvd.mpr ⟨hqa,hq⟩,by omega⟩,hP⟩
  · rintro ⟨⟨hr,hq,hne⟩,hP⟩
    exact ⟨⟨hr,(mem_paritySafeActiveSupport_iff_dvd.mp hq).2⟩, canonicalIncidence_root_lt (mem_canonicalIncidence_iff.mpr ⟨hr,hq,hne⟩),hP⟩

/-- Secondary-q regrouping uses the same actual active-prime index as B2. -/
theorem canonicalRootHead_card_eq_secondary_sum (n P : ℕ) :
    (canonicalRootHead n P).card = ∑ q ∈ squareAnchorOddActivePrimes n,
      (canonicalHeadAtQ n P q).card := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.snd) (t := squareAnchorOddActivePrimes n)
    (by intro i hi; exact (paritySafeCanonicalQuotientCoSupportIncidence_packet
      (Finset.mem_filter.mp hi).1).2.2.1)]
  apply Finset.sum_congr rfl
  intro q hq
  symm
  apply Finset.card_bij (fun r _ => (r,q))
  · intro r hr; exact Finset.mem_filter.mpr ⟨(headAtQ_mem_iff hq).mp hr,rfl⟩
  · intro a ha b hb he; exact congrArg Prod.fst he
  · intro i hi
    obtain ⟨hi,he⟩ := Finset.mem_filter.mp hi
    refine ⟨i.1, ?_, Prod.ext rfl he.symm⟩
    apply (headAtQ_mem_iff hq).mpr
    rcases i with ⟨r,s⟩
    dsimp at he ⊢
    subst s
    exact hi

/-- Pointwise head charge is the exact ordered pair sum at that secondary label. -/
theorem canonicalHeadAtQ_card_eq_pair_sum {n P q : ℕ}
    (hq : q ∈ squareAnchorOddActivePrimes n) :
    (canonicalHeadAtQ n P q).card =
      ∑ p ∈ (squareAnchorOddActivePrimes n).filter (fun p => p ≤ P ∧ p < q),
        (canonicalRootPairOffsets n p q).card := by
  classical
  let T := (squareAnchorOddActivePrimes n).filter (fun p => p ≤ P ∧ p < q)
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun r => paritySafeCanonicalSupportPrime n r) (t := T) (by
      intro r hr
      have hinc := (headAtQ_mem_iff hq).mp hr
      have hh := Finset.mem_filter.mp hinc
      have hp := paritySafeCanonicalQuotientCoSupportIncidence_packet hh.1
      exact Finset.mem_filter.mpr ⟨hp.2.1, hh.2, canonicalIncidence_root_lt hh.1⟩)]
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨hpa,hP,hlt⟩ := Finset.mem_filter.mp hp
  congr 1
  ext r
  rw [Finset.mem_filter, headAtQ_mem_iff hq, mem_canonicalRootPairOffsets_iff hpa hq hlt]
  simp only [canonicalRootHead, canonicalRootFiber, Finset.mem_filter]
  constructor
  · rintro ⟨⟨hi,_⟩,he⟩; exact ⟨hi,he⟩
  · rintro ⟨hi,he⟩; exact ⟨⟨hi,he ▸ hP⟩,he⟩

/-- Head and tail at q are disjoint subsets of its actual candidate wave. -/
theorem canonicalHeadAtQ_add_tail_le_cap {n P q : ℕ}
    (hq : q ∈ squareAnchorOddActivePrimes n) :
    (canonicalHeadAtQ n P q).card + (canonicalTailAtQ n P q).card ≤
      paritySafeTwoPrimeWaveUpper n q := by
  classical
  have hd : Disjoint (canonicalHeadAtQ n P q) (canonicalTailAtQ n P q) := by
    apply Finset.disjoint_left.mpr
    intro r hr hs
    have h := (Finset.mem_filter.mp hr).2.2
    have k := (Finset.mem_filter.mp hs).2.2
    omega
  have hsub : canonicalHeadAtQ n P q ∪ canonicalTailAtQ n P q ⊆ paritySafeActiveWaveOffsets n q :=
    Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  rw [← Finset.card_union_of_disjoint hd]
  exact (Finset.card_le_card hsub).trans (paritySafeActiveWave_card_le_twoPrimeWaveUpper hq)

/-- Safe pointwise cancellation. The residual need not equal the excess tail. -/
theorem canonicalTailAtQ_card_le_remaining {n P q : ℕ}
    (hq : q ∈ squareAnchorOddActivePrimes n) :
    (canonicalTailAtQ n P q).card ≤
      paritySafeTwoPrimeWaveUpper n q - (canonicalHeadAtQ n P q).card := by
  have := canonicalHeadAtQ_add_tail_le_cap (P := P) hq
  omega

noncomputable def canonicalRemainingCap (n P : ℕ) : ℕ :=
  paritySafeTwoPrimeIncidenceUpper n - (canonicalRootHead n P).card

/-- Nat subtraction commutes with this sum only after the pointwise cap proof. -/
theorem canonicalRemainingCap_eq_secondary_sum (n P : ℕ) :
    canonicalRemainingCap n P = ∑ q ∈ squareAnchorOddActivePrimes n,
      (paritySafeTwoPrimeWaveUpper n q - (canonicalHeadAtQ n P q).card) := by
  classical
  rw [canonicalRemainingCap, canonicalRootHead_card_eq_secondary_sum,
    paritySafeTwoPrimeIncidenceUpper]
  exact (Finset.sum_tsub_distrib (squareAnchorOddActivePrimes n) (fun q hq => by
    have := canonicalHeadAtQ_add_tail_le_cap (P := P) hq; omega)).symm

/-- Covered seats and upper-cap slack survive cancellation, in addition to tail excess. -/
theorem canonicalRemainingCap_eq_covered_tail_slack (n P : ℕ) :
    canonicalRemainingCap n P = (paritySafeCoveredCandidates n).card +
      (canonicalRootTail n P).card +
      (paritySafeTwoPrimeIncidenceUpper n - paritySafeIncidenceCount n) := by
  have hE := supportExcess_eq_head_add_tail n P
  have hI := paritySafeCoveredCandidates_card_add_supportExcess_eq_incidence n
  have hB := paritySafeIncidenceCount_le_twoPrimeUpper n
  unfold canonicalRemainingCap
  omega

/-- Remaining cap beats A exactly when the original head demand inequality does. -/
theorem remainingCap_lt_candidate_iff (n P : ℕ) :
    canonicalRemainingCap n P < (squareAnchorOddPointCoprimeOffsets n).card ↔
      paritySafeTwoPrimeIncidenceUpper n <
        (squareAnchorOddPointCoprimeOffsets n).card + (canonicalRootHead n P).card := by
  have hE := supportExcess_eq_head_add_tail n P
  have hI := paritySafeCoveredCandidates_card_add_supportExcess_eq_incidence n
  have hB := paritySafeIncidenceCount_le_twoPrimeUpper n
  unfold canonicalRemainingCap
  omega

/-- A rigorous remaining-cap demand consumer. -/
theorem uncovered_nonempty_of_remainingCap_lt {n P : ℕ}
    (h : canonicalRemainingCap n P < (squareAnchorOddPointCoprimeOffsets n).card) :
    (paritySafeUncoveredCandidates n).Nonempty := by
  have he := supportExcess_eq_head_add_tail n P
  apply paritySafeUncovered_nonempty_of_twoPrimeUpper_lt_candidate_add_excess
    (e := (canonicalRootHead n P).card) (by omega)
  exact (remainingCap_lt_candidate_iff n P).mp h

private theorem mem_tail_rough_erased {n P r q : ℕ} :
    (r,q) ∈ canonicalRootTail n P ↔ r ∈ canonicalRoughCandidates n P ∧
      q ∈ (paritySafeActiveSupport n r).erase (paritySafeCanonicalSupportPrime n r) := by
  classical
  rw [mem_canonicalRootTail_iff, Finset.mem_erase]
  constructor
  · rintro ⟨hr,hq,hs⟩
    exact ⟨hr,(supportLabel_ne_root_iff_smaller hq).mpr hs,hq⟩
  · rintro ⟨hr,hne,hq⟩
    exact ⟨hr,hq,(supportLabel_ne_root_iff_smaller hq).mp hne⟩

/-- Tail excess counts secondary labels, not merely the number of rough seats. -/
theorem canonicalRootTail_card_eq_rough_support_sum (n P : ℕ) :
    (canonicalRootTail n P).card = ∑ r ∈ canonicalRoughCandidates n P,
      ((paritySafeActiveSupport n r).card - 1) := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := canonicalRoughCandidates n P)
    (by intro i hi; exact (mem_canonicalRootTail_iff.mp hi).1)]
  apply Finset.sum_congr rfl
  intro r hr
  have he : ((canonicalRootTail n P).filter (fun i => i.1=r)).card =
      ((paritySafeActiveSupport n r).erase (paritySafeCanonicalSupportPrime n r)).card := by
    symm
    apply Finset.card_bij (fun q _ => (r,q))
    · intro q hq; exact Finset.mem_filter.mpr ⟨mem_tail_rough_erased.mpr ⟨hr,hq⟩,rfl⟩
    · intro a ha b hb he; exact congrArg Prod.snd he
    · intro i hi
      obtain ⟨hi,he⟩ := Finset.mem_filter.mp hi
      rcases i with ⟨s,q⟩
      dsimp at he ⊢
      subst s
      exact ⟨q,(mem_tail_rough_erased.mp hi).2,rfl⟩
  rw [he]
  by_cases hne : (paritySafeActiveSupport n r).Nonempty
  · have hp : paritySafeCanonicalSupportPrime n r ∈ paritySafeActiveSupport n r := by
      rw [paritySafeCanonicalSupportPrime,dite_eq_left hne]
      exact Finset.min'_mem _ hne
    exact Finset.card_erase_of_mem hp
  · have he := Finset.not_nonempty_iff_eq_empty.mp hne
    simp [he]

/-- Distinct support labels have a product dividing the positive candidate point. -/
theorem activeSupport_prod_dvd_point {n r : ℕ}
    (hr : r ∈ squareAnchorOddPointCoprimeOffsets n) :
    (∏ q ∈ paritySafeActiveSupport n r, q) ∣ n ^ 2 + r := by
  exact (Finset.prod_dvd_prod_of_subset _ _ id
    (paritySafeActiveSupport_subset_pointPrimeFactors hr)).trans (Nat.prod_primeFactors_dvd _)

/-- Elementary cutoff multiplicity bound, with an independently supplied next-prime lower label. -/
theorem rough_support_pow_le_point {n P r L : ℕ} (hr : r ∈ canonicalRoughCandidates n P)
    (hL : ∀ a ∈ squareAnchorOddActivePrimes n, P < a → L ≤ a) :
    L ^ (paritySafeActiveSupport n r).card ≤ n ^ 2 + r := by
  classical
  have hh := Finset.mem_filter.mp hr
  have hlo : ∀ q ∈ paritySafeActiveSupport n r, L ≤ q := by
    intro q hq
    obtain ⟨hqa,hd⟩ := mem_paritySafeActiveSupport_iff_dvd.mp hq
    apply hL q hqa
    by_contra hn
    exact hh.2 q hqa (by omega) hd
  have hp := Finset.pow_card_le_prod (paritySafeActiveSupport n r) id L hlo
  have hd := activeSupport_prod_dvd_point hh.1
  have hpos : 0 < n ^ 2 + r := by
    have hs := squareOffset_of_mem_squareAnchorOddPointCoprimeOffsets hh.1
    unfold SquareOffset at hs
    omega
  exact hp.trans (Nat.le_of_dvd hpos hd)

/-- A power threshold bounds support cardinality without logarithms. -/
theorem rough_support_card_le {n P r L K : ℕ} (hr : r ∈ canonicalRoughCandidates n P)
    (hL : ∀ a ∈ squareAnchorOddActivePrimes n, P < a → L ≤ a) (hLpos : 1 ≤ L)
    (hpow : n ^ 2 + 2 * n < L ^ (K + 1)) : (paritySafeActiveSupport n r).card ≤ K := by
  have hpoint := rough_support_pow_le_point hr hL
  have hs := squareOffset_of_mem_squareAnchorOddPointCoprimeOffsets (Finset.mem_filter.mp hr).1
  unfold SquareOffset at hs
  by_contra hnot
  have hmono := Nat.pow_le_pow_right hLpos (show K + 1 ≤ (paritySafeActiveSupport n r).card by omega)
  omega

/-- Rough seat count becomes a tail-excess bound only with an explicit multiplicity threshold. -/
theorem canonicalRootTail_card_le_rough_mul {n P L K : ℕ}
    (hL : ∀ a ∈ squareAnchorOddActivePrimes n, P < a → L ≤ a) (hLpos : 1 ≤ L)
    (hpow : n ^ 2 + 2 * n < L ^ (K + 1)) :
    (canonicalRootTail n P).card ≤ (canonicalRoughCandidates n P).card * (K-1) := by
  classical
  rw [canonicalRootTail_card_eq_rough_support_sum]
  have h := Finset.sum_le_sum (fun r hr => Nat.sub_le_sub_right
    (rough_support_card_le hr hL hLpos hpow) 1)
  simpa using h

end DkMath.NumberTheory.Legendre
