/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.ParitySafeSqrtRoughMoments
import DkMath.NumberTheory.Legendre.PairOverlap

#print "file: DkMath.NumberTheory.Legendre.ParitySafeSqrtRoughProductWaves"

namespace DkMath.NumberTheory.Legendre
open scoped BigOperators
open Internal

noncomputable def roughActiveLabels (n P : ℕ) : Finset ℕ :=
  (squareAnchorOddActivePrimes n).filter (fun p => P < p)

theorem rough_support_subset_labels {n P r : ℕ}
    (hr : r ∈ canonicalRoughCandidates n P) :
    paritySafeActiveSupport n r ⊆ roughActiveLabels n P := by
  intro p hp
  obtain ⟨ha, hd⟩ := mem_paritySafeActiveSupport_iff_dvd.mp hp
  refine Finset.mem_filter.mpr ⟨ha, ?_⟩
  by_contra h
  exact (Finset.mem_filter.mp hr).2 p ha (by omega) hd

noncomputable def roughPairs (n P : ℕ) : Finset (ℕ × ℕ) :=
  upperPairs (roughActiveLabels n P)

noncomputable def roughTriples (n P : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  upperTriples (roughActiveLabels n P)

@[simp] theorem mem_roughPairs {n P p q : ℕ} :
    (p, q) ∈ roughPairs n P ↔ p ∈ roughActiveLabels n P ∧
      q ∈ roughActiveLabels n P ∧ p < q := by
  simp only [roughPairs, upperPairs, Finset.mem_filter, Finset.mem_offDiag]
  constructor
  · intro h; exact ⟨h.1.1, h.1.2.1, h.2⟩
  · rintro ⟨hp, hq, he⟩; exact ⟨⟨hp, hq, he.ne⟩, he⟩

@[simp] theorem mem_roughTriples {n P p q s : ℕ} :
    (p, q, s) ∈ roughTriples n P ↔ p ∈ roughActiveLabels n P ∧
      q ∈ roughActiveLabels n P ∧ s ∈ roughActiveLabels n P ∧ p < q ∧ q < s :=
  mem_upperTriples

noncomputable def roughPairIncidences (n P : ℕ) : Finset (ℕ × (ℕ × ℕ)) :=
  ((canonicalRoughCandidates n P).product (roughPairs n P)).filter
    (fun i => i.2 ∈ upperPairs (paritySafeActiveSupport n i.1))

noncomputable def roughTripleIncidences (n P : ℕ) : Finset (ℕ × (ℕ × ℕ × ℕ)) :=
  ((canonicalRoughCandidates n P).product (roughTriples n P)).filter
    (fun i => i.2 ∈ upperTriples (paritySafeActiveSupport n i.1))

theorem roughPairIncidences_card (n P : ℕ) :
    (roughPairIncidences n P).card = roughPairMoment n P := by
  classical
  have hsub : ∀ r ∈ canonicalRoughCandidates n P,
      upperPairs (paritySafeActiveSupport n r) ⊆ roughPairs n P := by
    intro r hr a ha
    rcases a with ⟨p, q⟩
    have ha' := Finset.mem_filter.mp ha
    have hd := Finset.mem_offDiag.mp ha'.1
    exact mem_roughPairs.mpr ⟨rough_support_subset_labels hr hd.1,
      rough_support_subset_labels hr hd.2.1, ha'.2⟩
  calc
    _ = ∑ r ∈ canonicalRoughCandidates n P, (upperPairs (paritySafeActiveSupport n r)).card :=
      card_product_filter_mem _ _ _ hsub
    _ = _ := Finset.sum_congr rfl (fun r _ => card_upperPairs_eq_choose _)

theorem sqrt_roughTripleIncidences_card (n : ℕ) :
    (roughTripleIncidences n (Nat.sqrt n)).card = roughTripleMoment n (Nat.sqrt n) := by
  classical
  have hsub : ∀ r ∈ canonicalRoughCandidates n (Nat.sqrt n),
      upperTriples (paritySafeActiveSupport n r) ⊆ roughTriples n (Nat.sqrt n) := by
    intro r hr a ha
    rcases a with ⟨p, q, s⟩
    obtain ⟨hp, hq, hs, hpq, hqs⟩ := mem_upperTriples.mp ha
    exact mem_roughTriples.mpr ⟨rough_support_subset_labels hr hp,
      rough_support_subset_labels hr hq, rough_support_subset_labels hr hs, hpq, hqs⟩
  calc
    _ = ∑ r ∈ canonicalRoughCandidates n (Nat.sqrt n), (upperTriples (paritySafeActiveSupport n r)).card :=
      card_product_filter_mem _ _ _ hsub
    _ = _ := Finset.sum_congr rfl (fun r hr =>
      card_upperTriples_eq_choose_of_le_three (sqrtCutoff_support_card_le_three hr))

noncomputable def roughPairWave (n P p q : ℕ) : Finset ℕ :=
  (canonicalRoughCandidates n P).filter (fun r => p * q ∣ n ^ 2 + r)

noncomputable def roughTripleWave (n P p q s : ℕ) : Finset ℕ :=
  (canonicalRoughCandidates n P).filter (fun r => p * q * s ∣ n ^ 2 + r)

theorem active_pair_coprime {n P p q : ℕ} (h : (p, q) ∈ roughPairs n P) : Nat.Coprime p q := by
  obtain ⟨hp, hq, hlt⟩ := mem_roughPairs.mp h
  exact (mem_squareAnchorOddActivePrimes.mp (Finset.mem_filter.mp hp).1).1.coprime_iff_not_dvd.mpr
    (by intro hd
        have he := ((mem_squareAnchorOddActivePrimes.mp (Finset.mem_filter.mp hq).1).1.dvd_iff_eq
          (mem_squareAnchorOddActivePrimes.mp (Finset.mem_filter.mp hp).1).1.ne_one).mp hd
        omega)

theorem roughPair_support_iff_product {n P p q r : ℕ} (h : (p, q) ∈ roughPairs n P) :
    (p, q) ∈ upperPairs (paritySafeActiveSupport n r) ↔ p * q ∣ n ^ 2 + r := by
  obtain ⟨hp, hq, hlt⟩ := mem_roughPairs.mp h
  have hp' := (Finset.mem_filter.mp hp).1
  have hq' := (Finset.mem_filter.mp hq).1
  simp only [upperPairs, Finset.mem_filter, Finset.mem_offDiag, mem_paritySafeActiveSupport_iff_dvd]
  have hne := hlt.ne
  have hdiff : p * q ∣ n ^ 2 + r ↔ p ∣ n ^ 2 + r ∧ q ∣ n ^ 2 + r := by
    constructor
    · intro hd; exact ⟨(dvd_mul_right p q).trans hd, (dvd_mul_left q p).trans hd⟩
    · rintro ⟨hp, hq⟩; exact (active_pair_coprime h).mul_dvd_of_dvd_of_dvd hp hq
  rw [hdiff]
  tauto

theorem roughTriple_support_iff_product {n P p q s r : ℕ}
    (h : (p, q, s) ∈ roughTriples n P) :
    (p, q, s) ∈ upperTriples (paritySafeActiveSupport n r) ↔ p * q * s ∣ n ^ 2 + r := by
  obtain ⟨hp, hq, hs, hpq, hqs⟩ := mem_roughTriples.mp h
  have hp' := (Finset.mem_filter.mp hp).1
  have hq' := (Finset.mem_filter.mp hq).1
  have hs' := (Finset.mem_filter.mp hs).1
  have hpq' := active_pair_coprime (mem_roughPairs.mpr ⟨hp, hq, hpq⟩)
  have hps' := active_pair_coprime (mem_roughPairs.mpr ⟨hp, hs, hpq.trans hqs⟩)
  have hqs' := active_pair_coprime (mem_roughPairs.mpr ⟨hq, hs, hqs⟩)
  have hdiff : p * q * s ∣ n ^ 2 + r ↔ p ∣ n ^ 2 + r ∧ q ∣ n ^ 2 + r ∧ s ∣ n ^ 2 + r := by
    constructor
    · intro hd
      have hd' := (dvd_mul_right (p * q) s).trans hd
      exact ⟨(dvd_mul_right p q).trans hd', (dvd_mul_left q p).trans hd',
        (dvd_mul_left s (p * q)).trans hd⟩
    · rintro ⟨hp, hq, hs⟩
      exact (hps'.mul_left hqs').mul_dvd_of_dvd_of_dvd
        (hpq'.mul_dvd_of_dvd_of_dvd hp hq) hs
  rw [hdiff]
  simp only [mem_upperTriples, mem_paritySafeActiveSupport_iff_dvd]
  tauto

theorem roughPair_fiber_eq_wave {n P p q : ℕ} (h : (p, q) ∈ roughPairs n P) :
    (canonicalRoughCandidates n P).filter
      (fun r => (p, q) ∈ upperPairs (paritySafeActiveSupport n r)) = roughPairWave n P p q := by
  ext r
  simp only [roughPairWave, Finset.mem_filter, roughPair_support_iff_product h]

theorem roughTriple_fiber_eq_wave {n P p q s : ℕ} (h : (p, q, s) ∈ roughTriples n P) :
    (canonicalRoughCandidates n P).filter
      (fun r => (p, q, s) ∈ upperTriples (paritySafeActiveSupport n r)) = roughTripleWave n P p q s := by
  ext r
  simp only [roughTripleWave, Finset.mem_filter, roughTriple_support_iff_product h]

theorem roughPairMoment_eq_wave_sum (n P : ℕ) :
    roughPairMoment n P = ∑ a ∈ roughPairs n P, (roughPairWave n P a.1 a.2).card := by
  classical
  rw [← roughPairIncidences_card, roughPairIncidences, Finset.card_filter]
  trans ∑ a ∈ roughPairs n P, ∑ r ∈ canonicalRoughCandidates n P,
    if a ∈ upperPairs (paritySafeActiveSupport n r) then (1:ℕ) else 0
  · exact Finset.sum_product_right' (canonicalRoughCandidates n P) (roughPairs n P)
      (fun r a => if a ∈ upperPairs (paritySafeActiveSupport n r) then (1 : ℕ) else 0)
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_boole, roughPair_fiber_eq_wave ha]
  rfl

theorem sqrt_roughTripleMoment_eq_wave_sum (n : ℕ) :
    roughTripleMoment n (Nat.sqrt n) =
      ∑ a ∈ roughTriples n (Nat.sqrt n), (roughTripleWave n (Nat.sqrt n) a.1 a.2.1 a.2.2).card := by
  classical
  rw [← sqrt_roughTripleIncidences_card, roughTripleIncidences, Finset.card_filter]
  trans ∑ a ∈ roughTriples n (Nat.sqrt n), ∑ r ∈ canonicalRoughCandidates n (Nat.sqrt n),
    if a ∈ upperTriples (paritySafeActiveSupport n r) then (1:ℕ) else 0
  · exact Finset.sum_product_right' (canonicalRoughCandidates n (Nat.sqrt n))
      (roughTriples n (Nat.sqrt n))
      (fun r a => if a ∈ upperTriples (paritySafeActiveSupport n r) then (1 : ℕ) else 0)
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_boole, roughTriple_fiber_eq_wave ha]
  rfl

theorem sqrt_successor_square_gt (n : ℕ) : n < (Nat.sqrt n + 1) ^ 2 := by
  have := Nat.succ_le_succ_sqrt' n
  omega

theorem sqrt_roughPair_product_gt {n p q : ℕ}
    (h : (p, q) ∈ roughPairs n (Nat.sqrt n)) : n < p * q := by
  obtain ⟨hp, hq, _⟩ := mem_roughPairs.mp h
  have hlp := (Finset.mem_filter.mp hp).2
  have hlq := (Finset.mem_filter.mp hq).2
  have hm := Nat.mul_le_mul (show Nat.sqrt n + 1 ≤ p by omega)
    (show Nat.sqrt n + 1 ≤ q by omega)
  have := sqrt_successor_square_gt n
  nlinarith

theorem sqrt_roughTriple_product_gt {n p q s : ℕ}
    (h : (p, q, s) ∈ roughTriples n (Nat.sqrt n)) : 2 * n < p * q * s := by
  obtain ⟨hp, hq, hs, hpq, hqs⟩ := mem_roughTriples.mp h
  have hpair := sqrt_roughPair_product_gt (mem_roughPairs.mpr ⟨hp, hq, hpq⟩)
  have hsp := (mem_squareAnchorOddActivePrimes.mp (Finset.mem_filter.mp hs).1).1.two_le
  have hm := Nat.mul_le_mul_left (p * q) hsp
  nlinarith

theorem roughPairWave_subset_raw (n P p q : ℕ) :
    roughPairWave n P p q ⊆ squareWaveOffsets n (p * q) := by
  intro r hr
  obtain ⟨hr, hd⟩ := Finset.mem_filter.mp hr
  exact mem_squareWaveOffsets.mpr ⟨squareOffset_of_mem_squareAnchorOddPointCoprimeOffsets
    (Finset.mem_filter.mp hr).1, hd⟩

theorem roughTripleWave_subset_raw (n P p q s : ℕ) :
    roughTripleWave n P p q s ⊆ squareWaveOffsets n (p * q * s) := by
  intro r hr
  obtain ⟨hr, hd⟩ := Finset.mem_filter.mp hr
  exact mem_squareWaveOffsets.mpr ⟨squareOffset_of_mem_squareAnchorOddPointCoprimeOffsets
    (Finset.mem_filter.mp hr).1, hd⟩

theorem sqrt_roughPair_raw_card_le_two {n p q : ℕ}
    (h : (p, q) ∈ roughPairs n (Nat.sqrt n)) : (squareWaveOffsets n (p * q)).card ≤ 2 := by
  have hgt := sqrt_roughPair_product_gt h
  have hpos : 0 < p * q := by omega
  rw [card_squareWaveOffsets_eq_div_add_carry hpos]
  have hcarry := squareWaveCarry_le_one (n:=n) hpos
  have hd : 2 * n/(p * q) < 2 := (Nat.div_lt_iff_lt_mul hpos).mpr (by omega)
  omega

theorem sqrt_roughTriple_raw_card_le_one {n p q s : ℕ}
    (h : (p, q, s) ∈ roughTriples n (Nat.sqrt n)) :
    (squareWaveOffsets n (p * q * s)).card ≤ 1 := by
  have hgt := sqrt_roughTriple_product_gt h
  exact card_squareWaveOffsets_le_one_of_two_mul_lt_modulus (by omega) hgt

theorem sqrt_roughPairWave_card_le_two {n p q : ℕ}
    (h : (p, q) ∈ roughPairs n (Nat.sqrt n)) :
    (roughPairWave n (Nat.sqrt n) p q).card ≤ 2 :=
  (Finset.card_le_card (roughPairWave_subset_raw ..)).trans (sqrt_roughPair_raw_card_le_two h)

theorem sqrt_roughTripleWave_card_le_one {n p q s : ℕ}
    (h : (p, q, s) ∈ roughTriples n (Nat.sqrt n)) :
    (roughTripleWave n (Nat.sqrt n) p q s).card ≤ 1 :=
  (Finset.card_le_card (roughTripleWave_subset_raw ..)).trans (sqrt_roughTriple_raw_card_le_one h)

theorem roughPairWave_eq_candidate_product_filter (n P p q : ℕ) :
    roughPairWave n P p q = (paritySafeProductWaveOffsets n (p * q)).filter
      (fun r => ∀ a ∈ squareAnchorOddActivePrimes n, a ≤ P → ¬a ∣ n ^ 2 + r) := by
  ext r
  simp only [roughPairWave, canonicalRoughCandidates, paritySafeProductWaveOffsets, Finset.mem_filter]
  tauto

theorem roughTripleWave_eq_candidate_product_filter (n P p q s : ℕ) :
    roughTripleWave n P p q s = (paritySafeProductWaveOffsets n (p * q * s)).filter
      (fun r => ∀ a ∈ squareAnchorOddActivePrimes n, a ≤ P → ¬a ∣ n ^ 2 + r) := by
  ext r
  simp only [roughTripleWave, canonicalRoughCandidates, paritySafeProductWaveOffsets, Finset.mem_filter]
  tauto

theorem primeAnchor_roughPairWave_card_le_floor {n P p q : ℕ} (hn : n.Prime) (hne : n ≠ 2)
    (h : (p, q) ∈ roughPairs n P) :
    (roughPairWave n P p q).card ≤ primeAnchorProductWaveCount n (p * q) := by
  obtain ⟨hp, hq, _⟩ := mem_roughPairs.mp h
  have hpA := activePrime_reducedResidue_packet (Finset.mem_filter.mp hp).1
  have hqA := activePrime_reducedResidue_packet (Finset.mem_filter.mp hq).1
  have hodd := (hpA.1.odd_of_ne_two hpA.2.2.2.1).mul (hqA.1.odd_of_ne_two hqA.2.2.2.1)
  have hcop := (hpA.2.2.2.2.mul_right hqA.2.2.2.2).coprime_dvd_left (dvd_mul_left n 2)
  rw [← paritySafeProductWave_card_eq_count hn (hn.odd_of_ne_two hne) hodd hcop,
    roughPairWave_eq_candidate_product_filter]
  exact Finset.card_le_card (Finset.filter_subset ..)

theorem primeAnchor_roughTripleWave_card_le_floor {n P p q s : ℕ} (hn : n.Prime) (hne : n ≠ 2)
    (h : (p, q, s) ∈ roughTriples n P) :
    (roughTripleWave n P p q s).card ≤ primeAnchorProductWaveCount n (p * q * s) := by
  obtain ⟨hp, hq, hs, _, _⟩ := mem_roughTriples.mp h
  have hpA := activePrime_reducedResidue_packet (Finset.mem_filter.mp hp).1
  have hqA := activePrime_reducedResidue_packet (Finset.mem_filter.mp hq).1
  have hsA := activePrime_reducedResidue_packet (Finset.mem_filter.mp hs).1
  have hodd := ((hpA.1.odd_of_ne_two hpA.2.2.2.1).mul
    (hqA.1.odd_of_ne_two hqA.2.2.2.1)).mul (hsA.1.odd_of_ne_two hsA.2.2.2.1)
  have hcop := ((hpA.2.2.2.2.mul_right hqA.2.2.2.2).mul_right hsA.2.2.2.2).coprime_dvd_left
    (dvd_mul_left n 2)
  rw [← paritySafeProductWave_card_eq_count hn (hn.odd_of_ne_two hne) hodd hcop,
    roughTripleWave_eq_candidate_product_filter]
  exact Finset.card_le_card (Finset.filter_subset ..)

theorem prime_squareCell_of_sqrt_product_moment {n : ℕ} (hn : 0 < n)
    (h : (∑ q ∈ squareAnchorOddActivePrimes n, (canonicalRoughWave n (Nat.sqrt n) q).card) +
      (∑ a ∈ roughTriples n (Nat.sqrt n),
        (roughTripleWave n (Nat.sqrt n) a.1 a.2.1 a.2.2).card) <
      (canonicalRoughCandidates n (Nat.sqrt n)).card +
        (∑ a ∈ roughPairs n (Nat.sqrt n), (roughPairWave n (Nat.sqrt n) a.1 a.2).card)) :
    ∃ p, p.Prime ∧ SquareCell n p := by
  apply prime_squareCell_of_sqrt_moment hn
  simpa only [roughPairMoment_eq_wave_sum, sqrt_roughTripleMoment_eq_wave_sum] using h

/-- Parity doubles the product-wave separation; an odd modulus above n permits only one candidate. -/
theorem candidateProductWave_card_le_one_of_anchor_lt {n m : ℕ} (hm : Odd m) (hgt : n < m) :
    (paritySafeProductWaveOffsets n m).card ≤ 1 := by
  have hsep : ∀ r ∈ paritySafeProductWaveOffsets n m,
      ∀ s ∈ paritySafeProductWaveOffsets n m, r < s → False := by
    intro r hr s hs hrs
    obtain ⟨hr, hdr⟩ := Finset.mem_filter.mp hr
    obtain ⟨hs, hds⟩ := Finset.mem_filter.mp hs
    have hro := (mem_squareAnchorOddPointCoprimeOffsets.mp hr).2
    have hso := (mem_squareAnchorOddPointCoprimeOffsets.mp hs).2
    have he : Even (s - r) := by
      simpa only [Nat.add_sub_add_left] using Nat.Odd.sub_odd hso hro
    have hmd : m ∣ s - r := by
      simpa only [Nat.add_sub_add_left] using Nat.dvd_sub hds hdr
    have htwo : 2 ∣ s - r := even_iff_two_dvd.mp he
    have hbig := (Nat.coprime_two_right.mpr hm).mul_dvd_of_dvd_of_dvd hmd htwo
    have hle := Nat.le_of_dvd (show 0 < s - r by omega) hbig
    have hbound := squareOffset_of_mem_squareAnchorOddPointCoprimeOffsets hs
    dsimp only [SquareOffset] at hbound
    omega
  apply Finset.card_le_one.mpr
  intro r hr s hs
  rcases lt_trichotomy r s with h | h | h
  · exact False.elim (hsep r hr s hs h)
  · exact h
  · exact False.elim (hsep s hs r hr h)

/-- The actual parity-safe rough pair bound is one, sharper than the raw bound two. -/
theorem sqrt_roughPairWave_card_le_one {n p q : ℕ}
    (h : (p, q) ∈ roughPairs n (Nat.sqrt n)) :
    (roughPairWave n (Nat.sqrt n) p q).card ≤ 1 := by
  obtain ⟨hp, hq, _⟩ := mem_roughPairs.mp h
  have hpA := mem_squareAnchorOddActivePrimes.mp (Finset.mem_filter.mp hp).1
  have hqA := mem_squareAnchorOddActivePrimes.mp (Finset.mem_filter.mp hq).1
  have hodd := (hpA.1.odd_of_ne_two hpA.2.2.2).mul (hqA.1.odd_of_ne_two hqA.2.2.2)
  rw [roughPairWave_eq_candidate_product_filter]
  exact (Finset.card_le_card (Finset.filter_subset ..)).trans
    (candidateProductWave_card_le_one_of_anchor_lt hodd (sqrt_roughPair_product_gt h))

end DkMath.NumberTheory.Legendre
