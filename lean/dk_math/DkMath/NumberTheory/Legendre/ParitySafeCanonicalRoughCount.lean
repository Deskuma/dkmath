/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.ParitySafeCanonicalRootEleven

#print "file: DkMath.NumberTheory.Legendre.ParitySafeCanonicalRoughCount"

/-! Full rough incidence is a different currency from the erased excess tail.
Its finite wave sum can be compared directly with rough candidate cardinality. -/

namespace DkMath.NumberTheory.Legendre
open scoped BigOperators

/-- Uncovered candidates are exactly the candidates with empty active support. -/
theorem mem_uncovered_iff_no_activeSupport {n r : ℕ} :
    r ∈ paritySafeUncoveredCandidates n ↔ r ∈ squareAnchorOddPointCoprimeOffsets n ∧
      ¬(paritySafeActiveSupport n r).Nonempty := by
  classical
  simp only [paritySafeUncoveredCandidates,Finset.mem_sdiff,mem_paritySafeCoveredCandidates]
  tauto

/-- All supported q-labels on rough seats, including the canonical label. -/
noncomputable def canonicalRoughWave (n P q : ℕ) : Finset ℕ :=
  (canonicalRoughCandidates n P).filter (fun r => q ∣ n ^ 2 + r)

/-- Switching the rough incidence sum to its actual support multiplicities. -/
theorem roughWave_sum_eq_support_sum (n P : ℕ) :
    (∑ q ∈ squareAnchorOddActivePrimes n, (canonicalRoughWave n P q).card) =
      ∑ r ∈ canonicalRoughCandidates n P, (paritySafeActiveSupport n r).card := by
  classical
  have hs (r : ℕ) : paritySafeActiveSupport n r =
      (squareAnchorOddActivePrimes n).filter (fun q => q ∣ n ^ 2 + r) := by
    ext q
    simp only [mem_paritySafeActiveSupport_iff_dvd,Finset.mem_filter]
  simp only [canonicalRoughWave,Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  rw [hs,Finset.card_filter]

/-- The full rough currency is rough covered seats plus erased tail excess. -/
theorem roughWave_sum_eq_covered_add_tail (n P : ℕ) :
    (∑ q ∈ squareAnchorOddActivePrimes n, (canonicalRoughWave n P q).card) =
      ((canonicalRoughCandidates n P).filter (fun r => (paritySafeActiveSupport n r).Nonempty)).card +
      (canonicalRootTail n P).card := by
  classical
  rw [roughWave_sum_eq_support_sum,canonicalRootTail_card_eq_rough_support_sum]
  have he (r : ℕ) : (paritySafeActiveSupport n r).card =
      (if (paritySafeActiveSupport n r).Nonempty then 1 else 0) +
        ((paritySafeActiveSupport n r).card - 1) := by
    by_cases h : (paritySafeActiveSupport n r).Nonempty
    · have hc := Finset.card_pos.mpr h
      simp only [ite_eq_left h]
      omega
    · have hc := Finset.not_nonempty_iff_eq_empty.mp h
      simp [hc]
  rw [Finset.card_filter,← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun r hr => he r)

private theorem uncovered_mem_rough {n P r : ℕ} (hr : r ∈ paritySafeUncoveredCandidates n) :
    r ∈ canonicalRoughCandidates n P := by
  classical
  have hh := mem_uncovered_iff_no_activeSupport.mp hr
  apply Finset.mem_filter.mpr
  refine ⟨hh.1,?_⟩
  intro a ha hP hd
  exact hh.2 ⟨a,mem_paritySafeActiveSupport_iff_dvd.mpr ⟨ha,hd⟩⟩

/-- A rough-incidence bound below rough-seat count forces an uncovered rough seat. -/
theorem uncovered_nonempty_of_roughWave_sum_lt {n P : ℕ}
    (h : (∑ q ∈ squareAnchorOddActivePrimes n, (canonicalRoughWave n P q).card) <
      (canonicalRoughCandidates n P).card) : (paritySafeUncoveredCandidates n).Nonempty := by
  classical
  rw [roughWave_sum_eq_support_sum] at h
  by_contra hn
  have hs : ∀ r ∈ canonicalRoughCandidates n P, 1 ≤ (paritySafeActiveSupport n r).card := by
    intro r hr
    by_contra hc
    have hne : ¬(paritySafeActiveSupport n r).Nonempty := by
      intro he; have := Finset.card_pos.mpr he; omega
    exact hn ⟨r,mem_uncovered_iff_no_activeSupport.mpr ⟨(Finset.mem_filter.mp hr).1,hne⟩⟩
  have hh := Finset.sum_le_sum hs
  simp only [Finset.sum_const,smul_eq_mul,Nat.mul_one] at hh
  omega

/-- Exact cancellation currency: cap slack is retained explicitly. -/
theorem remainingCap_add_rough_eq_candidate_add_roughIncidence (n P : ℕ) :
    canonicalRemainingCap n P + (canonicalRoughCandidates n P).card =
      (squareAnchorOddPointCoprimeOffsets n).card +
      (∑ q ∈ squareAnchorOddActivePrimes n, (canonicalRoughWave n P q).card) +
      (paritySafeTwoPrimeIncidenceUpper n - paritySafeIncidenceCount n) := by
  classical
  let R := canonicalRoughCandidates n P
  have hnot : R.filter (fun r => ¬(paritySafeActiveSupport n r).Nonempty) =
      paritySafeUncoveredCandidates n := by
    ext r
    simp only [Finset.mem_filter,mem_uncovered_iff_no_activeSupport]
    constructor
    · rintro ⟨hr,hn⟩; exact ⟨(Finset.mem_filter.mp hr).1,hn⟩
    · intro hr; exact ⟨uncovered_mem_rough (P := P) (mem_uncovered_iff_no_activeSupport.mpr hr),hr.2⟩
  have hR := Finset.card_filter_add_card_filter_not (s := R)
    (fun r => (paritySafeActiveSupport n r).Nonempty)
  rw [hnot] at hR
  have hA := paritySafeCoveredCandidates_card_add_uncoveredCandidates_card_eq_candidate_card n
  have hI := roughWave_sum_eq_covered_add_tail n P
  have hcap := canonicalRemainingCap_eq_covered_tail_slack n P
  change _ + _ = R.card at hR
  change _ = (R.filter _).card + _ at hI
  dsimp only [R] at hR hI
  omega

/-- The remaining-cap comparison is equivalently a rough currency comparison plus cap slack. -/
theorem remainingCap_lt_iff_rough_currency (n P : ℕ) :
    canonicalRemainingCap n P < (squareAnchorOddPointCoprimeOffsets n).card ↔
      (∑ q ∈ squareAnchorOddActivePrimes n, (canonicalRoughWave n P q).card) +
        (paritySafeTwoPrimeIncidenceUpper n - paritySafeIncidenceCount n) <
          (canonicalRoughCandidates n P).card := by
  have := remainingCap_add_rough_eq_candidate_add_roughIncidence n P
  omega

/-- Multiplicity also bounds full rough incidence, which is distinct from tail excess. -/
theorem roughWave_sum_le_card_mul {n P L K : ℕ}
    (hL : ∀ a ∈ squareAnchorOddActivePrimes n, P < a → L ≤ a) (hLpos : 1 ≤ L)
    (hpow : n ^ 2 + 2 * n < L ^ (K + 1)) :
    (∑ q ∈ squareAnchorOddActivePrimes n, (canonicalRoughWave n P q).card) ≤
      (canonicalRoughCandidates n P).card * K := by
  classical
  rw [roughWave_sum_eq_support_sum]
  have h := Finset.sum_le_sum (fun r hr => rough_support_card_le hr hL hLpos hpow)
  simpa using h

/-- The finite cutoff roughness condition rewritten using the actual initial active labels. -/
theorem roughCriterion_smallCutoff {n P r : ℕ} (hn : n.Prime) (hlt : 11 < n)
    (hP : P ∈ ({3,5,7,11} : Finset ℕ)) :
    (∀ a ∈ squareAnchorOddActivePrimes n, a ≤ P → ¬a ∣ n ^ 2 + r) ↔
      ∀ a ∈ ({3,5,7,11} : Finset ℕ).filter (fun a => a ≤ P), ¬a ∣ n ^ 2 + r := by
  classical
  rw [← activePrimes_smallCutoff hn hlt hP]
  simp only [Finset.mem_filter,and_imp]

/-- Exact three-prime rough-seat object. -/
theorem roughCandidates_seven_eq {n : ℕ} (hn : n.Prime) (hlt : 11 < n) :
    canonicalRoughCandidates n 7 = candidateAvoidThree n 1 := by
  classical
  ext r
  simp only [canonicalRoughCandidates,candidateAvoidThree,paritySafeProductWaveOffsets,Finset.mem_filter,
    roughCriterion_smallCutoff hn hlt (show 7 ∈ ({3,5,7,11}:Finset ℕ) by simp)]
  simp

/-- Exact three-prime rough wave; no canonical minimum appears. -/
theorem roughWave_seven_eq {n q : ℕ} (hn : n.Prime) (hlt : 11 < n) :
    canonicalRoughWave n 7 q = candidateAvoidThree n q := by
  classical
  rw [canonicalRoughWave,roughCandidates_seven_eq hn hlt]
  ext r
  simp [candidateAvoidThree,paritySafeProductWaveOffsets,and_assoc,and_left_comm,and_comm]

/-- An additional coprime divisor commutes with the three-exclusion sieve. -/
theorem candidateAvoidThree_filter_dvd {n a m : ℕ} (ha : Nat.Coprime a m) :
    (candidateAvoidThree n m).filter (fun r => a ∣ n ^ 2 + r) = candidateAvoidThree n (a * m) := by
  classical
  have he : (candidateAvoidThree n m).filter (fun r => a ∣ n ^ 2 + r) =
      ((paritySafeProductWaveOffsets n m).filter (fun r => a ∣ n ^ 2 + r)).filter
        (fun r => ¬3 ∣ n ^ 2 + r ∧ ¬5 ∣ n ^ 2 + r ∧ ¬7 ∣ n ^ 2 + r) := by
    ext r; simp only [candidateAvoidThree,Finset.mem_filter]; tauto
  rw [he,productWave_filter_dvd ha]
  rfl

/-- Cutoff11 adds one exclusion to the already exact three-prime rough object. -/
theorem roughCandidates_eleven_eq {n : ℕ} (hn : n.Prime) (hlt : 11 < n) :
    canonicalRoughCandidates n 11 = (candidateAvoidThree n 1).filter (fun r => ¬11 ∣ n ^ 2 + r) := by
  classical
  ext r
  simp only [canonicalRoughCandidates,candidateAvoidThree,paritySafeProductWaveOffsets,Finset.mem_filter,
    roughCriterion_smallCutoff hn hlt (show 11 ∈ ({3,5,7,11}:Finset ℕ) by simp)]
  simp [and_assoc]

/-- Exact cutoff11 rough wave from a three-exclusion object followed by one subtraction. -/
theorem roughWave_eleven_eq {n q : ℕ} (hn : n.Prime) (hlt : 11 < n) :
    canonicalRoughWave n 11 q = (candidateAvoidThree n q).filter (fun r => ¬11 ∣ n ^ 2 + r) := by
  classical
  rw [canonicalRoughWave,roughCandidates_eleven_eq hn hlt]
  ext r
  simp [candidateAvoidThree,paritySafeProductWaveOffsets,and_assoc,and_left_comm,and_comm]

/-- Exact candidate rough-seat floor count at cutoff11. -/
theorem roughCandidates_eleven_card {n : ℕ} (hn : n.Prime) (hlt : 11 < n) :
    (canonicalRoughCandidates n 11).card =
      primeAnchorAvoidThreeCount n 1 - primeAnchorAvoidThreeCount n 11 := by
  classical
  rw [roughCandidates_eleven_eq hn hlt]
  have he := Finset.card_filter_add_card_filter_not (s := candidateAvoidThree n 1)
    (fun r => 11 ∣ n ^ 2 + r)
  rw [candidateAvoidThree_filter_dvd (by decide : Nat.Coprime 11 1)] at he
  have h3 := candidateAvoidThree_card_eq_count hn (by omega) (by decide : Odd 1)
    (by simp : Nat.Coprime n 1) (by decide) (by decide) (by decide)
  have h11 := primeAnchor_root11 hn hlt
  have hcop : Nat.Coprime n 11 := ((mem_squareAnchorOddActivePrimes.mp h11).1.coprime_iff_not_dvd.mpr
    (mem_squareAnchorOddActivePrimes.mp h11).2.2.1).symm
  have hc11 := candidateAvoidThree_card_eq_count hn (by omega) (by decide : Odd 11)
    hcop (by decide) (by decide) (by decide)
  simp only [Nat.mul_one] at he
  rw [h3,hc11] at he
  omega

/-- Exact secondary-q rough wave floor count, retaining every coprimality correction. -/
theorem roughWave_eleven_card {n q : ℕ} (hn : n.Prime) (hlt : 11 < n)
    (hq : q ∈ squareAnchorOddActivePrimes n) (hqgt : 11 < q) :
    (canonicalRoughWave n 11 q).card = primeAnchorAvoidThreeCount n q -
      primeAnchorAvoidThreeCount n (11 * q) := by
  classical
  rw [roughWave_eleven_eq hn hlt]
  obtain ⟨h3,h5,h7⟩ := primeAnchor_small_roots hn (by omega)
  have h11 := primeAnchor_root11 hn hlt
  have hcq : Nat.Coprime n q := ((mem_squareAnchorOddActivePrimes.mp hq).1.coprime_iff_not_dvd.mpr
    (mem_squareAnchorOddActivePrimes.mp hq).2.2.1).symm
  have hc11 : Nat.Coprime n 11 := ((mem_squareAnchorOddActivePrimes.mp h11).1.coprime_iff_not_dvd.mpr
    (mem_squareAnchorOddActivePrimes.mp h11).2.2.1).symm
  have hoq := (mem_squareAnchorOddActivePrimes.mp hq).1.odd_of_ne_two
    (mem_squareAnchorOddActivePrimes.mp hq).2.2.2
  have he := Finset.card_filter_add_card_filter_not (s := candidateAvoidThree n q)
    (fun r => 11 ∣ n ^ 2 + r)
  rw [candidateAvoidThree_filter_dvd (activePrimes_coprime h11 hq (by omega))] at he
  rw [candidateAvoidThree_card_eq_count hn (by omega) hoq hcq
    (activePrimes_coprime h3 hq (by omega)) (activePrimes_coprime h5 hq (by omega))
    (activePrimes_coprime h7 hq (by omega)),
    candidateAvoidThree_card_eq_count hn (by omega) ((by decide : Odd 11).mul hoq)
      (hc11.mul_right hcq)
      ((activePrimes_coprime h3 h11 (by decide)).mul_right (activePrimes_coprime h3 hq (by omega)))
      ((activePrimes_coprime h5 h11 (by decide)).mul_right (activePrimes_coprime h5 hq (by omega)))
      ((activePrimes_coprime h7 h11 (by decide)).mul_right (activePrimes_coprime h7 hq (by omega)))] at he
  omega

/-- Structural cutoff11 rough incidence sum, with the full active secondary range. -/
noncomputable def primeAnchorRoughElevenIncidenceCount (n : ℕ) : ℕ :=
  ∑ q ∈ (squareAnchorOddActivePrimes n).filter (fun q => 11 < q),
    (primeAnchorAvoidThreeCount n q - primeAnchorAvoidThreeCount n (11 * q))

/-- The structural formula computes only the rough incidence, not whole I or E. -/
theorem roughWave_eleven_sum_eq_count {n : ℕ} (hn : n.Prime) (hlt : 11 < n) :
    (∑ q ∈ squareAnchorOddActivePrimes n, (canonicalRoughWave n 11 q).card) =
      primeAnchorRoughElevenIncidenceCount n := by
  classical
  unfold primeAnchorRoughElevenIncidenceCount
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hgt : 11 < q
  · rw [ite_eq_left hgt,roughWave_eleven_card hn hlt hq hgt]
  · rw [ite_eq_right hgt]
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro r hr
    obtain ⟨hr,hd⟩ := Finset.mem_filter.mp hr
    exact (Finset.mem_filter.mp hr).2 q hq (by omega) hd

/-- A direct rough currency consumer; no head or whole-excess evaluation is needed. -/
theorem prime_squareCell_of_roughEleven_count {n : ℕ} (hn : n.Prime) (hlt : 11 < n)
    (h : primeAnchorRoughElevenIncidenceCount n <
      primeAnchorAvoidThreeCount n 1 - primeAnchorAvoidThreeCount n 11) :
    ∃ p, p.Prime ∧ SquareCell n p := by
  apply exists_prime_squareCell_of_paritySafeUncoveredCandidates_nonempty hn.pos
  apply uncovered_nonempty_of_roughWave_sum_lt (P := 11)
  rwa [roughWave_eleven_sum_eq_count hn hlt,roughCandidates_eleven_card hn hlt]

end DkMath.NumberTheory.Legendre
