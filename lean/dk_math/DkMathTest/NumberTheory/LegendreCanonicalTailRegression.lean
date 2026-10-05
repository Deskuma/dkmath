/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.ParitySafePrimeAnchorCap
import DkMathTest.NumberTheory.LegendreBlockLocalization

#print "file: DkMathTest.NumberTheory.LegendreCanonicalTailRegression"

namespace DkMathTest.LegendreCanonicalTailRegression
open DkMath.NumberTheory.Legendre DkMathTest.LegendreBlockLocalization

private theorem support_finite (n r : ℕ) :
    paritySafeActiveSupport n r = ((Finset.range (n+1)).filter
      (fun q => q.Prime ∧ ¬q ∣ n ∧ q ≠ 2)).filter (fun q => q ∣ n ^ 2 + r) := by
  ext q
  simp only [mem_paritySafeActiveSupport_iff_dvd, oddActive_eq_filter_range,
    Finset.mem_filter]

/-- The first active shell: the bare rough-support object includes its erased canonical root. -/
theorem erased_root_counterexample :
    (5 : ℕ) ∈ canonicalRoughCandidates 4 0 ∧ 3 ∈ paritySafeActiveSupport 4 5 ∧
      (5,3) ∉ canonicalRootTail 4 0 := by
  have hs : paritySafeActiveSupport 4 5 = {3} := by
    rw [support_finite]; decide +kernel
  have hroot : paritySafeCanonicalSupportPrime 4 5 = 3 := by
    apply (canonicalSupport_eq_iff_minimal (by decide : 0 < 3)).mpr
    simp only [hs, Finset.mem_singleton]
    exact ⟨trivial, by intro a ha; omega⟩
  have hr : (5 : ℕ) ∈ canonicalRoughCandidates 4 0 := by
    apply Finset.mem_filter.mpr
    refine ⟨?_, ?_⟩
    · rw [candidate_eq_filter_Icc]; decide +kernel
    · intro a ha hle
      have := (mem_squareAnchorOddActivePrimes.mp ha).1.two_le
      omega
  refine ⟨hr, by simp [hs], ?_⟩
  simp only [canonicalRootTail, Finset.mem_filter, mem_canonicalIncidence_iff, hroot]
  tauto

/-- Empty support gives default root0, although the candidate is rough at cutoff0. -/
theorem empty_support_counterexample :
    (1 : ℕ) ∈ canonicalRoughCandidates 4 0 ∧ paritySafeActiveSupport 4 1 = ∅ ∧
      paritySafeCanonicalSupportPrime 4 1 = 0 ∧ ¬0 < paritySafeCanonicalSupportPrime 4 1 := by
  have hs : paritySafeActiveSupport 4 1 = ∅ := by
    rw [support_finite]; decide +kernel
  have hroot : paritySafeCanonicalSupportPrime 4 1 = 0 := by
    simp [paritySafeCanonicalSupportPrime, hs]
  refine ⟨?_, hs, hroot, by omega⟩
  apply Finset.mem_filter.mpr
  refine ⟨?_, ?_⟩
  · rw [candidate_eq_filter_Icc]; decide +kernel
  · intro a ha hle
    have := (mem_squareAnchorOddActivePrimes.mp ha).1.two_le
    omega

/-- Residual cap at q3 retains a root-owned covered seat, so it is not the tail at q3. -/
theorem termwise_cancellation_counterexample :
    (canonicalHeadAtQ 4 3 3).card = 0 ∧ (canonicalTailAtQ 4 3 3).card = 0 ∧
      paritySafeTwoPrimeWaveUpper 4 3 = 1 ∧
      paritySafeTwoPrimeWaveUpper 4 3 - (canonicalHeadAtQ 4 3 3).card ≠
        (canonicalTailAtQ 4 3 3).card := by
  have hqa : 3 ∈ squareAnchorOddActivePrimes 4 := by
    rw [mem_squareAnchorOddActivePrimes]; decide
  have hroot : ∀ r ∈ paritySafeActiveWaveOffsets 4 3,
      paritySafeCanonicalSupportPrime 4 r = 3 := by
    intro r hr
    apply (canonicalSupport_eq_iff_minimal (by decide : 0 < 3)).mpr
    refine ⟨mem_paritySafeActiveSupport_iff_dvd.mpr
      ⟨hqa, (mem_paritySafeActiveWaveOffsets.mp hr).2⟩, ?_⟩
    intro a ha
    have := (mem_squareAnchorOddActivePrimes.mp
      (mem_paritySafeActiveSupport_iff_dvd.mp ha).1).1.two_le
    have := (mem_squareAnchorOddActivePrimes.mp
      (mem_paritySafeActiveSupport_iff_dvd.mp ha).1).2.2.2
    omega
  have hh : canonicalHeadAtQ 4 3 3 = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro r hr
    obtain ⟨hw,hlt,_⟩ := Finset.mem_filter.mp hr
    have := hroot r hw
    omega
  have ht : canonicalTailAtQ 4 3 3 = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro r hr
    obtain ⟨hw,hlt,_⟩ := Finset.mem_filter.mp hr
    have := hroot r hw
    omega
  have hcap : paritySafeTwoPrimeWaveUpper 4 3 = 1 := by decide +kernel
  simp only [hh,ht,Finset.card_empty,hcap]
  decide

/-- The first prime anchor above11 with a 3-rough seat carrying three supported labels. -/
theorem rough_seat_multiplicity_counterexample :
    (24 : ℕ) ∈ canonicalRoughCandidates 19 3 ∧
    paritySafeActiveSupport 19 24 = {5,7,11} ∧
    (({5,7,11}:Finset ℕ).card - 1) = 2 := by
  have hs : paritySafeActiveSupport 19 24 = {5,7,11} := by
    rw [support_finite]; decide +kernel
  refine ⟨?_, hs, by decide⟩
  apply Finset.mem_filter.mpr
  refine ⟨?_, ?_⟩
  · rw [candidate_eq_filter_Icc]; decide +kernel
  · intro a ha hle hd
    have hmem : a ∈ paritySafeActiveSupport 19 24 :=
      mem_paritySafeActiveSupport_iff_dvd.mpr ⟨ha,hd⟩
    rw [hs] at hmem
    simp only [Finset.mem_insert,Finset.mem_singleton] at hmem
    omega

/-- Clipped sequential Nat subtraction overcounts a triply excluded singleton. -/
theorem sequential_three_exclusion_counterexample :
    ((({0}:Finset ℕ).filter (fun _ => ¬True ∧ ¬True ∧ ¬True)).card = 0) ∧
    (1 : ℕ) + 3 - (3 + 1) = 0 ∧
    (1 : ℕ) - 1 - 1 - 1 + 1 + 1 + 1 - 1 = 2 := by
  decide +kernel

/-- The old generic root11 union provider has exactly this candidate floor normal form. -/
theorem root11_sieve_eq_floor_union {n : ℕ} (hn : n.Prime) (hlt : 11 < n) :
    canonicalRootSieveLower n 11 =
      ∑ q ∈ (squareAnchorOddActivePrimes n).filter (fun q => 11 < q),
        (primeAnchorProductWaveCount n (11 * q) -
          (primeAnchorProductWaveCount n (33 * q) + primeAnchorProductWaveCount n (55 * q) +
            primeAnchorProductWaveCount n (77 * q))) := by
  classical
  obtain ⟨h3,h5,h7⟩ := primeAnchor_small_roots hn (by omega)
  have h11 := primeAnchor_root11 hn hlt
  have hsmall : (squareAnchorOddActivePrimes n).filter (fun a => a < 11) = {3,5,7} := by
    ext a
    simp only [Finset.mem_filter,Finset.mem_insert,Finset.mem_singleton]
    constructor
    · rintro ⟨ha,hbound⟩; exact activePrime_below_eleven ha hbound
    · rintro (rfl | rfl | rfl)
      · exact ⟨h3,by decide⟩
      · exact ⟨h5,by decide⟩
      · exact ⟨h7,by decide⟩
  unfold canonicalRootSieveLower
  apply Finset.sum_congr rfl
  intro q hq
  obtain ⟨hqa,hgt⟩ := Finset.mem_filter.mp hq
  have hqOdd := (mem_squareAnchorOddActivePrimes.mp hqa).1.odd_of_ne_two
    (mem_squareAnchorOddActivePrimes.mp hqa).2.2.2
  have hnOdd := hn.odd_of_ne_two (by omega)
  have hcopn (a : ℕ) (ha : a ∈ squareAnchorOddActivePrimes n) : Nat.Coprime n a :=
    ((mem_squareAnchorOddActivePrimes.mp ha).1.coprime_iff_not_dvd.mpr
      (mem_squareAnchorOddActivePrimes.mp ha).2.2.1).symm
  have hcop (a : ℕ) (ha : a ∈ squareAnchorOddActivePrimes n) (haSmall : a < 11) :
      Nat.Coprime a (11 * q) :=
    (activePrimes_coprime ha h11 (by omega)).mul_right
      (activePrimes_coprime ha hqa (by omega))
  rw [hsmall]
  simp only [Finset.sum_insert,Finset.sum_singleton,Finset.mem_insert,Finset.mem_singleton,
    show (3:ℕ) ≠ 5 by decide,show (3:ℕ) ≠ 7 by decide,show (5:ℕ) ≠ 7 by decide,
    false_or,not_false_eq_true]
  rw [productWave_filter_dvd (hcop 3 h3 (by decide)),
    productWave_filter_dvd (hcop 5 h5 (by decide)),
    productWave_filter_dvd (hcop 7 h7 (by decide))]
  have hbase : Nat.Coprime n (11 * q) := (hcopn 11 h11).mul_right (hcopn q hqa)
  have hbaseOdd : Odd (11 * q) := (by decide : Odd 11).mul hqOdd
  rw [paritySafeProductWave_card_eq_count hn hnOdd hbaseOdd hbase,
    paritySafeProductWave_card_eq_count hn hnOdd ((by decide : Odd 3).mul hbaseOdd)
      ((hcopn 3 h3).mul_right hbase),
    paritySafeProductWave_card_eq_count hn hnOdd ((by decide : Odd 5).mul hbaseOdd)
      ((hcopn 5 h5).mul_right hbase),
    paritySafeProductWave_card_eq_count hn hnOdd ((by decide : Odd 7).mul hbaseOdd)
      ((hcopn 7 h7).mul_right hbase)]
  simp only [← Nat.mul_assoc, Nat.add_assoc]

/-- Cutoff3 candidate rough-seat count in exact product-wave floor form. -/
theorem rough_seats_three_floor {n : ℕ} (hn : n.Prime) (hlt : 11 < n) :
    (canonicalRoughCandidates n 3).card =
      primeAnchorProductWaveCount n 1 - primeAnchorProductWaveCount n 3 := by
  classical
  have hf : ({3,5,7,11}:Finset ℕ).filter (fun a => a ≤ 3) = {3} := by decide
  have hc (r : ℕ) : (∀ a ∈ squareAnchorOddActivePrimes n, a ≤ 3 → ¬a ∣ n ^ 2 + r) ↔
      ¬3 ∣ n ^ 2 + r := by
    rw [roughCriterion_smallCutoff hn hlt (by decide),hf]
    simp only [Finset.mem_singleton,forall_eq]
  have he : canonicalRoughCandidates n 3 =
      (paritySafeProductWaveOffsets n 1).filter (fun r => ¬3 ∣ n ^ 2 + r) := by
    ext r
    simp only [canonicalRoughCandidates,paritySafeProductWaveOffsets,Finset.mem_filter,
      hc,one_dvd,and_true]
  rw [he]
  have hcards := Finset.card_filter_add_card_filter_not
    (s := paritySafeProductWaveOffsets n 1) (fun r => 3 ∣ n ^ 2 + r)
  rw [productWave_filter_dvd (by decide : Nat.Coprime 3 1)] at hcards
  have h3 := (primeAnchor_small_roots hn (by omega)).1
  have hcop3 := ((mem_squareAnchorOddActivePrimes.mp h3).1.coprime_iff_not_dvd.mpr
    (mem_squareAnchorOddActivePrimes.mp h3).2.2.1).symm
  simp only [Nat.mul_one] at hcards
  rw [paritySafeProductWave_card_eq_count hn (hn.odd_of_ne_two (by omega)) (by decide : Odd 1)
      (by simp : Nat.Coprime n 1),
    paritySafeProductWave_card_eq_count hn (hn.odd_of_ne_two (by omega)) (by decide : Odd 3) hcop3] at hcards
  omega

/-- Cutoff5 uses exact two-exclusion credit, rather than clipped sequential subtraction. -/
theorem rough_seats_five_floor {n : ℕ} (hn : n.Prime) (hlt : 11 < n) :
    (canonicalRoughCandidates n 5).card =
      primeAnchorProductWaveCount n 1 + primeAnchorProductWaveCount n 15 -
        (primeAnchorProductWaveCount n 3 + primeAnchorProductWaveCount n 5) := by
  classical
  have hf : ({3,5,7,11}:Finset ℕ).filter (fun a => a ≤ 5) = {3,5} := by decide
  have hc (r : ℕ) : (∀ a ∈ squareAnchorOddActivePrimes n, a ≤ 5 → ¬a ∣ n ^ 2 + r) ↔
      ¬3 ∣ n ^ 2 + r ∧ ¬5 ∣ n ^ 2 + r := by
    rw [roughCriterion_smallCutoff hn hlt (by decide),hf]
    simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  have he : canonicalRoughCandidates n 5 =
      (paritySafeProductWaveOffsets n 1).filter (fun r => ¬3 ∣ n ^ 2 + r ∧ ¬5 ∣ n ^ 2 + r) := by
    ext r
    simp only [canonicalRoughCandidates,paritySafeProductWaveOffsets,Finset.mem_filter,
      hc,one_dvd,and_true]
  rw [he,DkMath.NumberTheory.card_filter_two_exclusions]
  have hi : (paritySafeProductWaveOffsets n 1).filter
      (fun r => 3 ∣ n ^ 2 + r ∧ 5 ∣ n ^ 2 + r) = paritySafeProductWaveOffsets n 15 := by
    rw [← Finset.filter_filter,productWave_filter_dvd (by decide : Nat.Coprime 3 1)]
    rw [productWave_filter_dvd (by decide : Nat.Coprime 5 (3 * 1))]
  rw [hi,productWave_filter_dvd (by decide : Nat.Coprime 3 1),
    productWave_filter_dvd (by decide : Nat.Coprime 5 1)]
  obtain ⟨h3,h5,_⟩ := primeAnchor_small_roots hn (by omega)
  have hcopn (a : ℕ) (ha : a ∈ squareAnchorOddActivePrimes n) : Nat.Coprime n a :=
    ((mem_squareAnchorOddActivePrimes.mp ha).1.coprime_iff_not_dvd.mpr
      (mem_squareAnchorOddActivePrimes.mp ha).2.2.1).symm
  have hc15 : Nat.Coprime n 15 := by
    exact (hcopn 3 h3).mul_right (hcopn 5 h5)
  simp only [Nat.mul_one]
  rw [paritySafeProductWave_card_eq_count hn (hn.odd_of_ne_two (by omega)) (by decide : Odd 1)
      (by simp : Nat.Coprime n 1),
    paritySafeProductWave_card_eq_count hn (hn.odd_of_ne_two (by omega)) (by decide : Odd 15) hc15,
    paritySafeProductWave_card_eq_count hn (hn.odd_of_ne_two (by omega)) (by decide : Odd 3) (hcopn 3 h3),
    paritySafeProductWave_card_eq_count hn (hn.odd_of_ne_two (by omega)) (by decide : Odd 5) (hcopn 5 h5)]

/-- The sqrt cutoff support bound3 is sharp, even at a prime anchor. -/
theorem sqrt_multiplicity_bound_sharp :
    (24 : ℕ) ∈ canonicalRoughCandidates 19 (Nat.sqrt 19) ∧
      (paritySafeActiveSupport 19 24).card = 3 := by
  obtain ⟨hr,hs,_⟩ := rough_seat_multiplicity_counterexample
  refine ⟨?_, by rw [hs]; decide⟩
  have hsqrt : Nat.sqrt 19 = 4 := by decide +kernel
  rw [hsqrt]
  apply Finset.mem_filter.mpr
  refine ⟨(Finset.mem_filter.mp hr).1, ?_⟩
  intro a ha hle
  rcases activePrime_small_cases ha (by omega) with h3 | h5
  · subst a
    exact (Finset.mem_filter.mp hr).2 3 ha (by decide)
  · omega

end DkMathTest.LegendreCanonicalTailRegression
