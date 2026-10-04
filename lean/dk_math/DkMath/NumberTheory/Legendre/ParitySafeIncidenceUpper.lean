/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.ParitySafeMobiusOddCorrection
import DkMath.NumberTheory.Legendre.ParitySafeBlockLocalization
import Mathlib.Data.Finset.Fold

#print "file: DkMath.NumberTheory.Legendre.ParitySafeIncidenceUpper"

/-!
## Elementary incidence upper bounds and uncovered deficits

The bounds retain quotient endpoints and remove odd multiples of one or two
anchor primes. Taking the minimum over actual odd anchor primes is independent
of full cover. No active incidence is replaced by an exact finite lookup.
The existing incidence and uncovered-candidate objects are used throughout.
-/

namespace DkMath.NumberTheory

/-- A neutral two-exclusion bound retaining intersection credit before Nat subtraction. -/
theorem card_le_sub_two_exclusions {α : Type*} [DecidableEq α]
    {C S D E : Finset α} (hD : D ⊆ S) (hE : E ⊆ S)
    (hC : C ⊆ S \ (D ∪ E)) :
    C.card ≤ S.card + (D ∩ E).card - (D.card + E.card) := by
  have hU : D ∪ E ⊆ S := Finset.union_subset hD hE
  have h := Finset.card_le_card hC
  rw [Finset.card_sdiff_of_subset hU] at h
  have hcard := Finset.card_union_add_card_inter D E
  have hle := Finset.card_le_card hU
  omega

end DkMath.NumberTheory

namespace DkMath.NumberTheory.Legendre

open scoped BigOperators

/-- Exact odd endpoint occupancy before imposing anchor coprimality. -/
def paritySafeOddQuotientUpper (n q : ℕ) : ℕ :=
  (((n ^ 2 + 2 * n) / q + 1) / 2) - ((n ^ 2 / q + 1) / 2)

/-- Odd endpoint occupancy after excluding multiples of one odd anchor prime. -/
def paritySafeDivisorWaveUpper (n q d : ℕ) : ℕ :=
  paritySafeOddQuotientUpper n q -
    paritySafeOddMultipleFloorDelta (n ^ 2 / q) ((n ^ 2 + 2 * n) / q) d

/-- The best single-anchor-prime exclusion, including the uncorrected endpoint bound. -/
def paritySafeQuotientWaveUpper (n q : ℕ) : ℕ :=
  (n.primeFactors.erase 2).fold min (paritySafeOddQuotientUpper n q)
    (paritySafeDivisorWaveUpper n q)

/-- Retain both the endpoint-sensitive exclusion and uniform2q packing. -/
def paritySafeWaveUpper (n q : ℕ) : ℕ :=
  min (shellFrequencyCap (2 * q) (2 * n)) (paritySafeQuotientWaveUpper n q)

/-- Upper bound on the existing incidence count, summed over the actual active prime set. -/
noncomputable def paritySafeIncidenceUpper (n : ℕ) : ℕ :=
  ∑ q ∈ squareAnchorOddActivePrimes n, paritySafeWaveUpper n q

/-- Same-wave2q divisibility gives a uniform finite packing bound. -/
theorem paritySafeActiveWave_card_le_spacing {n q : ℕ}
    (hq : q ∈ squareAnchorOddActivePrimes n) :
    (paritySafeActiveWaveOffsets n q).card ≤ shellFrequencyCap (2 * q) (2 * n) := by
  classical
  have hqpos := (mem_squareAnchorOddActivePrimes.mp hq).1.pos
  have hnpos : 0 < n := lt_of_lt_of_le hqpos (mem_squareAnchorOddActivePrimes.mp hq).2.1
  have hmap : ∀ r ∈ paritySafeActiveWaveOffsets n q,
      (r - 1) / (2 * q) ∈ Finset.range (shellFrequencyCap (2 * q) (2 * n)) := by
    intro r hr
    have hoff := squareOffset_of_mem_squareAnchorOddPointCoprimeOffsets
      (mem_paritySafeActiveWaveOffsets.mp hr).1
    have hle : r - 1 ≤ 2 * n - 1 := by dsimp [SquareOffset] at hoff; omega
    have hdiv := Nat.div_le_div_right (c := 2 * q) hle
    simp only [Finset.mem_range, shellFrequencyCap, ite_eq_right (by omega : 2 * n ≠ 0)]
    omega
  have hsep {r s : ℕ} (hr : r ∈ paritySafeActiveWaveOffsets n q)
      (hs : s ∈ paritySafeActiveWaveOffsets n q) (hlt : r < s)
      (heq : (r - 1) / (2 * q) = (s - 1) / (2 * q)) : False := by
    have hspace := (paritySafeActiveWave_same_wave_quotient_rigidity hq hr hs hlt).2.1
    have hdpos : 0 < 2 * q := by omega
    have hdiff : 0 < s - r := by omega
    have hgap := Nat.le_of_dvd hdiff hspace
    have hrpos := (squareOffset_of_mem_squareAnchorOddPointCoprimeOffsets
      (mem_paritySafeActiveWaveOffsets.mp hr).1).1
    have hspos := (squareOffset_of_mem_squareAnchorOddPointCoprimeOffsets
      (mem_paritySafeActiveWaveOffsets.mp hs).1).1
    have hre := Nat.mod_add_div (r - 1) (2 * q)
    have hse := Nat.mod_add_div (s - 1) (2 * q)
    have hrmod := Nat.mod_lt (r - 1) hdpos
    have hsmod := Nat.mod_lt (s - 1) hdpos
    rw [heq] at hre
    omega
  have hinj : Set.InjOn (fun r : ℕ => (r - 1) / (2 * q))
      (paritySafeActiveWaveOffsets n q) := by
    intro r hr s hs heq
    dsimp only at heq
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact hsep hr hs hlt heq
    · exact hsep hs hr hlt heq.symm
  simpa using Finset.card_le_card_of_injOn (fun r => (r - 1) / (2 * q)) hmap hinj

/-- The exact odd endpoint count bounds every reduced quotient interval. -/
theorem paritySafeReducedQuotient_card_le_oddUpper {n q : ℕ} (hqpos : 0 < q) :
    (paritySafeReducedQuotientInterval n q).card ≤ paritySafeOddQuotientUpper n q := by
  have h := Finset.card_le_card
    (paritySafeReducedQuotientInterval_subset_oddRaw (n := n) (q := q))
  rw [paritySafeOddRawQuotientInterval_card_eq hqpos] at h
  exact h

/-- Excluding one actual odd anchor prime is an unconditional wave upper bound. -/
theorem paritySafeReducedQuotient_card_le_divisorUpper {n q d : ℕ}
    (hqpos : 0 < q) (hd : d.Prime) (hd2 : d ≠ 2) (hdn : d ∣ n) :
    (paritySafeReducedQuotientInterval n q).card ≤ paritySafeDivisorWaveUpper n q d := by
  classical
  let raw := paritySafeOddRawQuotientInterval n q
  let removed := raw.filter (fun k => d ∣ k)
  have hsub : paritySafeReducedQuotientInterval n q ⊆ raw \ removed := by
    intro k hk
    have hr := paritySafeReducedQuotientInterval_subset_oddRaw hk
    have hc := (Finset.mem_filter.mp hk).2
    apply Finset.mem_sdiff.mpr
    refine ⟨hr, ?_⟩
    intro hm
    have hdk := (Finset.mem_filter.mp hm).2
    have hd2n : d ∣ 2 * n := dvd_mul_of_dvd_right hdn 2
    have hone := Nat.eq_one_of_dvd_coprimes hc hd2n hdk
    exact hd.ne_one hone
  have hremoved : removed.card =
      paritySafeOddMultipleFloorDelta (n ^ 2 / q) ((n ^ 2 + 2 * n) / q) d := by
    have heq : removed = (Finset.Ioc (n ^ 2 / q) ((n ^ 2 + 2 * n) / q)).filter
        (fun k => Odd k ∧ d ∣ k) := by
      ext k
      simp [removed, raw, paritySafeOddRawQuotientInterval, and_assoc]
    rw [heq]
    exact card_filter_odd_dvd_Ioc_eq_paritySafeDelta (hd.odd_of_ne_two hd2)
      (Nat.div_le_div_right (by omega))
  have h := Finset.card_le_card hsub
  rw [Finset.card_sdiff_of_subset (Finset.filter_subset _ _), hremoved] at h
  rw [show raw.card = paritySafeOddQuotientUpper n q from
    paritySafeOddRawQuotientInterval_card_eq hqpos] at h
  exact h

/-- The minimum over all admissible single-prime exclusions is still an upper bound. -/
theorem paritySafeReducedQuotient_card_le_quotientUpper {n q : ℕ} (hqpos : 0 < q) :
    (paritySafeReducedQuotientInterval n q).card ≤ paritySafeQuotientWaveUpper n q := by
  classical
  apply (Finset.le_fold_min _).mpr
  constructor
  · exact paritySafeReducedQuotient_card_le_oddUpper hqpos
  · intro d hd
    have hde := Finset.mem_erase.mp hd
    have hdp := Nat.mem_primeFactors.mp hde.2
    exact paritySafeReducedQuotient_card_le_divisorUpper hqpos hdp.1 hde.1 hdp.2.1

theorem paritySafeActiveWave_card_le_waveUpper {n q : ℕ}
    (hq : q ∈ squareAnchorOddActivePrimes n) :
    (paritySafeActiveWaveOffsets n q).card ≤ paritySafeWaveUpper n q := by
  apply Nat.le_min.mpr
  constructor
  · exact paritySafeActiveWave_card_le_spacing hq
  · rw [card_paritySafeActiveWaveOffsets_eq_reducedQuotientInterval hq]
    exact paritySafeReducedQuotient_card_le_quotientUpper
      (mem_squareAnchorOddActivePrimes.mp hq).1.pos

/-- The new cap never exceeds the existing exact odd endpoint count. -/
theorem paritySafeWaveUpper_le_oddUpper (n q : ℕ) :
    paritySafeWaveUpper n q ≤ paritySafeOddQuotientUpper n q := by
  exact (Nat.min_le_right _ _).trans
    ((Finset.fold_min_le _).mpr (Or.inl (le_refl _)))

/-- Full-cover-independent structural incidence upper bound. -/
theorem paritySafeIncidenceCount_le_upper (n : ℕ) :
    paritySafeIncidenceCount n ≤ paritySafeIncidenceUpper n := by
  unfold paritySafeIncidenceCount paritySafeIncidenceUpper
  exact Finset.sum_le_sum fun q hq => paritySafeActiveWave_card_le_waveUpper hq

/-- Two odd-divisor exclusions with their common multiples credited before subtraction. -/
def paritySafePairDivisorWaveUpper (n q d e : ℕ) : ℕ :=
  (paritySafeOddQuotientUpper n q +
    paritySafeOddMultipleFloorDelta (n ^ 2 / q) ((n ^ 2 + 2 * n) / q) (d * e)) -
    (paritySafeOddMultipleFloorDelta (n ^ 2 / q) ((n ^ 2 + 2 * n) / q) d +
      paritySafeOddMultipleFloorDelta (n ^ 2 / q) ((n ^ 2 + 2 * n) / q) e)

/-- The old cap and all distinct odd-anchor-prime-pair caps are minimized together. -/
def paritySafeTwoPrimeWaveUpper (n q : ℕ) : ℕ :=
  (n.primeFactors.erase 2).offDiag.fold min (paritySafeWaveUpper n q)
    (fun p => paritySafePairDivisorWaveUpper n q p.1 p.2)

/-- The pairwise cap bounds the existing incidence, with the original active-prime index. -/
noncomputable def paritySafeTwoPrimeIncidenceUpper (n : ℕ) : ℕ :=
  ∑ q ∈ squareAnchorOddActivePrimes n, paritySafeTwoPrimeWaveUpper n q

private theorem oddRaw_filter_dvd_card {n q d : ℕ} (hd : Odd d) :
    ((paritySafeOddRawQuotientInterval n q).filter (fun k => d ∣ k)).card =
      paritySafeOddMultipleFloorDelta (n ^ 2 / q) ((n ^ 2 + 2 * n) / q) d := by
  have heq : (paritySafeOddRawQuotientInterval n q).filter (fun k => d ∣ k) =
      (Finset.Ioc (n ^ 2 / q) ((n ^ 2 + 2 * n) / q)).filter
        (fun k => Odd k ∧ d ∣ k) := by
    ext k
    simp [paritySafeOddRawQuotientInterval, and_assoc]
  rw [heq]
  exact card_filter_odd_dvd_Ioc_eq_paritySafeDelta hd (Nat.div_le_div_right (by omega))

/-- Distinct odd anchor primes give a full-cover-independent inclusion-exclusion cap. -/
theorem paritySafeReducedQuotient_card_le_pairDivisorUpper {n q d e : ℕ}
    (hqpos : 0 < q) (hd : d.Prime) (he : e.Prime) (hd2 : d ≠ 2) (he2 : e ≠ 2)
    (hde : d ≠ e) (hdn : d ∣ n) (hen : e ∣ n) :
    (paritySafeReducedQuotientInterval n q).card ≤
      paritySafePairDivisorWaveUpper n q d e := by
  classical
  let raw := paritySafeOddRawQuotientInterval n q
  let D := raw.filter (fun k => d ∣ k)
  let E := raw.filter (fun k => e ∣ k)
  have hsub : paritySafeReducedQuotientInterval n q ⊆ raw \ (D ∪ E) := by
    intro k hk
    refine Finset.mem_sdiff.mpr ⟨paritySafeReducedQuotientInterval_subset_oddRaw hk, ?_⟩
    intro hm
    have hc := (Finset.mem_filter.mp hk).2
    rcases Finset.mem_union.mp hm with hm | hm
    · have hone := Nat.eq_one_of_dvd_coprimes hc (dvd_mul_of_dvd_right hdn 2)
        (Finset.mem_filter.mp hm).2
      exact hd.ne_one hone
    · have hone := Nat.eq_one_of_dvd_coprimes hc (dvd_mul_of_dvd_right hen 2)
        (Finset.mem_filter.mp hm).2
      exact he.ne_one hone
  have hinter : D ∩ E = raw.filter (fun k => d * e ∣ k) := by
    ext k
    simp only [D, E, Finset.mem_inter, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hk, hdk⟩, ⟨_, hek⟩⟩
      exact ⟨hk, ((Nat.coprime_primes hd he).mpr hde).mul_dvd_of_dvd_of_dvd hdk hek⟩
    · rintro ⟨hk, hmul⟩
      exact ⟨⟨hk, (dvd_mul_right d e).trans hmul⟩,
        ⟨hk, (dvd_mul_left e d).trans hmul⟩⟩
  have h := DkMath.NumberTheory.card_le_sub_two_exclusions
    (Finset.filter_subset _ _) (Finset.filter_subset _ _) hsub
  rw [hinter, oddRaw_filter_dvd_card ((hd.odd_of_ne_two hd2).mul (he.odd_of_ne_two he2))] at h
  rw [show D.card = _ from oddRaw_filter_dvd_card (hd.odd_of_ne_two hd2),
    show E.card = _ from oddRaw_filter_dvd_card (he.odd_of_ne_two he2),
    show raw.card = _ from paritySafeOddRawQuotientInterval_card_eq hqpos] at h
  exact h

theorem paritySafeActiveWave_card_le_twoPrimeWaveUpper {n q : ℕ}
    (hq : q ∈ squareAnchorOddActivePrimes n) :
    (paritySafeActiveWaveOffsets n q).card ≤ paritySafeTwoPrimeWaveUpper n q := by
  apply (Finset.le_fold_min _).mpr
  refine ⟨paritySafeActiveWave_card_le_waveUpper hq, ?_⟩
  intro p hp
  obtain ⟨hd, he, hde⟩ := Finset.mem_offDiag.mp hp
  obtain ⟨hd2, hdf⟩ := Finset.mem_erase.mp hd
  obtain ⟨he2, hef⟩ := Finset.mem_erase.mp he
  obtain ⟨hdprime, hdn, _⟩ := Nat.mem_primeFactors.mp hdf
  obtain ⟨heprime, hen, _⟩ := Nat.mem_primeFactors.mp hef
  rw [card_paritySafeActiveWaveOffsets_eq_reducedQuotientInterval hq]
  exact paritySafeReducedQuotient_card_le_pairDivisorUpper
    (mem_squareAnchorOddActivePrimes.mp hq).1.pos hdprime heprime hd2 he2 hde hdn hen

theorem paritySafeTwoPrimeWaveUpper_le_waveUpper (n q : ℕ) :
    paritySafeTwoPrimeWaveUpper n q ≤ paritySafeWaveUpper n q :=
  (Finset.fold_min_le _).mpr (Or.inl (le_refl _))

theorem paritySafeIncidenceCount_le_twoPrimeUpper (n : ℕ) :
    paritySafeIncidenceCount n ≤ paritySafeTwoPrimeIncidenceUpper n := by
  unfold paritySafeIncidenceCount paritySafeTwoPrimeIncidenceUpper
  exact Finset.sum_le_sum fun q hq => paritySafeActiveWave_card_le_twoPrimeWaveUpper hq

theorem paritySafeTwoPrimeIncidenceUpper_le_upper (n : ℕ) :
    paritySafeTwoPrimeIncidenceUpper n ≤ paritySafeIncidenceUpper n := by
  unfold paritySafeTwoPrimeIncidenceUpper paritySafeIncidenceUpper
  exact Finset.sum_le_sum fun q _ => paritySafeTwoPrimeWaveUpper_le_waveUpper n q

/-- With fewer than two distinct odd anchor primes, pair exclusion adds no new cap. -/
theorem paritySafeTwoPrimeWaveUpper_eq_waveUpper_of_card_le_one {n : ℕ}
    (hcard : (n.primeFactors.erase 2).card ≤ 1) (q : ℕ) :
    paritySafeTwoPrimeWaveUpper n q = paritySafeWaveUpper n q := by
  have hempty : (n.primeFactors.erase 2).offDiag = ∅ := by
    apply Finset.card_eq_zero.mp
    rw [Finset.offDiag_card]
    interval_cases h : (n.primeFactors.erase 2).card <;> simp_all
  simp [paritySafeTwoPrimeWaveUpper, hempty]

theorem paritySafeTwoPrimeIncidenceUpper_eq_upper_of_card_le_one {n : ℕ}
    (hcard : (n.primeFactors.erase 2).card ≤ 1) :
    paritySafeTwoPrimeIncidenceUpper n = paritySafeIncidenceUpper n := by
  unfold paritySafeTwoPrimeIncidenceUpper paritySafeIncidenceUpper
  exact Finset.sum_congr rfl fun q _ => paritySafeTwoPrimeWaveUpper_eq_waveUpper_of_card_le_one hcard q

/-- Pair exclusion cannot improve the cap on prime powers or powers of two times a prime power. -/
theorem paritySafeTwoPrimeIncidenceUpper_eq_upper_two_pow_mul_prime_pow
    {p : ℕ} (hp : p.Prime) (a k : ℕ) :
    paritySafeTwoPrimeIncidenceUpper (2 ^ a * p ^ k) =
      paritySafeIncidenceUpper (2 ^ a * p ^ k) := by
  have htwo : (2 ^ a).primeFactors ⊆ ({2} : Finset ℕ) := by
    by_cases ha : a = 0
    · simp [ha]
    · rw [Nat.primeFactors_pow 2 ha, Nat.prime_two.primeFactors]
  have hpPow : (p ^ k).primeFactors ⊆ ({p} : Finset ℕ) := by
    by_cases hk : k = 0
    · simp [hk]
    · rw [Nat.primeFactors_pow p hk, hp.primeFactors]
  have hsub : ((2 ^ a * p ^ k).primeFactors.erase 2) ⊆ ({p} : Finset ℕ) := by
    intro q hq
    obtain ⟨hq2, hqf⟩ := Finset.mem_erase.mp hq
    rw [Nat.primeFactors_mul (pow_ne_zero _ (by decide : (2 : ℕ) ≠ 0))
      (pow_ne_zero _ hp.ne_zero)] at hqf
    rcases Finset.mem_union.mp hqf with hqf | hqf
    · exact False.elim (hq2 (Finset.mem_singleton.mp (htwo hqf)))
    · exact hpPow hqf
  apply paritySafeTwoPrimeIncidenceUpper_eq_upper_of_card_le_one
  simpa using Finset.card_le_card hsub

/-- The seat-side arithmetic alternative uses distinct prime factors of the actual point. -/
theorem paritySafeActiveSupport_subset_pointPrimeFactors {n r : ℕ}
    (hr : r ∈ squareAnchorOddPointCoprimeOffsets n) :
    paritySafeActiveSupport n r ⊆ (n ^ 2 + r).primeFactors := by
  intro q hq
  have hp := mem_paritySafeActiveSupport_iff_dvd.mp hq
  have hs := squareOffset_of_mem_squareAnchorOddPointCoprimeOffsets hr
  exact Nat.mem_primeFactors.mpr
    ⟨(mem_squareAnchorOddActivePrimes.mp hp.1).1, hp.2, by
      dsimp [SquareOffset] at hs
      omega⟩

/-- This independent seat-side upper bound includes large prime factors and can be weaker. -/
theorem paritySafeIncidenceCount_le_pointPrimeFactors_sum (n : ℕ) :
    paritySafeIncidenceCount n ≤ ∑ r ∈ squareAnchorOddPointCoprimeOffsets n,
      (n ^ 2 + r).primeFactors.card := by
  rw [paritySafeIncidenceCount_eq_candidate_support_sum]
  exact Finset.sum_le_sum fun r hr =>
    Finset.card_le_card (paritySafeActiveSupport_subset_pointPrimeFactors hr)

/-- Exact switching between the two audited incidence views in a successor block. -/
theorem block_candidateSupportSum_eq_reducedQuotientSum (N T : ℕ) :
    (∑ i ∈ Finset.range T, ∑ r ∈ squareAnchorOddPointCoprimeOffsets (N + i + 1),
      (paritySafeActiveSupport (N + i + 1) r).card) =
    ∑ i ∈ Finset.range T, ∑ q ∈ squareAnchorOddActivePrimes (N + i + 1),
      (paritySafeReducedQuotientInterval (N + i + 1) q).card := by
  apply Finset.sum_congr rfl
  intro i hi
  rw [← paritySafeIncidenceCount_eq_candidate_support_sum,
    paritySafeIncidenceCount_eq_reducedQuotientInterval_sum]

theorem block_incidenceCount_le_upper (N T : ℕ) :
    (∑ i ∈ Finset.range T, paritySafeIncidenceCount (N + i + 1)) ≤
      ∑ i ∈ Finset.range T, paritySafeIncidenceUpper (N + i + 1) :=
  Finset.sum_le_sum fun i _ => paritySafeIncidenceCount_le_upper (N + i + 1)

/-- Consume the structural cap through006's existing temporal-demand consumer. -/
theorem not_block_fullyCovered_of_upper_lt_candidate_add_freshBound
    (N T : ℕ)
    (hlt : (∑ i ∈ Finset.range T, paritySafeIncidenceUpper (N + i + 1)) <
      (∑ i ∈ Finset.range T, (squareAnchorOddPointCoprimeOffsets (N + i + 1)).card) +
      ((∑ i ∈ Finset.range T, (lowerParitySafeCandidates (N + i)).card) -
        lowerParitySafeParityPersistenceCap N T -
        (∑ i ∈ Finset.range T, (lowerFreshWithoutPersistentSeats (N + i)).card))) :
    ¬ (∀ i ∈ Finset.range T, SquareOffsetsFullyCovered (N + i + 1)) := by
  apply not_block_fullyCovered_of_incidence_lt_candidate_add_freshBound N T
  exact lt_of_le_of_lt (block_incidenceCount_le_upper N T) hlt

/-- Quantitative deficit with honest Nat subtraction and an independently supplied excess bound. -/
theorem paritySafeUncovered_card_ge_candidate_add_excess_sub_upper
    (n e : ℕ) (he : e ≤ paritySafeSupportExcess n) :
    (squareAnchorOddPointCoprimeOffsets n).card + e - paritySafeIncidenceUpper n ≤
      (paritySafeUncoveredCandidates n).card := by
  have hu := paritySafeIncidenceCount_le_upper n
  have hc := paritySafeCoveredCandidates_card_add_uncoveredCandidates_card_eq_candidate_card n
  have hb := paritySafeCoveredCandidates_card_add_supportExcess_eq_incidence n
  omega

/-- The unconditional block version needs no simultaneous full-cover premise. -/
theorem block_uncovered_ge_candidate_add_excess_sub_upper
    (N T e : ℕ) (he : e ≤ ∑ i ∈ Finset.range T, paritySafeSupportExcess (N + i + 1)) :
    (∑ i ∈ Finset.range T, (squareAnchorOddPointCoprimeOffsets (N + i + 1)).card) + e -
      (∑ i ∈ Finset.range T, paritySafeIncidenceUpper (N + i + 1)) ≤
      ∑ i ∈ Finset.range T, (paritySafeUncoveredCandidates (N + i + 1)).card := by
  have hu := block_incidenceCount_le_upper N T
  have hb := block_incidence_add_uncovered_eq_candidate_add_supportExcess N T
  omega

theorem exists_prime_squareCell_of_candidate_add_excess_gt_upper
    {n e : ℕ} (hn : 0 < n) (he : e ≤ paritySafeSupportExcess n)
    (hlt : paritySafeIncidenceUpper n < (squareAnchorOddPointCoprimeOffsets n).card + e) :
    ∃ p, Nat.Prime p ∧ SquareCell n p := by
  apply exists_prime_squareCell_of_paritySafeUncoveredCandidates_nonempty hn
  apply Finset.card_pos.mp
  have h := paritySafeUncovered_card_ge_candidate_add_excess_sub_upper n e he
  omega

theorem exists_prime_squareCell_of_block_candidate_add_excess_gt_upper
    (N T e : ℕ) (he : e ≤ ∑ i ∈ Finset.range T, paritySafeSupportExcess (N + i + 1))
    (hlt : (∑ i ∈ Finset.range T, paritySafeIncidenceUpper (N + i + 1)) <
      (∑ i ∈ Finset.range T, (squareAnchorOddPointCoprimeOffsets (N + i + 1)).card) + e) :
    ∃ i ∈ Finset.range T, ∃ p, Nat.Prime p ∧ SquareCell (N + i + 1) p := by
  have hu := block_uncovered_ge_candidate_add_excess_sub_upper N T e he
  have hp : 0 < ∑ i ∈ Finset.range T, (paritySafeUncoveredCandidates (N + i + 1)).card := by omega
  obtain ⟨i, hi, hpos⟩ := Finset.sum_pos_iff.mp hp
  obtain ⟨p, hprime, hcell⟩ := exists_prime_squareCell_of_paritySafeUncoveredCandidates_nonempty
    (by omega) (Finset.card_pos.mp hpos)
  exact ⟨i, hi, p, hprime, hcell⟩

end DkMath.NumberTheory.Legendre
