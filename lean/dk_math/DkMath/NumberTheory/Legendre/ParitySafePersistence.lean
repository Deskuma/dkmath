/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.CyclotomicPersistence
import DkMath.NumberTheory.Legendre.ParitySafeIncidenceBalance

/-!
# Lower persistence in the existing parity-safe incidence ledger

We restrict the existing successor candidates and active support to the lower
channel. Freshness is relative to the full old bounded-prime support at the
same offset, not to the old parity-safe candidate family (parity reverses).
The finite-run bound includes the number of seats as a weight. It does not
bound pair overlap, support excess, or any residual capacity by itself.
-/

namespace DkMath.NumberTheory.Legendre

open DkMath.Gnomon DkMath.NumberTheory.Primitive
open scoped BigOperators

/-- The lower canonical reindex sends an old odd point to an even point.
Consequently it cannot preserve the parity-safe candidate family. -/
theorem lower_successor_not_paritySafeCandidate_of_odd
    {n r : ℕ} (hlow : r < n + 1) (hodd : Odd (n ^ 2 + r)) :
    successorThresholdInsert n r ∉ squareAnchorOddPointCoprimeOffsets (n + 1) := by
  have heven := hodd.add_odd (oddGnomon_odd n)
  rw [← successorThresholdInsert_lower_additive_displacement hlow] at heven
  intro hr
  exact (Nat.not_odd_iff_even.mpr heven)
    (mem_squareAnchorOddPointCoprimeOffsets.mp hr).2

/-- Under a prime successor threshold, the upper old/active intersection is
empty: the existing upper theorem forces two, excluded by active support. -/
theorem disjoint_upper_oldSupport_paritySafeActiveSupport
    {n r : ℕ} (hr : SquareOffset n r) (hupp : n + 1 ≤ r)
    (hsucc : (n + 1).Prime) :
    Disjoint (squareOffsetPrimeSupport n r)
      (paritySafeActiveSupport (n + 1) (successorThresholdInsert n r)) := by
  classical
  rw [Finset.disjoint_left]
  intro q hold hnew
  have hn := mem_paritySafeActiveSupport_iff_dvd.mp hnew
  have ha := mem_squareAnchorOddActivePrimes.mp hn.1
  have hs : q ∈ squareOffsetPrimeSupport (n + 1) (successorThresholdInsert n r) :=
    mem_squareOffsetPrimeSupport.mpr ⟨ha.1, ha.2.1, hn.2⟩
  exact ha.2.2.2 (mem_reindexed_primeSupport_inter_upper_imp_eq_two
    hr hupp hsucc (Finset.mem_inter.mpr ⟨hold, hs⟩))

/-- Actual successor candidates in the lower channel of the canonical reindex. -/
noncomputable def lowerParitySafeCandidates (n : ℕ) : Finset ℕ :=
  (squareAnchorOddPointCoprimeOffsets (n + 1)).filter (fun r => r < n + 1)

/-- A finite arithmetic normalization of the same production candidate sector. -/
theorem lowerParitySafeCandidates_eq_filter_Icc (n : ℕ) :
    lowerParitySafeCandidates n = (Finset.Icc 1 n).filter
      (fun r => Nat.Coprime (n + 1) r ∧ ((n + 1) ^ 2 + r) % 2 = 1) := by
  ext r
  simp only [lowerParitySafeCandidates, Finset.mem_filter,
    mem_squareAnchorOddPointCoprimeOffsets, mem_squareAnchorCoprimeOffsets,
    SquareOffset, Nat.odd_iff, Finset.mem_Icc]
  omega

/-- Persistent active primes at a lower successor seat. -/
noncomputable def lowerParitySafePersistentSupport (n r : ℕ) : Finset ℕ :=
  paritySafeActiveSupport (n + 1) r ∩ squareOffsetPrimeSupport n r

/-- Active successor primes absent from the old full support at the same seat. -/
noncomputable def lowerParitySafeFreshSupport (n r : ℕ) : Finset ℕ :=
  paritySafeActiveSupport (n + 1) r \ squareOffsetPrimeSupport n r

/-- A restriction of the production candidate-side incidence sum. -/
noncomputable def lowerParitySafeIncidenceCount (n : ℕ) : ℕ :=
  ∑ r ∈ lowerParitySafeCandidates n, (paritySafeActiveSupport (n + 1) r).card

/-- Persistent incidences count seats as well as primes. -/
noncomputable def lowerParitySafePersistentCount (n : ℕ) : ℕ :=
  ∑ r ∈ lowerParitySafeCandidates n, (lowerParitySafePersistentSupport n r).card

/-- Fresh incidences in precisely the same lower candidate sector. -/
noncomputable def lowerParitySafeFreshCount (n : ℕ) : ℕ :=
  ∑ r ∈ lowerParitySafeCandidates n, (lowerParitySafeFreshSupport n r).card

/-- The exact incidence partition, with no cover hypothesis. -/
theorem lowerParitySafeIncidenceCount_eq_persistent_add_fresh (n : ℕ) :
    lowerParitySafeIncidenceCount n =
      lowerParitySafePersistentCount n + lowerParitySafeFreshCount n := by
  classical
  unfold lowerParitySafeIncidenceCount lowerParitySafePersistentCount lowerParitySafeFreshCount
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  dsimp only [lowerParitySafePersistentSupport, lowerParitySafeFreshSupport]
  have h := Finset.card_sdiff_add_card_inter
    (paritySafeActiveSupport (n + 1) r) (squareOffsetPrimeSupport n r)
  omega

/-- This sector belongs to the existing incidence count; it is not a new cover ledger. -/
theorem lowerParitySafeIncidenceCount_le_incidence (n : ℕ) :
    lowerParitySafeIncidenceCount n ≤ paritySafeIncidenceCount (n + 1) := by
  classical
  rw [paritySafeIncidenceCount_eq_candidate_support_sum]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by intros; omega)

/-- A persistent incidence has an odd old prime at the shell address. -/
theorem lowerParitySafePersistentSupport_subset_addresses
    {n r M : ℕ} (hr : r ∈ lowerParitySafeCandidates n) (hnM : n ≤ M) :
    lowerParitySafePersistentSupport n r ⊆
      ((primeScalesUpTo M).erase 2).filter (fun q => q ∣ oddGnomon n) := by
  classical
  intro q hq
  have hseat := Finset.mem_filter.mp hr
  obtain ⟨hnew, hold⟩ := Finset.mem_inter.mp hq
  have hnew' := mem_paritySafeActiveSupport_iff_dvd.mp hnew
  have hactive := mem_squareAnchorOddActivePrimes.mp hnew'.1
  have hold' := mem_squareOffsetPrimeSupport.mp hold
  have hdiv : q ∣ oddGnomon n := by
    apply dvd_oddGnomon_of_dvd_reindexed_lower_common hseat.2 hold'.2.2
    simpa [successorThresholdInsert, hseat.2] using hnew'.2
  exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr
    ⟨hactive.2.2.2, mem_primeScalesUpTo.mpr ⟨hold'.1, hold'.2.1.trans hnM⟩⟩, hdiv⟩

/-- The lower sector has at most `n` seats. -/
theorem lowerParitySafeCandidates_card_le (n : ℕ) :
    (lowerParitySafeCandidates n).card ≤ n := by
  classical
  have hsub : lowerParitySafeCandidates n ⊆ Finset.Icc 1 n := by
    intro r hr
    have h := Finset.mem_filter.mp hr
    have hs := squareOffset_of_mem_squareAnchorOddPointCoprimeOffsets h.1
    exact Finset.mem_Icc.mpr ⟨hs.1, by omega⟩
  simpa using Finset.card_le_card hsub

/-- Possible seats for a fixed persistent prime, independent of the shell:
the addressed old point forces divisibility of `4*r+1`. -/
def lowerPersistentSeatPool (q M : ℕ) : Finset ℕ :=
  (Finset.Icc 1 M).filter (fun r => q ∣ 4 * r + 1)

/-- Fixed-seat weights never exceed the crude all-seat weight. -/
theorem lowerPersistentSeatPool_card_le (q M : ℕ) :
    (lowerPersistentSeatPool q M).card ≤ M := by
  simpa [lowerPersistentSeatPool] using Finset.card_le_card (Finset.filter_subset (fun r => q ∣ 4 * r + 1)
    (Finset.Icc 1 M))

/-- A sharper incidence bound uses the fixed-seat restriction, not all `M` seats. -/
theorem lowerParitySafePersistentCount_le_seatWeighted_addresses
    {n M : ℕ} (hnM : n ≤ M) :
    lowerParitySafePersistentCount n ≤
      ∑ q ∈ (primeScalesUpTo M).erase 2,
        if q ∣ oddGnomon n then (lowerPersistentSeatPool q M).card else 0 := by
  classical
  let B := (primeScalesUpTo M).erase 2
  have hseats : lowerParitySafeCandidates n ⊆ Finset.Icc 1 M := by
    intro r hr
    have h := Finset.mem_filter.mp hr
    have hs := squareOffset_of_mem_squareAnchorOddPointCoprimeOffsets h.1
    exact Finset.mem_Icc.mpr ⟨hs.1, by omega⟩
  have hsupport (r : ℕ) (hr : r ∈ lowerParitySafeCandidates n) :
      lowerParitySafePersistentSupport n r ⊆
        B.filter (fun q => q ∣ oddGnomon n ∧ q ∣ 4 * r + 1) := by
    intro q hq
    have ha := Finset.mem_filter.mp
      (lowerParitySafePersistentSupport_subset_addresses hr hnM hq)
    have hp := (mem_squareOffsetPrimeSupport.mp (Finset.mem_inter.mp hq).2).2.2
    exact Finset.mem_filter.mpr
      ⟨ha.1, ha.2, dvd_four_mul_offset_add_one_of_lower_persistence hp ha.2⟩
  calc
    lowerParitySafePersistentCount n ≤ ∑ r ∈ lowerParitySafeCandidates n,
        (B.filter (fun q => q ∣ oddGnomon n ∧ q ∣ 4 * r + 1)).card := by
      exact Finset.sum_le_sum (fun r hr => Finset.card_le_card (hsupport r hr))
    _ ≤ ∑ r ∈ Finset.Icc 1 M,
        (B.filter (fun q => q ∣ oddGnomon n ∧ q ∣ 4 * r + 1)).card :=
      Finset.sum_le_sum_of_subset_of_nonneg hseats (by intros; omega)
    _ = ∑ q ∈ B,
        if q ∣ oddGnomon n then (lowerPersistentSeatPool q M).card else 0 := by
      simp only [Finset.card_filter]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q hq
      by_cases ha : q ∣ oddGnomon n <;> simp [ha, lowerPersistentSeatPool]

/-- A per-shell bound with explicit seat multiplicity. -/
theorem lowerParitySafePersistentCount_le_weighted_addresses {n M : ℕ} (hnM : n ≤ M) :
    lowerParitySafePersistentCount n ≤
      M * (((primeScalesUpTo M).erase 2).filter (fun q => q ∣ oddGnomon n)).card := by
  classical
  calc
    lowerParitySafePersistentCount n ≤
        ∑ r ∈ lowerParitySafeCandidates n,
          (((primeScalesUpTo M).erase 2).filter (fun q => q ∣ oddGnomon n)).card := by
      apply Finset.sum_le_sum
      intro r hr
      exact Finset.card_le_card (lowerParitySafePersistentSupport_subset_addresses hr hnM)
    _ = (lowerParitySafeCandidates n).card *
        (((primeScalesUpTo M).erase 2).filter (fun q => q ∣ oddGnomon n)).card := by simp
    _ ≤ M * (((primeScalesUpTo M).erase 2).filter (fun q => q ∣ oddGnomon n)).card := by
      exact Nat.mul_le_mul_right _ ((lowerParitySafeCandidates_card_le n).trans hnM)

/-- A finite-run capacity for actual lower persistent incidences. Each prime
is weighted by its fixed-seat pool up to the maximal shell bound `N+T`. -/
noncomputable def lowerParitySafePersistenceCap (N T : ℕ) : ℕ :=
  ∑ q ∈ (primeScalesUpTo (N + T)).erase 2,
    (lowerPersistentSeatPool q (N + T)).card * shellFrequencyCap q T

/-- Comparison with the crude maximal-seat frequency bound. This comparison
does not mention any of the production frontier's residual capacities. -/
theorem lowerParitySafePersistenceCap_le_crude (N T : ℕ) :
    lowerParitySafePersistenceCap N T ≤
      (N + T) * ∑ q ∈ (primeScalesUpTo (N + T)).erase 2, shellFrequencyCap q T := by
  unfold lowerParitySafePersistenceCap
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun q _ =>
    Nat.mul_le_mul_right _ (lowerPersistentSeatPool_card_le q (N + T)))

/-- Prime-shell frequency yields an incidence bound only after weighting seats. -/
theorem sum_lowerParitySafePersistentCount_le_cap (N T : ℕ) :
    (∑ i ∈ Finset.range T, lowerParitySafePersistentCount (N + i)) ≤
      lowerParitySafePersistenceCap N T := by
  classical
  let B := (primeScalesUpTo (N + T)).erase 2
  calc
    (∑ i ∈ Finset.range T, lowerParitySafePersistentCount (N + i)) ≤
        ∑ i ∈ Finset.range T,
          ∑ q ∈ B, if q ∣ oddGnomon (N + i) then
            (lowerPersistentSeatPool q (N + T)).card else 0 := by
      apply Finset.sum_le_sum
      intro i hi
      apply lowerParitySafePersistentCount_le_seatWeighted_addresses
      have := Finset.mem_range.mp hi
      omega
    _ = ∑ q ∈ B, (lowerPersistentSeatPool q (N + T)).card *
        (lowerPrimeAddressOffsets q N T).card := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q hq
      simp only [lowerPrimeAddressOffsets, Finset.card_filter, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases ha : q ∣ oddGnomon (N + i) <;> simp [ha]
    _ ≤ ∑ q ∈ B, (lowerPersistentSeatPool q (N + T)).card * shellFrequencyCap q T := by
      apply Finset.sum_le_sum
      intro q hq
      have hb := Finset.mem_erase.mp hq
      apply Nat.mul_le_mul_left
      exact lowerPrimeAddressOffsets_card_le (mem_primeScalesUpTo.mp hb.2).1 hb.1 N T
    _ = lowerParitySafePersistenceCap N T := rfl

/-- A checked fresh-incidence bound for the actual lower sector, without full cover. -/
theorem sum_lowerParitySafeIncidenceCount_sub_cap_le_fresh (N T : ℕ) :
    (∑ i ∈ Finset.range T, lowerParitySafeIncidenceCount (N + i)) -
        lowerParitySafePersistenceCap N T ≤
      ∑ i ∈ Finset.range T, lowerParitySafeFreshCount (N + i) := by
  have hsplit : (∑ i ∈ Finset.range T, lowerParitySafeIncidenceCount (N + i)) =
      (∑ i ∈ Finset.range T, lowerParitySafePersistentCount (N + i)) +
        ∑ i ∈ Finset.range T, lowerParitySafeFreshCount (N + i) := by
    simp_rw [lowerParitySafeIncidenceCount_eq_persistent_add_fresh]
    rw [Finset.sum_add_distrib]
  have hcap := sum_lowerParitySafePersistentCount_le_cap N T
  omega

/-- Under the existing full-cover predicate, each lower candidate requires an incidence. -/
theorem lowerParitySafeCandidates_card_le_incidence_of_fullyCovered
    {n : ℕ} (hfull : SquareOffsetsFullyCovered (n + 1)) :
    (lowerParitySafeCandidates n).card ≤ lowerParitySafeIncidenceCount n := by
  classical
  calc
    (lowerParitySafeCandidates n).card = ∑ r ∈ lowerParitySafeCandidates n, 1 := by simp
    _ ≤ lowerParitySafeIncidenceCount n := by
      apply Finset.sum_le_sum
      intro r hr
      have hseat := (Finset.mem_filter.mp hr).1
      have hs := squareOffset_of_mem_squareAnchorOddPointCoprimeOffsets hseat
      have hnondiv := (squareOffsetAnchorNondivisorSupport_nonempty_iff_covered_of_candidate
        (by omega : 0 < n + 1) hseat).mpr (hfull r hs)
      rw [squareOffsetAnchorNondivisorSupport_eq_paritySafeActiveSupport_of_candidate hseat]
        at hnondiv
      exact Finset.card_pos.mpr hnondiv

/-- Simultaneous full cover forces this bounded lower-sector fresh-incidence count.
It does not compare fresh incidences with the residual capacities of the frontier. -/
theorem sum_lowerParitySafeCandidates_sub_cap_le_fresh_of_fullyCovered
    (N T : ℕ)
    (hfull : ∀ i ∈ Finset.range T, SquareOffsetsFullyCovered (N + i + 1)) :
    (∑ i ∈ Finset.range T, (lowerParitySafeCandidates (N + i)).card) -
        lowerParitySafePersistenceCap N T ≤
      ∑ i ∈ Finset.range T, lowerParitySafeFreshCount (N + i) := by
  have hneed : (∑ i ∈ Finset.range T, (lowerParitySafeCandidates (N + i)).card) ≤
      ∑ i ∈ Finset.range T, lowerParitySafeIncidenceCount (N + i) := by
    apply Finset.sum_le_sum
    intro i hi
    exact lowerParitySafeCandidates_card_le_incidence_of_fullyCovered (hfull i hi)
  exact (Nat.sub_le_sub_right hneed _).trans
    (sum_lowerParitySafeIncidenceCount_sub_cap_le_fresh N T)

end DkMath.NumberTheory.Legendre
