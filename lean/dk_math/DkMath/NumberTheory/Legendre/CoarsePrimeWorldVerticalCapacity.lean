/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.CoarsePrimeWorldFullTown

#print "file: DkMath.NumberTheory.Legendre.CoarsePrimeWorldVerticalCapacity"

/-! Exact vertical congruence, ceiling occupancy, and full-cover capacity. -/

namespace DkMath.NumberTheory.Legendre

open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.StructuralArithmetic
open DkMath.NumberTheory.PrimorialUniverse
open scoped BigOperators

/-- A common outside direction forces congruence of street indices. -/
theorem coarseColumn_commonPrime_modEq {S : Finset ℕ} (hS : KnownPrimeScales S)
    {n r q j k : ℕ} (hq : q.Prime) (hqS : q ∉ S)
    (hj : q ∣ n ^ 2 + r + j * primeWorldModulus S)
    (hk : q ∣ n ^ 2 + r + k * primeWorldModulus S) : Nat.ModEq q j k := by
  have hm : Nat.ModEq q (j * primeWorldModulus S) (k * primeWorldModulus S) :=
    Nat.ModEq.add_left_cancel' (n ^ 2 + r) (hj.modEq_zero_nat.trans hk.modEq_zero_nat.symm)
  exact Nat.ModEq.cancel_right_of_coprime
    (prime_coprime_primeWorldModulus_of_not_mem hS hq hqS) hm

theorem coarseColumn_commonPrime_dvd_index_gap {S : Finset ℕ} (hS : KnownPrimeScales S)
    {n r q j k : ℕ} (hq : q.Prime) (hqS : q ∉ S)
    (hj : q ∣ n ^ 2 + r + j * primeWorldModulus S)
    (hk : q ∣ n ^ 2 + r + k * primeWorldModulus S) : q ∣ k - j :=
  (coarseColumn_commonPrime_modEq hS hq hqS hj hk).dvd'

theorem coarseColumn_no_commonPrime_of_small_gap {S : Finset ℕ} (hS : KnownPrimeScales S)
    {n r q j k : ℕ} (hq : q.Prime) (hqS : q ∉ S) (hjk : j < k) (hgap : k - j < q) :
    ¬ (q ∣ n ^ 2 + r + j * primeWorldModulus S ∧
      q ∣ n ^ 2 + r + k * primeWorldModulus S) := by
  intro h
  have hz := Nat.eq_zero_of_dvd_of_lt
    (coarseColumn_commonPrime_dvd_index_gap hS hq hqS h.1 h.2) hgap
  omega

/-- Entire columns satisfy the existing old-support family predicate when outside waves are sparse. -/
theorem coarseColumn_oldSupport_family {S : Finset ℕ} (hS : KnownPrimeScales S) {n r : ℕ}
    (hr : r ∈ coarsePrimeWorldBase S n)
    (hlarge : ∀ q ∈ coarseOutsidePrimes S n, coarsePrimeWorldPeriodCount S n ≤ q) :
    PairwiseOldSupportDisjointSquareSeatFamily n (coarsePrimeWorldColumn S n r) := by
  constructor
  · intro a ha
    exact mem_squareOffsets.mp
      (coarseFullTown_subset_squareOffsets S n (coarseColumn_subset_fullTown hr ha))
  · intro a ha b hb hab
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hb
    change Disjoint (squareOffsetPrimeSupport n (r + j * primeWorldModulus S))
      (squareOffsetPrimeSupport n (r + k * primeWorldModulus S))
    rw [Finset.disjoint_left]
    intro q hqj hqk
    have hq := mem_squareOffsetPrimeSupport.mp hqj
    have hjtown := coarseColumn_subset_fullTown hr (Finset.mem_image.mpr ⟨j, hj, rfl⟩)
    have hqT := coarse_survivor_support_outside (coarseFullTown_survivor hS hjtown) hqj
    have hmod := coarseColumn_commonPrime_modEq hS hq.1 (Finset.mem_sdiff.mp hqT).2
      (by simpa only [Nat.add_assoc] using hq.2.2)
      (by simpa only [Nat.add_assoc] using (mem_squareOffsetPrimeSupport.mp hqk).2.2)
    have he := hmod.eq_of_lt_of_lt
      (lt_of_lt_of_le (Finset.mem_range.mp hj) (hlarge q hqT))
      (lt_of_lt_of_le (Finset.mem_range.mp hk) (hlarge q hqT))
    exact hab (by rw [he])

/-- A cutoff bound suffices; no next-prime function is needed. -/
theorem coarseColumn_oldSupport_family_initial {P n r : ℕ}
    (hr : r ∈ coarsePrimeWorldBase (primeScalesUpTo P) n)
    (hK : coarsePrimeWorldPeriodCount (primeScalesUpTo P) n ≤ P + 1) :
    PairwiseOldSupportDisjointSquareSeatFamily n
      (coarsePrimeWorldColumn (primeScalesUpTo P) n r) := by
  apply coarseColumn_oldSupport_family (knownPrimeScales_primeScalesUpTo P) hr
  intro q hq
  have h := Finset.mem_sdiff.mp hq
  have hp := (mem_primeScalesUpTo.mp h.1).1
  have hP : P < q := by
    by_contra hle
    exact h.2 (mem_primeScalesUpTo.mpr ⟨hp, by omega⟩)
  omega

/-- Raw column wave indices; actual bounded support uses the same indices for an outside old prime. -/
def coarseColumnWaveIndices (S : Finset ℕ) (n r q : ℕ) : Finset ℕ :=
  (Finset.range (coarsePrimeWorldPeriodCount S n)).filter
    (fun j => q ∣ n ^ 2 + r + j * primeWorldModulus S)

/-- One residue class can occupy at most one index in each quotient bucket. -/
theorem card_coarseColumnWaveIndices_le_ceil {S : Finset ℕ} (hS : KnownPrimeScales S)
    (n r : ℕ) {q : ℕ} (hq : q.Prime) (hqS : q ∉ S) :
    (coarseColumnWaveIndices S n r q).card ≤
      (coarsePrimeWorldPeriodCount S n + q - 1) / q := by
  suffices (coarseColumnWaveIndices S n r q).card ≤
      (Finset.range ((coarsePrimeWorldPeriodCount S n + q - 1) / q)).card by
    simpa only [Finset.card_range] using this
  apply Finset.card_le_card_of_injOn (fun j => j / q)
  · intro j hj
    have h := Finset.mem_filter.mp hj
    have hjK := Finset.mem_range.mp h.1
    apply Finset.mem_range.mpr
    apply Nat.lt_of_succ_le
    apply (Nat.le_div_iff_mul_le hq.pos).mpr
    have hdiv := Nat.div_mul_le_self j q
    have hsub : coarsePrimeWorldPeriodCount S n + q - 1 + 1 =
        coarsePrimeWorldPeriodCount S n + q := by omega
    nlinarith
  · intro j hj k hk he
    have hj' := (Finset.mem_filter.mp hj).2
    have hk' := (Finset.mem_filter.mp hk).2
    have hm := coarseColumn_commonPrime_modEq hS hq hqS hj' hk'
    have hjrep := Nat.mod_add_div j q
    have hkrep := Nat.mod_add_div k q
    change j % q = k % q at hm
    change j / q = k / q at he
    rw [he] at hjrep
    omega

/-- The arithmetic child is exact at the complete parent, which need not be a canonical residue. -/
theorem coarseColumnPoint_eq_child (S : Finset ℕ) (n r j : ℕ) :
    n ^ 2 + r + j * primeWorldModulus S = primeWorldChild S (n ^ 2 + r) j := rfl

/-- Canonical refinement coordinates use the phased complete-point address and a block shift. -/
theorem coarseColumnPoint_eq_canonical_child (S : Finset ℕ) (n r j : ℕ) :
    n ^ 2 + r + j * primeWorldModulus S =
      primeWorldChild S ((n ^ 2 + r) % primeWorldModulus S)
        ((n ^ 2 + r) / primeWorldModulus S + j) := by
  have h := Nat.mod_add_div (n ^ 2 + r) (primeWorldModulus S)
  dsimp [primeWorldChild]
  nlinarith

/-- Refinement at the canonical complete-point parent needs the negative block-shift target. -/
theorem coarseColumn_dvd_iff_refinement_target (S : Finset ℕ) (n r j q : ℕ) :
    q ∣ n ^ 2 + r + j * primeWorldModulus S ↔
      (primeWorldChild S ((n ^ 2 + r) % primeWorldModulus S) j : ZMod q) =
        -(((n ^ 2 + r) / primeWorldModulus S * primeWorldModulus S : ℕ) : ZMod q) := by
  have he : n ^ 2 + r + j * primeWorldModulus S =
      primeWorldChild S ((n ^ 2 + r) % primeWorldModulus S) j +
        (n ^ 2 + r) / primeWorldModulus S * primeWorldModulus S := by
    have h := Nat.mod_add_div (n ^ 2 + r) (primeWorldModulus S)
    dsimp [primeWorldChild]
    nlinarith
  rw [← ZMod.natCast_eq_zero_iff, he, Nat.cast_add, add_eq_zero_iff_eq_neg]

/-- Existing target-child uniqueness supplies the exact phased vertical residue class. -/
theorem existsUnique_coarseColumnWaveIndex_mod_prime {S : Finset ℕ} (hS : KnownPrimeScales S)
    (n r : ℕ) {q : ℕ} (hq : q.Prime) (hqS : q ∉ S) :
    ∃! j : ℕ, j < q ∧ q ∣ n ^ 2 + r + j * primeWorldModulus S := by
  simpa only [coarseColumn_dvd_iff_refinement_target] using
    existsUnique_child_eq_target hS hq hqS
      (Nat.mod_lt (n ^ 2 + r) (coarsePrimeWorld_modulus_pos hS))
      (-(((n ^ 2 + r) / primeWorldModulus S * primeWorldModulus S : ℕ) : ZMod q))

/-- The shell prefix of the fresh-prime child family has at most one reserved index. -/
theorem card_coarseColumnWaveIndices_le_one {S : Finset ℕ} (hS : KnownPrimeScales S)
    (n r : ℕ) {q : ℕ} (hq : q.Prime) (hqS : q ∉ S)
    (hK : coarsePrimeWorldPeriodCount S n ≤ q) :
    (coarseColumnWaveIndices S n r q).card ≤ 1 := by
  obtain ⟨j, _hj, huniq⟩ := existsUnique_coarseColumnWaveIndex_mod_prime hS n r hq hqS
  apply Finset.card_le_one.mpr
  intro a ha b hb
  have ha' := Finset.mem_filter.mp ha
  have hb' := Finset.mem_filter.mp hb
  exact (huniq a ⟨lt_of_lt_of_le (Finset.mem_range.mp ha'.1) hK, ha'.2⟩).trans
    (huniq b ⟨lt_of_lt_of_le (Finset.mem_range.mp hb'.1) hK, hb'.2⟩).symm

/-- A fixed left seat does not change uniqueness of the compatible right street index. -/
theorem coarseCrossColumn_compatible_index_unique {S : Finset ℕ} (hS : KnownPrimeScales S)
    {n s q k l : ℕ} (hq : q.Prime) (hqS : q ∉ S)
    (hK : coarsePrimeWorldPeriodCount S n ≤ q)
    (hk : k < coarsePrimeWorldPeriodCount S n) (hl : l < coarsePrimeWorldPeriodCount S n)
    (hkd : q ∣ n ^ 2 + s + k * primeWorldModulus S)
    (hld : q ∣ n ^ 2 + s + l * primeWorldModulus S) : k = l :=
  (coarseColumn_commonPrime_modEq hS hq hqS hkd hld).eq_of_lt_of_lt
    (lt_of_lt_of_le hk hK) (lt_of_lt_of_le hl hK)

/-- Cross-column collisions retain the signed offset and street-index differences. -/
theorem coarseCrossColumn_commonPrime_signed_gap {S : Finset ℕ} {n r s j k q : ℕ}
    (hj : q ∣ n ^ 2 + r + j * primeWorldModulus S)
    (hk : q ∣ n ^ 2 + s + k * primeWorldModulus S) :
    (q : ℤ) ∣ ((s : ℤ) - r) + ((k : ℤ) - j) * primeWorldModulus S := by
  have h := (hj.modEq_zero_nat.trans hk.modEq_zero_nat.symm).dvd
  convert h using 1
  push_cast
  ring

/-- Actual old-prime seats in the complete-period town. -/
noncomputable def coarseFullTownPrimeFiber (S : Finset ℕ) (n q : ℕ) : Finset ℕ := by
  classical
  exact (coarsePrimeWorldFullTown S n).filter (fun a => q ∈ squareOffsetPrimeSupport n a)

theorem coarseFullTownPrimeFiber_eq_column_union {S : Finset ℕ} {n q : ℕ}
    (hq : q ∈ coarseOutsidePrimes S n) :
    coarseFullTownPrimeFiber S n q = (coarsePrimeWorldBase S n).biUnion
      (fun r => (coarseColumnWaveIndices S n r q).image (fun j => r + j * primeWorldModulus S)) := by
  classical
  have hqp := mem_primeScalesUpTo.mp (Finset.mem_sdiff.mp hq).1
  ext a
  constructor
  · intro ha
    have h := Finset.mem_filter.mp ha
    obtain ⟨r, hr, j, hj, he⟩ := mem_coarsePrimeWorldFullTown.mp h.1
    apply Finset.mem_biUnion.mpr
    refine ⟨r, hr, Finset.mem_image.mpr ⟨j, ?_, he⟩⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr hj, ?_⟩
    simpa only [Nat.add_assoc, he] using (mem_squareOffsetPrimeSupport.mp h.2).2.2
  · intro ha
    obtain ⟨r, hr, ha'⟩ := Finset.mem_biUnion.mp ha
    obtain ⟨j, hj, he⟩ := Finset.mem_image.mp ha'
    have h := Finset.mem_filter.mp hj
    apply Finset.mem_filter.mpr
    refine ⟨mem_coarsePrimeWorldFullTown.mpr ⟨r, hr, j, Finset.mem_range.mp h.1, he⟩,
      mem_squareOffsetPrimeSupport.mpr ⟨hqp.1, hqp.2, ?_⟩⟩
    simpa only [Nat.add_assoc, he] using h.2

theorem card_coarseFullTownPrimeFiber_le {S : Finset ℕ} (hS : KnownPrimeScales S)
    {n q : ℕ} (hq : q ∈ coarseOutsidePrimes S n) :
    (coarseFullTownPrimeFiber S n q).card ≤ (coarsePrimeWorldBase S n).card *
      ((coarsePrimeWorldPeriodCount S n + q - 1) / q) := by
  classical
  have h := Finset.mem_sdiff.mp hq
  have hp := (mem_primeScalesUpTo.mp h.1).1
  rw [coarseFullTownPrimeFiber_eq_column_union hq]
  calc
    _ ≤ ∑ r ∈ coarsePrimeWorldBase S n,
        ((coarseColumnWaveIndices S n r q).image (fun j => r + j * primeWorldModulus S)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _r ∈ coarsePrimeWorldBase S n,
        ((coarsePrimeWorldPeriodCount S n + q - 1) / q) := by
      apply Finset.sum_le_sum
      intro r _hr
      exact Finset.card_image_le.trans (card_coarseColumnWaveIndices_le_ceil hS n r hp h.2)
    _ = _ := by simp

theorem coarse_ceiling_le_one {K q : ℕ} (hq : 0 < q) (hK : K ≤ q) :
    (K + q - 1) / q ≤ 1 := by
  have h : K + q - 1 < 2 * q := by omega
  have hd := (Nat.div_lt_iff_lt_mul hq).mpr h
  omega

theorem card_coarseFullTownPrimeFiber_le_base {S : Finset ℕ} (hS : KnownPrimeScales S)
    {n q : ℕ} (hq : q ∈ coarseOutsidePrimes S n) (hK : coarsePrimeWorldPeriodCount S n ≤ q) :
    (coarseFullTownPrimeFiber S n q).card ≤ (coarsePrimeWorldBase S n).card := by
  have hp := (mem_primeScalesUpTo.mp (Finset.mem_sdiff.mp hq).1).1
  have h := card_coarseFullTownPrimeFiber_le hS hq
  have hc := Nat.mul_le_mul_left (coarsePrimeWorldBase S n).card (coarse_ceiling_le_one hp.pos hK)
  simpa only [Nat.mul_one] using h.trans hc

/-- Incidence counts actual support memberships. -/
noncomputable def coarseFullTownIncidence (S : Finset ℕ) (n : ℕ) : ℕ :=
  ∑ q ∈ coarseOutsidePrimes S n, (coarseFullTownPrimeFiber S n q).card

theorem coarseFullTownIncidence_eq_support_sum {S : Finset ℕ} (hS : KnownPrimeScales S) (n : ℕ) :
    coarseFullTownIncidence S n =
      ∑ a ∈ coarsePrimeWorldFullTown S n, (squareOffsetPrimeSupport n a).card := by
  classical
  unfold coarseFullTownIncidence
  simp only [coarseFullTownPrimeFiber, Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_boole]
  have he : (coarseOutsidePrimes S n).filter (fun q => q ∈ squareOffsetPrimeSupport n a) =
      squareOffsetPrimeSupport n a := by
    ext q
    have ht := coarse_survivor_support_outside (coarseFullTown_survivor hS ha)
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨ht h, h⟩⟩
  rw [he]
  simp only [Nat.cast_id]

theorem card_coarseFullTown_le_incidence_of_fullyCovered {S : Finset ℕ}
    (hS : KnownPrimeScales S) {n : ℕ} (hfull : SquareOffsetsFullyCovered n) :
    (coarsePrimeWorldFullTown S n).card ≤ coarseFullTownIncidence S n := by
  rw [coarseFullTownIncidence_eq_support_sum hS n]
  calc
    _ = ∑ a ∈ coarsePrimeWorldFullTown S n, 1 := by simp
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro a ha
      exact Finset.card_pos.mpr (squareOffsetCovered_iff_primeSupport_nonempty.mp
        (hfull a (mem_squareOffsets.mp (coarseFullTown_subset_squareOffsets S n ha))))

/-- The complete-period wave-capacity sum. -/
def coarseVerticalCapacity (S : Finset ℕ) (n : ℕ) : ℕ :=
  ∑ q ∈ coarseOutsidePrimes S n, (coarsePrimeWorldPeriodCount S n + q - 1) / q

theorem coarseFullTownIncidence_le_capacity {S : Finset ℕ} (hS : KnownPrimeScales S) (n : ℕ) :
    coarseFullTownIncidence S n ≤ (coarsePrimeWorldBase S n).card * coarseVerticalCapacity S n := by
  classical
  unfold coarseFullTownIncidence coarseVerticalCapacity
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun q hq => card_coarseFullTownPrimeFiber_le hS hq)

/-- Positive base cardinality cancels without analytic assumptions. -/
theorem coarseFullTown_vertical_frontier {S : Finset ℕ} (hS : KnownPrimeScales S) {n : ℕ}
    (hfull : SquareOffsetsFullyCovered n) :
    coarsePrimeWorldPeriodCount S n ≤ coarseVerticalCapacity S n := by
  have h := (card_coarseFullTown_le_incidence_of_fullyCovered hS hfull).trans
    (coarseFullTownIncidence_le_capacity hS n)
  rw [card_coarsePrimeWorldFullTown hS n, card_coarsePrimeWorldBase] at h
  have hp := Nat.totient_pos.mpr (coarsePrimeWorld_modulus_pos hS)
  nlinarith

theorem coarseFullTown_uniform_vertical_frontier {S : Finset ℕ} (hS : KnownPrimeScales S) {n : ℕ}
    (hlarge : ∀ q ∈ coarseOutsidePrimes S n, coarsePrimeWorldPeriodCount S n ≤ q)
    (hfull : SquareOffsetsFullyCovered n) :
    coarsePrimeWorldPeriodCount S n ≤ (coarseOutsidePrimes S n).card := by
  have h := coarseFullTown_vertical_frontier hS hfull
  have hs : coarseVerticalCapacity S n ≤ (coarseOutsidePrimes S n).card := by
    unfold coarseVerticalCapacity
    calc
      _ ≤ ∑ _q ∈ coarseOutsidePrimes S n, 1 := by
        apply Finset.sum_le_sum
        intro q hq
        exact coarse_ceiling_le_one
          (mem_primeScalesUpTo.mp (Finset.mem_sdiff.mp hq).1).1.pos (hlarge q hq)
      _ = _ := by simp
  exact h.trans hs

theorem not_fullyCovered_of_coarseVerticalCapacity_deficit {S : Finset ℕ}
    (hS : KnownPrimeScales S) {n : ℕ}
    (hdef : coarseVerticalCapacity S n < coarsePrimeWorldPeriodCount S n) :
    ¬ SquareOffsetsFullyCovered n :=
  fun hfull => (not_le_of_gt hdef) (coarseFullTown_vertical_frontier hS hfull)

/-- Consume a strict vertical deficit through the existing Frontier escape theorem. -/
theorem exists_prime_squareCell_of_coarseVerticalCapacity_deficit {S : Finset ℕ}
    (hS : KnownPrimeScales S) {n : ℕ} (hn : 0 < n)
    (hdef : coarseVerticalCapacity S n < coarsePrimeWorldPeriodCount S n) :
    ∃ p, p.Prime ∧ SquareCell n p := by
  have hnot := not_fullyCovered_of_coarseVerticalCapacity_deficit hS hdef
  obtain ⟨r, hr⟩ := not_squareOffsetsFullyCovered_iff_escaping_nonempty.mp hnot
  have hs := mem_escapingSquareOffsets.mp hr
  refine ⟨n ^ 2 + r, prime_of_squareAnchoredSupportEscape hn hs.1 ?_, ?_⟩
  · exact supportDisjointFrom_primeScalesUpTo_square_add_iff_not_covered.mpr hs.2
  · exact (squareCell_iff_exists_squareOffset n (n ^ 2 + r)).mpr ⟨r, hs.1, rfl⟩

end DkMath.NumberTheory.Legendre
