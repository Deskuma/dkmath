/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.QuadraticGnomonFold
import DkMath.NumberTheory.Legendre.GnomonPrimorialTransition
import DkMath.NumberTheory.Legendre.OldSupportGcd

#print "file: DkMath.NumberTheory.Legendre.CenteredOwnerFold"

/-! Least-owner folding is parity normalization; common nonleast support can persist. -/
namespace DkMath.NumberTheory.Legendre
open DkMath.NumberTheory.Primitive
open scoped BigOperators

/-- Opposite parity forces distinct least factors, even without covered-seat hypotheses. -/
theorem squareOffsetFold_owner_ne {n r : ℕ} (hr : SquareOffset n r) :
    squareResidueCoverOwner n r ≠ squareResidueCoverOwner n (squareOffsetFold n r) := by
  intro he
  have hf := squareOffsetFold_squareOffset hr
  have hsum : Odd ((n ^ 2 + r) + (n ^ 2 + squareOffsetFold n r)) := by
    refine ⟨n ^ 2 + n, ?_⟩
    have hs := squareOffsetFold_sum hr
    omega
  by_cases h2 : squareResidueCoverOwner n r = 2
  · have ho := (squareResidueCoverOwner_eq_two_iff hr).mp h2
    have hn := (squareResidueCoverOwner_eq_two_iff hf).mp (he.symm.trans h2)
    exact hsum.not_two_dvd_nat (dvd_add ho hn)
  · have ho : Odd (n ^ 2 + r) := Nat.not_even_iff_odd.mp (by
      intro h; exact h2 ((squareResidueCoverOwner_eq_two_iff hr).mpr h.two_dvd))
    have hn : Odd (n ^ 2 + squareOffsetFold n r) := Nat.not_even_iff_odd.mp (by
      intro h; exact h2 (he.trans ((squareResidueCoverOwner_eq_two_iff hf).mpr h.two_dvd)))
    exact hsum.not_two_dvd_nat (ho.add_odd hn).two_dvd

theorem centeredPair_owner_ne {n j : ℕ} (hj : j < n) :
    squareResidueCoverOwner n (centeredLeftOffset n j) ≠
      squareResidueCoverOwner n (centeredRightOffset n j) := by
  simpa [squareOffsetFold_centeredLeft hj] using
    squareOffsetFold_owner_ne (squareOffset_centeredLeftOffset hj)

/-- The requested same-owner divisibility implication is valid but vacuous for least owners. -/
theorem centered_same_owner_dvd_gap {n j : ℕ} (hj : j < n)
    (hl : SquareOffsetCovered n (centeredLeftOffset n j))
    (hr : SquareOffsetCovered n (centeredRightOffset n j))
    (he : squareResidueCoverOwner n (centeredLeftOffset n j) =
      squareResidueCoverOwner n (centeredRightOffset n j)) :
    squareResidueCoverOwner n (centeredLeftOffset n j) ∣ 2 * j + 1 := by
  have hd0 := (squareResidueCoverOwner_packet (squareOffset_centeredLeftOffset hj) hl).2.2.1
  have hd1 := (squareResidueCoverOwner_packet (squareOffset_centeredRightOffset hj) hr).2.2.1
  rw [← he] at hd1
  exact ((centeredCommonDivisor_iff hj).mp ⟨hd0, hd1⟩).2

/-- Reuse the old prime-gap support theorem; least-owner distinction needs no prime gap. -/
theorem centered_prime_gap_support_packet {n j : ℕ} (hj : j < n)
    (hp : (2 * j + 1).Prime) (hn : n < 2 * j + 1) :
    Disjoint (squareOffsetPrimeSupport n (centeredLeftOffset n j))
      (squareOffsetPrimeSupport n (centeredRightOffset n j)) ∧
    squareResidueCoverOwner n (centeredLeftOffset n j) ≠
      squareResidueCoverOwner n (centeredRightOffset n j) :=
  ⟨disjoint_squareOffsetPrimeSupport_centeredPair hj hp hn, centeredPair_owner_ne hj⟩

/-- Potential support addresses, reusing the old lower gnomon progression. -/
abbrev centeredOwnerGapCapacityIndices (n p : ℕ) : Finset ℕ := lowerPrimeAddressOffsets p 0 n

theorem mem_centeredOwnerGapCapacityIndices {n p j : ℕ} :
    j ∈ centeredOwnerGapCapacityIndices n p ↔ j < n ∧ p ∣ 2 * j + 1 := by
  simp [centeredOwnerGapCapacityIndices, lowerPrimeAddressOffsets, DkMath.Gnomon.oddGnomon]

theorem centeredOwnerGapCapacityIndices_two (n : ℕ) :
    centeredOwnerGapCapacityIndices n 2 = ∅ := by
  ext j
  simp only [mem_centeredOwnerGapCapacityIndices, Finset.notMem_empty, iff_false, not_and]
  intro _
  exact (DkMath.Gnomon.oddGnomon_odd j).not_two_dvd_nat

/-- Exact residue class, not a count of actual same least owners. -/
theorem centeredOwnerGapCapacityIndices_eq_residue {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    centeredOwnerGapCapacityIndices n p =
      (Finset.range n).filter (fun j => j % p = (p - 1) / 2) := by
  ext j
  simp only [centeredOwnerGapCapacityIndices, lowerPrimeAddressOffsets, Finset.mem_filter]
  rw [Nat.zero_add, dvd_oddGnomon_iff_modEq_half hp hp2]
  have hc : (p - 1) / 2 < p := by have := hp.pos; omega
  simp only [Nat.ModEq, Nat.mod_eq_of_lt hc]

/-- Exact floor capacity for odd old primes. -/
theorem centeredOwnerGapCapacityIndices_card {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    (centeredOwnerGapCapacityIndices n p).card = (n + (p - 1) / 2) / p := by
  let c := (p - 1) / 2
  have hpc : p = 2 * c + 1 := by
    obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
    dsimp [c]
    omega
  have hbound (k : ℕ) : k < (n + c) / p ↔ c + k * p < n := by
    rw [Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le hp.pos]
    rw [Nat.add_mul, one_mul]
    omega
  have hb : (Finset.range ((n + c) / p)).card = (centeredOwnerGapCapacityIndices n p).card := by
    apply Finset.card_bij (fun k _ => c + k * p)
    · intro k hk
      rw [mem_centeredOwnerGapCapacityIndices]
      refine ⟨(hbound k).mp (Finset.mem_range.mp hk), ?_⟩
      exact (dvd_oddGnomon_iff_eq_half_add_mul hp hp2).mpr ⟨k, rfl⟩
    · intro a ha b hb he
      have hm : a * p = b * p := by omega
      exact Nat.eq_of_mul_eq_mul_right hp.pos hm
    · intro j hj
      have hg := (mem_centeredOwnerGapCapacityIndices.mp hj)
      obtain ⟨k, he⟩ := (dvd_oddGnomon_iff_eq_half_add_mul hp hp2).mp hg.2
      exact ⟨k, Finset.mem_range.mpr ((hbound k).mpr (he ▸ hg.1)), he.symm⟩
  rw [Finset.card_range] at hb
  exact hb.symm

noncomputable def centeredSameOwnerIndices (n p : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range n).filter (fun j =>
    SquareOffsetCovered n (centeredLeftOffset n j) ∧
    SquareOffsetCovered n (centeredRightOffset n j) ∧
    squareResidueCoverOwner n (centeredLeftOffset n j) = p ∧
    squareResidueCoverOwner n (centeredRightOffset n j) = p)

theorem centeredSameOwnerIndices_subset_capacity (n p : ℕ) :
    centeredSameOwnerIndices n p ⊆ centeredOwnerGapCapacityIndices n p := by
  classical
  intro j hj
  obtain ⟨hjn, hl, hr, ho0, ho1⟩ := Finset.mem_filter.mp hj
  have hjn := Finset.mem_range.mp hjn
  rw [mem_centeredOwnerGapCapacityIndices]
  exact ⟨hjn, ho0 ▸ centered_same_owner_dvd_gap hjn hl hr (ho0.trans ho1.symm)⟩

theorem centeredSameOwnerIndices_empty (n p : ℕ) : centeredSameOwnerIndices n p = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro j hj
  obtain ⟨hjn, _, _, ho0, ho1⟩ := Finset.mem_filter.mp hj
  exact centeredPair_owner_ne (Finset.mem_range.mp hjn) (ho0.trans ho1.symm)

theorem centeredSameOwnerIndices_card_le {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    (centeredSameOwnerIndices n p).card ≤ (n + (p - 1) / 2) / p := by
  rw [← centeredOwnerGapCapacityIndices_card hp hp2]
  exact Finset.card_le_card (centeredSameOwnerIndices_subset_capacity n p)

theorem centeredSameOwnerIndices_sum (n : ℕ) :
    (∑ p ∈ primeScalesUpTo n, (centeredSameOwnerIndices n p).card) = 0 := by
  simp [centeredSameOwnerIndices_empty]

noncomputable def centeredDifferentOwnerIndices (n : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range n).filter (fun j =>
    SquareOffsetCovered n (centeredLeftOffset n j) ∧
    SquareOffsetCovered n (centeredRightOffset n j) ∧
    squareResidueCoverOwner n (centeredLeftOffset n j) ≠
      squareResidueCoverOwner n (centeredRightOffset n j))

theorem centeredDifferentOwnerIndices_eq_range_of_full {n : ℕ} (hf : SquareOffsetsFullyCovered n) :
    centeredDifferentOwnerIndices n = Finset.range n := by
  classical
  apply Finset.filter_eq_self.mpr
  intro j hj
  have hj := Finset.mem_range.mp hj
  exact ⟨hf _ (squareOffset_centeredLeftOffset hj), hf _ (squareOffset_centeredRightOffset hj),
    centeredPair_owner_ne hj⟩

theorem centeredDifferentOwnerIndices_card_of_full {n : ℕ} (hf : SquareOffsetsFullyCovered n) :
    (centeredDifferentOwnerIndices n).card = n := by
  rw [centeredDifferentOwnerIndices_eq_range_of_full hf, Finset.card_range]

/-- Fold then insert and insert then fold differ by exactly one seat. -/
theorem squareOffsetFold_successor_noncommuting {n r : ℕ} (hr : SquareOffset n r) :
    squareOffsetFold (n + 1) (successorThresholdInsert n r) =
      successorThresholdInsert n (squareOffsetFold n r) + 1 := by
  dsimp [SquareOffset, squareOffsetFold, successorThresholdInsert] at hr ⊢
  split_ifs <;> omega

/-- Any divisor common to the two path endpoints must divide one. -/
theorem fold_successor_common_divisor_iff {n r q : ℕ} (hr : SquareOffset n r) :
    (q ∣ (n + 1) ^ 2 + squareOffsetFold (n + 1) (successorThresholdInsert n r) ∧
      q ∣ (n + 1) ^ 2 + successorThresholdInsert n (squareOffsetFold n r)) ↔ q = 1 := by
  rw [squareOffsetFold_successor_noncommuting hr]
  constructor
  · rintro ⟨ha, hb⟩
    have h1 : q ∣ 1 := (Nat.dvd_add_iff_right hb).mpr (by simpa [Nat.add_assoc] using ha)
    exact Nat.eq_one_of_dvd_one h1
  · rintro rfl; simp

theorem fold_successor_support_disjoint {n r : ℕ} (hr : SquareOffset n r) :
    Disjoint (squareOffsetPrimeSupport (n + 1)
      (squareOffsetFold (n + 1) (successorThresholdInsert n r)))
      (squareOffsetPrimeSupport (n + 1) (successorThresholdInsert n (squareOffsetFold n r))) := by
  rw [Finset.disjoint_left]
  intro p ha hb
  have a := mem_squareOffsetPrimeSupport.mp ha
  have b := mem_squareOffsetPrimeSupport.mp hb
  exact a.1.ne_one ((fold_successor_common_divisor_iff hr).mp ⟨a.2.2, b.2.2⟩)

/-- The cross-shell lower change and within-shell fold change are compatible. -/
theorem fold_lower_successor_owner_packet {n r : ℕ} (hr : SquareOffset n r) (hl : r < n + 1)
    (hc : SquareOffsetCovered n r)
    (hs : SquareOffsetCovered (n + 1) (successorThresholdInsert n r)) :
    squareResidueCoverOwner n r ≠ squareResidueCoverOwner n (squareOffsetFold n r) ∧
    squareResidueCoverOwner n r ≠
      squareResidueCoverOwner (n + 1) (successorThresholdInsert n r) :=
  ⟨squareOffsetFold_owner_ne hr, residue_owner_changes_lower hr hl hc hs⟩

end DkMath.NumberTheory.Legendre
