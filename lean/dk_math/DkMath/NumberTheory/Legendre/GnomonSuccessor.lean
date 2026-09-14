/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: DkMath contributors.
-/

import DkMath.NumberTheory.Legendre.GnomonBridge
import DkMath.NumberTheory.Legendre.PrimorialWheelSuccessor
import Mathlib.Tactic

#print "file: DkMath.NumberTheory.Legendre.GnomonSuccessor"

/-!
# Successor gnomon balance and support firewall

This module audits the finite transition from the `n` square shell to the
`n + 1` square shell.  The two additional seats are exactly the seats reserved
by a fresh threshold prime, but the natural seat reindex does not preserve
old-basis support.  Instead, common support is constrained by the exact point
displacement.  No full-cover propagation or Legendre theorem is asserted.
-/

namespace DkMath.NumberTheory.Legendre

open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.PrimorialUniverse

/-! ## Exact shell balance -/

/-- The successor open shell has exactly two more seats. -/
theorem card_squareOffsets_succ_add_two (n : ℕ) :
    (squareOffsets (n + 1)).card = (squareOffsets n).card + 2 := by
  simp only [card_squareOffsets]
  omega

/-- The same two-seat growth in neutral gnomon coordinates. -/
theorem oddGnomon_succ_add_two (n : ℕ) :
    DkMath.Gnomon.oddGnomon (n + 1) =
      DkMath.Gnomon.oddGnomon n + 2 :=
  DkMath.Gnomon.oddGnomon_succ n

/-! ## Threshold seats -/

/-- The two offsets controlled by a prime threshold at `n + 1`. -/
def successorThresholdOffsets (n : ℕ) : Finset ℕ :=
  {n + 1, 2 * (n + 1)}

/-- The threshold seats lie in the successor open shell. -/
theorem successorThresholdOffsets_subset_squareOffsets_succ (n : ℕ) :
    successorThresholdOffsets n ⊆ squareOffsets (n + 1) := by
  intro r hr
  simp only [successorThresholdOffsets, Finset.mem_insert,
    Finset.mem_singleton] at hr
  rcases hr with rfl | rfl
  · apply mem_squareOffsets.mpr
    dsimp [SquareOffset]
    omega
  · apply mem_squareOffsets.mpr
    dsimp [SquareOffset]
    omega

/-- The two threshold seats are distinct. -/
@[simp] theorem card_successorThresholdOffsets (n : ℕ) :
    (successorThresholdOffsets n).card = 2 := by
  have hne : n + 1 ≠ 2 * (n + 1) := by omega
  simp [successorThresholdOffsets, hne]

/-- Under primality, threshold membership is exactly fresh-prime reservation. -/
theorem mem_successorThresholdOffsets_iff_threshold_dvd
    {n r : ℕ} (hq : Nat.Prime (n + 1))
    (hr : SquareOffset (n + 1) r) :
    r ∈ successorThresholdOffsets n ↔ (n + 1) ∣ r := by
  rw [successorThresholdPrime_dvd_iff hq hr]
  simp [successorThresholdOffsets]

/-- Removing the two fresh-prime seats restores the old shell cardinality. -/
theorem card_squareOffsets_succ_sdiff_threshold (n : ℕ) :
    (squareOffsets (n + 1) \ successorThresholdOffsets n).card =
      (squareOffsets n).card := by
  rw [Finset.card_sdiff_of_subset
    (successorThresholdOffsets_subset_squareOffsets_succ n)]
  rw [card_squareOffsets, card_successorThresholdOffsets]
  simp only [card_squareOffsets]
  omega

/-! ## The canonical threshold-skipping reindex -/

/-- Insert one seat after the fresh-prime threshold seat. -/
def successorThresholdInsert (n r : ℕ) : ℕ :=
  if r < n + 1 then r else r + 1

/-- Every old shell seat maps to a threshold-free successor seat. -/
theorem successorThresholdInsert_mem_sdiff
    {n r : ℕ} (hr : SquareOffset n r) :
    successorThresholdInsert n r ∈
      squareOffsets (n + 1) \ successorThresholdOffsets n := by
  apply Finset.mem_sdiff.mpr
  dsimp [SquareOffset] at hr
  constructor
  · apply mem_squareOffsets.mpr
    change 1 ≤ successorThresholdInsert n r ∧
      successorThresholdInsert n r ≤ 2 * (n + 1)
    by_cases h : r < n + 1
    · have hinsert : successorThresholdInsert n r = r := by
        simp [successorThresholdInsert, h]
      rw [hinsert]
      omega
    · have hinsert : successorThresholdInsert n r = r + 1 := by
        simp [successorThresholdInsert, h]
      rw [hinsert]
      omega
  · simp only [successorThresholdOffsets, Finset.mem_insert,
      Finset.mem_singleton]
    by_cases h : r < n + 1
    · rw [show successorThresholdInsert n r = r by
        simp [successorThresholdInsert, h]]
      omega
    · rw [show successorThresholdInsert n r = r + 1 by
        simp [successorThresholdInsert, h]]
      omega

/-! ## Same-offset support firewall -/

/-- A divisor common to adjacent same-offset points divides the unit gnomon. -/
theorem dvd_oddGnomon_of_dvd_adjacent_square_points
    {n r q : ℕ}
    (hold : q ∣ n ^ 2 + r)
    (hnew : q ∣ (n + 1) ^ 2 + r) :
    q ∣ DkMath.Gnomon.oddGnomon n := by
  have hstep : (n + 1) ^ 2 + r =
      (n ^ 2 + r) + DkMath.Gnomon.oddGnomon n := by
    rw [← DkMath.Gnomon.square_add_oddGnomon n]
    omega
  rw [hstep] at hnew
  exact (Nat.dvd_add_iff_right hold).mpr hnew

/-- An old prime not dividing the unit gnomon cannot persist at one offset. -/
theorem oldPrime_not_common_sameOffset
    {n r q : ℕ} (_hq : Nat.Prime q) (_hqle : q ≤ n)
    (hnot : ¬ q ∣ DkMath.Gnomon.oddGnomon n) :
    ¬ (q ∣ n ^ 2 + r ∧ q ∣ (n + 1) ^ 2 + r) := by
  intro hcommon
  exact hnot (dvd_oddGnomon_of_dvd_adjacent_square_points
    hcommon.1 hcommon.2)

/-! ## Reindex displacement firewall -/

/-- Lower-half reindexing has exactly the unit-gnomon displacement. -/
theorem successorThresholdInsert_lower_additive_displacement
    {n r : ℕ} (hr : r < n + 1) :
    (n + 1) ^ 2 + successorThresholdInsert n r =
      (n ^ 2 + r) + DkMath.Gnomon.oddGnomon n := by
  calc
    (n + 1) ^ 2 + successorThresholdInsert n r =
        (n + 1) ^ 2 + r := by simp [successorThresholdInsert, hr]
    _ = (n ^ 2 + DkMath.Gnomon.oddGnomon n) + r := by
      rw [DkMath.Gnomon.square_add_oddGnomon]
    _ = (n ^ 2 + r) + DkMath.Gnomon.oddGnomon n := by omega

/-- Upper-half reindexing has exactly the fresh-threshold displacement. -/
theorem successorThresholdInsert_upper_additive_displacement
    {n r : ℕ} (hr : n + 1 ≤ r) :
    (n + 1) ^ 2 + successorThresholdInsert n r =
      (n ^ 2 + r) + 2 * (n + 1) := by
  simp [successorThresholdInsert, not_lt_of_ge hr]
  ring

/-- Lower-half common support is forced into the unit gnomon. -/
theorem dvd_oddGnomon_of_dvd_reindexed_lower_common
    {n r q : ℕ} (hr : r < n + 1)
    (hold : q ∣ n ^ 2 + r)
    (hnew : q ∣ (n + 1) ^ 2 + successorThresholdInsert n r) :
    q ∣ DkMath.Gnomon.oddGnomon n := by
  apply dvd_oddGnomon_of_dvd_adjacent_square_points hold
  simpa [successorThresholdInsert, hr] using hnew

/-- Upper-half common support is forced into twice the fresh threshold. -/
theorem dvd_two_mul_succ_of_dvd_reindexed_upper_common
    {n r q : ℕ} (hr : n + 1 ≤ r)
    (hold : q ∣ n ^ 2 + r)
    (hnew : q ∣ (n + 1) ^ 2 + successorThresholdInsert n r) :
    q ∣ 2 * (n + 1) := by
  have hshift : q ∣ (n ^ 2 + r) + 2 * (n + 1) := by
    rw [successorThresholdInsert_upper_additive_displacement hr] at hnew
    exact hnew
  exact (Nat.dvd_add_iff_right hold).mpr hshift

/-! ## The required 30 -> 31 boundary -/

theorem primeScalesUpTo_31_eq_insert :
    primeScalesUpTo 31 = insert 31 (primeScalesUpTo 30) := by
  simpa [show Nat.Prime (30 + 1) by norm_num] using
    (primeScalesUpTo_succ_eq 30)

theorem successorThresholdOffsets_30_eq :
    successorThresholdOffsets 30 = ({31, 62} : Finset ℕ) := by
  norm_num [successorThresholdOffsets]

theorem card_squareOffsets_31_sdiff_threshold_30 :
    (squareOffsets 31 \ successorThresholdOffsets 30).card = 60 := by
  rw [card_squareOffsets_succ_sdiff_threshold]
  norm_num

/-- The first concrete mismatch: coverage is not preserved by the reindex. -/
theorem successor_reindex_30_6_mismatch :
    SquareOffsetCovered 30 6 ∧
      ¬ SuccessorOldBasisReserved 30 (successorThresholdInsert 30 6) := by
  have hcovered : SquareOffsetCovered 30 6 := by
    refine ⟨2, ?_, ?_⟩
    · norm_num [mem_primeScalesUpTo]
    · norm_num [SquareOffsetForbiddenBy]
  have hnot : ¬ SuccessorOldBasisReserved 30 6 := by
    norm_num [SuccessorOldBasisReserved, ReservedByPrimeBasis,
      primeScalesUpTo]
    intro q hqle hq hqd
    interval_cases q <;> norm_num at hq <;> norm_num at hqd
  simpa [successorThresholdInsert] using And.intro hcovered hnot

/-- The reverse concrete mismatch: noncoverage becomes old-basis coverage. -/
theorem successor_reindex_30_7_mismatch :
    ¬ SquareOffsetCovered 30 7 ∧
      SuccessorOldBasisReserved 30 (successorThresholdInsert 30 7) := by
  have hnot : ¬ SquareOffsetCovered 30 7 := by
    norm_num [SquareOffsetCovered, SquareOffsetForbiddenBy,
      primeScalesUpTo]
    intro q hqle hq hqd
    interval_cases q <;> norm_num at hq <;> norm_num at hqd
  have hreserved : SuccessorOldBasisReserved 30 7 := by
    refine ⟨2, ?_, ?_⟩
    · norm_num [mem_primeScalesUpTo]
    · norm_num [SquareOffsetForbiddenBy]
  simpa [successorThresholdInsert] using And.intro hnot hreserved

/-- At 30 -> 31, lower-half common old support must divide 61. -/
theorem oldPrime_30_not_common_lower_reindex
    {r q : ℕ} (hr : r < 31) (hq : Nat.Prime q) (hqle : q ≤ 30) :
    ¬ (q ∣ 30 ^ 2 + r ∧
      q ∣ 31 ^ 2 + successorThresholdInsert 30 r) := by
  have hnot : ¬ q ∣ 61 := by
    intro hq61
    have hq2 : 2 ≤ q := hq.two_le
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 61)).mp hq61 with hqone | hqeq
    · omega
    · omega
  intro hcommon
  apply hnot
  simpa [DkMath.Gnomon.oddGnomon] using
    dvd_oddGnomon_of_dvd_reindexed_lower_common hr hcommon.1 hcommon.2

/-- At 30 -> 31, upper-half common old support must divide 62. -/
theorem oldPrime_30_common_upper_reindex_dvd_62
    {r q : ℕ} (hr : 31 ≤ r)
    (hold : q ∣ 30 ^ 2 + r)
    (hnew : q ∣ 31 ^ 2 + successorThresholdInsert 30 r) :
    q ∣ 62 := by
  simpa using dvd_two_mul_succ_of_dvd_reindexed_upper_common hr hold hnew

end DkMath.NumberTheory.Legendre
