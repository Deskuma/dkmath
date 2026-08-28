/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.PrimorialWheelBridge
import Mathlib.Tactic

#print "file: DkMath.NumberTheory.Legendre.PrimorialWheelSuccessor"

/-!
# Successor square-shell transition

This module decomposes the exact `n → n + 1` transition of the bounded prime
waves.  The old basis sees the successor shell through the shifted offsets
`2 * n + 2 ≤ s ≤ 4 * n + 3`; if `n + 1` is prime, its new direction removes
exactly the two offsets `n + 1` and `2 * (n + 1)`.  The resulting theorem is a
transition audit, not a propagation theorem from a full old shell to a full
successor shell.

The module reuses the PUU-L011 projected-survivor dictionary and does not
introduce square-hole propagation, gap bounds, PowerSwap, GN/CosmicFormula,
PNT, or RH.
-/

namespace DkMath.NumberTheory.Legendre

open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.PrimorialUniverse

/-! ## The bounded-prime basis transition -/

/-- The bounded prime basis either gains the threshold prime or stays fixed. -/
theorem primeScalesUpTo_succ_eq
    (n : ℕ) :
    primeScalesUpTo (n + 1) =
      if Nat.Prime (n + 1) then
        insert (n + 1) (primeScalesUpTo n)
      else
        primeScalesUpTo n := by
  by_cases hq : Nat.Prime (n + 1)
  · rw [if_pos hq]
    ext p
    simp only [mem_primeScalesUpTo, Finset.mem_insert]
    constructor
    · rintro ⟨hp, hple⟩
      by_cases heq : p = n + 1
      · exact Or.inl heq
      · exact Or.inr ⟨hp, by omega⟩
    · rintro (rfl | ⟨hp, hple⟩)
      · exact ⟨hq, le_rfl⟩
      · exact ⟨hp, by omega⟩
  · rw [if_neg hq]
    ext p
    simp only [mem_primeScalesUpTo]
    constructor
    · rintro ⟨hp, hple⟩
      by_cases heq : p = n + 1
      · exact (hq (by simpa [heq] using hp)).elim
      · exact ⟨hp, by omega⟩
    · rintro ⟨hp, hple⟩
      exact ⟨hp, by omega⟩

/-! ## Old-basis view of the successor shell -/

/-- Reservation of a successor-shell point by the old bounded basis. -/
def SuccessorOldBasisReserved (n r : ℕ) : Prop :=
  ReservedByPrimeBasis (primeScalesUpTo n) ((n + 1) ^ 2 + r)

/-- The successor square shell is the old square anchor with a shifted offset. -/
theorem successorOldBasisReserved_iff_shiftedOffset
    {n r : ℕ} :
    SuccessorOldBasisReserved n r ↔
      ReservedByPrimeBasis (primeScalesUpTo n)
        (n ^ 2 + (2 * n + 1 + r)) := by
  unfold SuccessorOldBasisReserved
  rw [show (n + 1) ^ 2 + r = n ^ 2 + (2 * n + 1 + r) by ring]

/-- Successor-shell offsets land in the shifted old-basis window. -/
theorem squareOffset_succ_shiftedOffset_range
    {n r : ℕ} (hr : SquareOffset (n + 1) r) :
    2 * n + 2 ≤ 2 * n + 1 + r ∧
      2 * n + 1 + r ≤ 4 * n + 3 := by
  dsimp [SquareOffset] at hr
  omega

/-! ## Exact cover decomposition -/

/-- Successor coverage is old-basis reservation or threshold-prime reservation. -/
theorem squareOffsetCovered_succ_iff_old_or_threshold
    {n r : ℕ} :
    SquareOffsetCovered (n + 1) r ↔
      SuccessorOldBasisReserved n r ∨
        (Nat.Prime (n + 1) ∧ (n + 1) ∣ r) := by
  unfold SquareOffsetCovered SuccessorOldBasisReserved
    SquareOffsetForbiddenBy
  constructor
  · rintro ⟨q, hqmem, hqdiv⟩
    have hqdata := mem_primeScalesUpTo.mp hqmem
    by_cases hqeq : q = n + 1
    · right
      refine ⟨by simpa [hqeq] using hqdata.1, ?_⟩
      rw [hqeq] at hqdiv
      exact (Nat.dvd_add_right (by
        rw [pow_two]
        exact dvd_mul_right (n + 1) (n + 1))).mp hqdiv
    · left
      refine ⟨q, mem_primeScalesUpTo.mpr ⟨hqdata.1, by omega⟩, hqdiv⟩
  · rintro (hold | ⟨hq, hqdiv⟩)
    · obtain ⟨q, hqmem, hqpoint⟩ := hold
      have hqdata := mem_primeScalesUpTo.mp hqmem
      exact ⟨q, mem_primeScalesUpTo.mpr
        ⟨hqdata.1, by omega⟩, hqpoint⟩
    · refine ⟨n + 1, mem_primeScalesUpTo.mpr ⟨hq, le_rfl⟩, ?_⟩
      apply (Nat.dvd_add_right (by
        rw [pow_two]
        exact dvd_mul_right (n + 1) (n + 1))).mpr
      exact hqdiv

/-! ## The two fresh threshold seats -/

/-- A prime threshold divides only the two offsets in its successor shell. -/
theorem successorThresholdPrime_dvd_iff
    {n r : ℕ}
    (hq : Nat.Prime (n + 1))
    (hr : SquareOffset (n + 1) r) :
    (n + 1) ∣ r ↔ r = n + 1 ∨ r = 2 * (n + 1) := by
  constructor
  · intro hdiv
    obtain ⟨k, hk⟩ := hdiv
    have hmul : (n + 1) * k ≤ (n + 1) * 2 := by
      rw [← hk]
      simpa [Nat.mul_comm] using hr.2
    have hk2 : k ≤ 2 := Nat.le_of_mul_le_mul_left hmul hq.pos
    have hkpos : 0 < k := by
      by_contra hk0
      have hkzero : k = 0 := Nat.eq_zero_of_not_pos hk0
      rw [hkzero] at hk
      have hrzero : r = 0 := by simpa using hk
      exact (Nat.not_succ_le_zero 0) (by simpa [hrzero] using hr.1)
    have hk_cases : k = 1 ∨ k = 2 := by
      revert hk2
      clear hmul
      clear hk
      omega
    rcases hk_cases with rfl | rfl
    · left
      simpa using hk
    · right
      simpa [Nat.mul_comm] using hk
  · rintro (rfl | rfl)
    · exact dvd_refl (n + 1)
    · rw [Nat.mul_comm 2 (n + 1)]
      exact dvd_mul_right (n + 1) 2

/-- Under a prime threshold, successor coverage has two explicit fresh seats. -/
theorem squareOffsetCovered_succ_iff_threshold
    {n r : ℕ}
    (hq : Nat.Prime (n + 1))
    (hr : SquareOffset (n + 1) r) :
    SquareOffsetCovered (n + 1) r ↔
      SuccessorOldBasisReserved n r ∨
        r = n + 1 ∨ r = 2 * (n + 1) := by
  rw [squareOffsetCovered_succ_iff_old_or_threshold,
    successorThresholdPrime_dvd_iff hq hr]
  simp [hq]

/-! ## Composite successor and projected-survivor transitions -/

/-- A composite successor adds no new bounded prime direction. -/
theorem squareOffsetCovered_succ_iff_old_of_not_prime
    {n r : ℕ} (hq : ¬ Nat.Prime (n + 1)) :
    SquareOffsetCovered (n + 1) r ↔
      SuccessorOldBasisReserved n r := by
  rw [squareOffsetCovered_succ_iff_old_or_threshold]
  simp [hq]

/-- In the prime-threshold case, survivor status removes the two threshold seats. -/
theorem successorProjectedSurvivor_iff_primeThreshold
    {n r : ℕ}
    (hq : Nat.Prime (n + 1))
    (hr : SquareOffset (n + 1) r) :
    IsPrimeBasisWheelSurvivor (primeScalesUpTo (n + 1))
        (squareShellWheelProjection (primeScalesUpTo (n + 1)) (n + 1) r) ↔
      ¬ SuccessorOldBasisReserved n r ∧
        r ≠ n + 1 ∧ r ≠ 2 * (n + 1) := by
  rw [← not_squareOffsetCovered_iff_projection_survivor hq.two_le]
  rw [squareOffsetCovered_succ_iff_threshold hq hr]
  simp only [not_or]

/-- In the composite case, successor survivor status is exactly old-basis escape. -/
theorem successorProjectedSurvivor_iff_composite
    {n r : ℕ}
    (hq : ¬ Nat.Prime (n + 1))
    (hn : 1 ≤ n)
    (_hr : SquareOffset (n + 1) r) :
    IsPrimeBasisWheelSurvivor (primeScalesUpTo (n + 1))
        (squareShellWheelProjection (primeScalesUpTo (n + 1)) (n + 1) r) ↔
      ¬ SuccessorOldBasisReserved n r := by
  rw [← not_squareOffsetCovered_iff_projection_survivor (by omega)]
  rw [squareOffsetCovered_succ_iff_old_of_not_prime hq]

/-! ## Full-cover frontier -/

/-- Prime-threshold full cover is old-basis cover plus the two threshold seats. -/
theorem squareOffsetsFullyCovered_succ_iff_primeThreshold
    {n : ℕ} (hq : Nat.Prime (n + 1)) :
    SquareOffsetsFullyCovered (n + 1) ↔
      ∀ r, SquareOffset (n + 1) r →
        SuccessorOldBasisReserved n r ∨
          r = n + 1 ∨ r = 2 * (n + 1) := by
  constructor
  · intro hfull r hr
    exact (squareOffsetCovered_succ_iff_threshold hq hr).mp (hfull r hr)
  · intro hcriterion r hr
    exact (squareOffsetCovered_succ_iff_threshold hq hr).mpr (hcriterion r hr)

/-- Composite-successor full cover is entirely old-basis cover. -/
theorem squareOffsetsFullyCovered_succ_iff_composite
    {n : ℕ} (hq : ¬ Nat.Prime (n + 1)) :
    SquareOffsetsFullyCovered (n + 1) ↔
      ∀ r, SquareOffset (n + 1) r → SuccessorOldBasisReserved n r := by
  constructor
  · intro hfull r hr
    exact (squareOffsetCovered_succ_iff_old_of_not_prime hq).mp (hfull r hr)
  · intro hcriterion r hr
    exact (squareOffsetCovered_succ_iff_old_of_not_prime hq).mpr
      (hcriterion r hr)

/-! ## Visible transition regression -/

/-- At `n = 4`, the new prime `5` covers the threshold offset `10`. -/
theorem successorThresholdRegression_four_ten :
    ¬ SuccessorOldBasisReserved 4 10 ∧
      SquareOffsetCovered 5 10 := by
  have hq : Nat.Prime (4 + 1) := by norm_num
  have hr : SquareOffset (4 + 1) 10 := by norm_num [SquareOffset]
  have htransition := squareOffsetCovered_succ_iff_threshold hq hr
  constructor
  · intro h
    obtain ⟨p, hp, hpdvd⟩ := h
    have hple : p ≤ 4 := (mem_primeScalesUpTo.mp hp).2
    interval_cases p <;> norm_num at hp <;> norm_num at hpdvd
  · exact htransition.mpr (Or.inr (Or.inr rfl))

end DkMath.NumberTheory.Legendre
