/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.PrimorialWheelSuccessorEscape
import Mathlib.Tactic

#print "file: DkMath.NumberTheory.Legendre.PrimorialWheelTwinThreshold"

/-!
# Twin-threshold exception and exact old-escape classification

This module identifies the only old-basis escape that can be removed by the
fresh prime threshold.  The first threshold seat is already old-reserved, and
the second seat is an old-basis escape exactly when the next odd factor is
prime.  Thus the exceptional seat is precisely the twin-prime semiprime seat.

The results sharpen the L013 cardinality sufficient condition into an exact
finite criterion.  They do not assert that the shifted successor window has
any old-basis escape.

The module reuses the PUU-L011--L013 dictionaries and does not introduce
square-hole propagation, gap bounds, PowerSwap, GN/CosmicFormula, PNT, or RH.
-/

namespace DkMath.NumberTheory.Legendre

open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.PrimorialUniverse

/-! ## Existing Legendre escape vocabulary -/

/-- Projected successor escapes are the existing Legendre escaping offsets. -/
theorem successorProjectedEscapingOffsets_eq_escapingSquareOffsets
    {n : ℕ} (hn : 1 ≤ n) :
    successorProjectedEscapingOffsets n =
      escapingSquareOffsets (n + 1) := by
  classical
  ext r
  rw [mem_successorProjectedEscapingOffsets, mem_escapingSquareOffsets]
  constructor
  · rintro ⟨hsq, hsurv⟩
    exact ⟨hsq,
      (not_squareOffsetCovered_iff_projection_survivor (by omega)).mpr hsurv⟩
  · rintro ⟨hsq, hnot⟩
    exact ⟨hsq,
      (not_squareOffsetCovered_iff_projection_survivor (by omega)).mp hnot⟩

/-! ## The second threshold seat -/

/-- The second threshold seat escapes the old basis exactly at a twin prime. -/
theorem secondThreshold_not_oldReserved_iff_twinPrime
    {n : ℕ}
    (hn : 2 ≤ n)
    (hq : Nat.Prime (n + 1)) :
    (¬ SuccessorOldBasisReserved n (2 * (n + 1))) ↔
      Nat.Prime (n + 3) := by
  constructor
  · intro hnot
    by_contra hnotprime
    obtain ⟨p, hp, hpdvd⟩ :=
      Nat.exists_prime_and_dvd (by omega : n + 3 ≠ 1)
    obtain ⟨k, hk⟩ := hpdvd
    have hkpos : 0 < k := by
      by_contra hk0
      have hkzero : k = 0 := Nat.eq_zero_of_not_pos hk0
      rw [hkzero] at hk
      simp only [Nat.mul_zero] at hk
      have hmzero : n + 3 = 0 := hk
      omega
    have hkneone : k ≠ 1 := by
      intro hkone
      rw [hkone] at hk
      simp only [Nat.mul_one] at hk
      have hpeq : n + 3 = p := hk
      exact hnotprime (by simpa [hpeq] using hp)
    have hk2 : 2 ≤ k := by omega
    have hmul_le : p * 2 ≤ p * k := Nat.mul_le_mul_left p hk2
    have hple : p ≤ n := by omega
    have hreserve : SuccessorOldBasisReserved n (2 * (n + 1)) := by
      unfold SuccessorOldBasisReserved ReservedByPrimeBasis
      refine ⟨p, mem_primeScalesUpTo.mpr ⟨hp, hple⟩, ?_⟩
      refine ⟨(n + 1) * k, ?_⟩
      rw [show (n + 1) ^ 2 + 2 * (n + 1) = (n + 1) * (n + 3) by ring]
      rw [hk]
      ring
    exact hnot hreserve
  · intro htwin hreserve
    obtain ⟨p, hpmem, hpdvd⟩ := hreserve
    have hpdata := mem_primeScalesUpTo.mp hpmem
    rw [show (n + 1) ^ 2 + 2 * (n + 1) =
      (n + 1) * (n + 3) by ring] at hpdvd
    rcases (hpdata.1.dvd_mul.mp hpdvd) with hpq | hptwin
    · have hpeq : p = n + 1 :=
        ((Nat.dvd_prime hq).mp hpq).resolve_left hpdata.1.ne_one
      omega
    · have hpeq : p = n + 3 :=
        ((Nat.dvd_prime htwin).mp hptwin).resolve_left hpdata.1.ne_one
      omega

/-- Finset form of the twin-prime second-seat classification. -/
theorem secondThreshold_mem_oldEscape_iff_twinPrime
    {n : ℕ}
    (hn : 2 ≤ n)
    (hq : Nat.Prime (n + 1)) :
    2 * (n + 1) ∈ successorOldBasisEscapingOffsets n ↔
      Nat.Prime (n + 3) := by
  have hsq : SquareOffset (n + 1) (2 * (n + 1)) := by
    dsimp [SquareOffset]
    omega
  rw [mem_successorOldBasisEscapingOffsets]
  constructor
  · intro hmem
    exact (secondThreshold_not_oldReserved_iff_twinPrime hn hq).mp hmem.2
  · intro htwin
    exact ⟨hsq,
      (secondThreshold_not_oldReserved_iff_twinPrime hn hq).mpr htwin⟩

/-! ## Exact prime-threshold classification -/

/-- Away from the second seat, old escape is exactly projected escape. -/
theorem mem_successorProjectedEscapingOffsets_iff_old_ne_second
    {n r : ℕ}
    (hn : 2 ≤ n)
    (hq : Nat.Prime (n + 1)) :
    r ∈ successorProjectedEscapingOffsets n ↔
      r ∈ successorOldBasisEscapingOffsets n ∧
        r ≠ 2 * (n + 1) := by
  rw [successorProjectedEscapingOffsets_eq_erase_secondThreshold hn hq,
    Finset.mem_erase]
  simp [and_comm]

/-- Every non-deleted old escape is a prime point in the successor shell. -/
theorem prime_of_mem_successorOldBasisEscape_ne_second
    {n r : ℕ}
    (hn : 2 ≤ n)
    (hq : Nat.Prime (n + 1))
    (hr : r ∈ successorOldBasisEscapingOffsets n)
    (hne : r ≠ 2 * (n + 1)) :
    Nat.Prime ((n + 1) ^ 2 + r) := by
  have hproj : r ∈ successorProjectedEscapingOffsets n :=
    (mem_successorProjectedEscapingOffsets_iff_old_ne_second hn hq).mpr
      ⟨hr, hne⟩
  have hmem := mem_successorProjectedEscapingOffsets.mp hproj
  exact (squareOffset_prime_iff_projection_survivor (by omega) hmem.1).mpr hmem.2

/-- Old-basis escapes are projected escapes plus the optional twin-prime seat. -/
theorem successorOldBasisEscapingOffsets_eq_projected_union_twinSeat
    {n : ℕ}
    (hn : 2 ≤ n)
    (hq : Nat.Prime (n + 1)) :
    successorOldBasisEscapingOffsets n =
      successorProjectedEscapingOffsets n ∪
        (if Nat.Prime (n + 3) then
          {2 * (n + 1)}
        else
          ∅) := by
  classical
  ext r
  have hsecond := secondThreshold_mem_oldEscape_iff_twinPrime hn hq
  by_cases heq : r = 2 * (n + 1)
  · subst r
    have hproj : 2 * (n + 1) ∉ successorProjectedEscapingOffsets n := by
      rw [successorProjectedEscapingOffsets_eq_erase_secondThreshold hn hq]
      simp
    by_cases htwin : Nat.Prime (n + 3)
    · simp [hproj, hsecond.mpr htwin, htwin]
    · have hsecondnot : ¬ 2 * (n + 1) ∈ successorOldBasisEscapingOffsets n := by
        intro hmem
        exact htwin (hsecond.mp hmem)
      simp [hproj, hsecondnot, htwin]
  · have haway :=
      mem_successorProjectedEscapingOffsets_iff_old_ne_second hn hq
        (r := r)
    by_cases htwin : Nat.Prime (n + 3)
    · simp [haway, heq, htwin]
    · simp [haway, heq, htwin]

/-! ## Exact nonemptiness criteria -/

/-- Projected escape is exactly an old escape away from the second seat. -/
theorem successorProjectedEscapingOffsets_nonempty_iff_exists_old_ne_second
    {n : ℕ}
    (hn : 2 ≤ n)
    (hq : Nat.Prime (n + 1)) :
    (successorProjectedEscapingOffsets n).Nonempty ↔
      ∃ r ∈ successorOldBasisEscapingOffsets n,
        r ≠ 2 * (n + 1) := by
  constructor
  · rintro ⟨r, hr⟩
    have h := (mem_successorProjectedEscapingOffsets_iff_old_ne_second hn hq).mp hr
    exact ⟨r, h.1, h.2⟩
  · rintro ⟨r, hr, hne⟩
    exact ⟨r, (mem_successorProjectedEscapingOffsets_iff_old_ne_second hn hq).mpr
      ⟨hr, hne⟩⟩

/-- In the twin-prime case, projected nonemptiness is equivalent to two old escapes. -/
theorem successorProjectedEscapingOffsets_nonempty_iff_two_oldEscape_of_twinPrime
    {n : ℕ}
    (hn : 2 ≤ n)
    (hq : Nat.Prime (n + 1))
    (htwin : Nat.Prime (n + 3)) :
    (successorProjectedEscapingOffsets n).Nonempty ↔
      2 ≤ (successorOldBasisEscapingOffsets n).card := by
  rw [successorProjectedEscapingOffsets_eq_erase_secondThreshold hn hq]
  have hsecond := secondThreshold_mem_oldEscape_iff_twinPrime hn hq
  rw [Finset.erase_nonempty (hsecond.mpr htwin)]
  rw [← Finset.one_lt_card_iff_nontrivial]
  omega

/-- In the non-twin prime case, projected and old escape sets coincide. -/
theorem successorProjectedEscapingOffsets_eq_old_of_not_twinPrime
    {n : ℕ}
    (hn : 2 ≤ n)
    (hq : Nat.Prime (n + 1))
    (hntwin : ¬ Nat.Prime (n + 3)) :
    successorProjectedEscapingOffsets n =
      successorOldBasisEscapingOffsets n := by
  rw [successorProjectedEscapingOffsets_eq_erase_secondThreshold hn hq]
  rw [Finset.erase_eq_self.mpr]
  exact (secondThreshold_mem_oldEscape_iff_twinPrime hn hq).not.mpr hntwin

/-- In the non-twin prime case, old and projected nonemptiness coincide. -/
theorem successorProjectedEscapingOffsets_nonempty_iff_old_of_not_twinPrime
    {n : ℕ}
    (hn : 2 ≤ n)
    (hq : Nat.Prime (n + 1))
    (hntwin : ¬ Nat.Prime (n + 3)) :
    (successorProjectedEscapingOffsets n).Nonempty ↔
      (successorOldBasisEscapingOffsets n).Nonempty := by
  rw [successorProjectedEscapingOffsets_eq_old_of_not_twinPrime hn hq hntwin]

/-! ## Visible regression -/

/-- At `n = 4`, the twin-prime seat `10` is deleted by threshold `5`. -/
theorem successorTwinThresholdRegression_four :
    Nat.Prime (4 + 1) ∧ Nat.Prime (4 + 3) ∧
      10 ∈ successorOldBasisEscapingOffsets 4 ∧
      10 ∉ successorProjectedEscapingOffsets 4 := by
  have hn : 2 ≤ (4 : ℕ) := by norm_num
  have hq : Nat.Prime (4 + 1) := by norm_num
  have htwin : Nat.Prime (4 + 3) := by norm_num
  have hold := secondThreshold_mem_oldEscape_iff_twinPrime hn hq
  have hproj := successorProjectedEscapingOffsets_eq_erase_secondThreshold hn hq
  refine ⟨hq, htwin, hold.mpr htwin, ?_⟩
  rw [hproj]
  simp [hold.mpr htwin]

end DkMath.NumberTheory.Legendre
