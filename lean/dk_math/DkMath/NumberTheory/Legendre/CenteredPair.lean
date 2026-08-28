/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.PacketCoprimality

#print "file: DkMath.NumberTheory.Legendre.CenteredPair"

/-!
## CenteredPair

Exact centered pairing of the two offsets `n - j` and `n + 1 + j` in a
square shell.  The pair points differ by the odd gap `2 * j + 1`, so a
common old prime divisor must divide that gap.  This file records the
finite arithmetic and full-cover witness consequences only; it does not
claim a contradiction or prove Legendre's conjecture.
-/

namespace DkMath.NumberTheory.Legendre

open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.StructuralArithmetic

/-- The left offset in the centered pair around the midpoint of a shell. -/
def centeredLeftOffset (n j : ℕ) : ℕ := n - j

/-- The right offset in the centered pair around the midpoint of a shell. -/
def centeredRightOffset (n j : ℕ) : ℕ := n + 1 + j

/-! ### PRIM-L024.1: centered offsets in the square shell -/

/-- The left centered offset lies in the square shell when `j < n`. -/
theorem squareOffset_centeredLeftOffset
    {n j : ℕ} (hj : j < n) :
    SquareOffset n (centeredLeftOffset n j) := by
  dsimp [centeredLeftOffset, SquareOffset]
  omega

/-- The right centered offset lies in the square shell when `j < n`. -/
theorem squareOffset_centeredRightOffset
    {n j : ℕ} (hj : j < n) :
    SquareOffset n (centeredRightOffset n j) := by
  dsimp [centeredRightOffset, SquareOffset]
  omega

/-! ### PRIM-L024.2: exact point difference -/

/-- The right centered point is the left point plus the odd centered gap. -/
theorem centeredPoint_difference
    {n j : ℕ} (hj : j < n) :
    n ^ 2 + centeredRightOffset n j =
      (n ^ 2 + centeredLeftOffset n j) + (2 * j + 1) := by
  dsimp [centeredLeftOffset, centeredRightOffset]
  omega

/-! ### PRIM-L024.3: common-divisor reduction -/

/-- A common divisor of the centered points divides the odd centered gap. -/
theorem centeredCommonDivisor_iff
    {n j q : ℕ} (hj : j < n) :
    q ∣ n ^ 2 + centeredLeftOffset n j ∧
        q ∣ n ^ 2 + centeredRightOffset n j ↔
      q ∣ n ^ 2 + centeredLeftOffset n j ∧ q ∣ 2 * j + 1 := by
  constructor
  · rintro ⟨hleft, hright⟩
    refine ⟨hleft, ?_⟩
    rw [centeredPoint_difference hj] at hright
    exact (Nat.dvd_add_iff_right hleft).mpr hright
  · rintro ⟨hleft, hgap⟩
    refine ⟨hleft, ?_⟩
    rw [centeredPoint_difference hj]
    exact (Nat.dvd_add_iff_right hleft).mp hgap

/-! ### PRIM-L024.4: common old-prime support -/

/-- Common old-prime support is exactly support on the left and on the gap. -/
theorem mem_common_squareOffsetPrimeSupport_iff
    {n j q : ℕ} (hj : j < n) :
    q ∈ squareOffsetPrimeSupport n (centeredLeftOffset n j) ∧
        q ∈ squareOffsetPrimeSupport n (centeredRightOffset n j) ↔
      Nat.Prime q ∧ q ≤ n ∧
        q ∣ n ^ 2 + centeredLeftOffset n j ∧ q ∣ 2 * j + 1 := by
  constructor
  · rintro ⟨hleft, hright⟩
    have hleft' := mem_squareOffsetPrimeSupport.mp hleft
    have hright' := mem_squareOffsetPrimeSupport.mp hright
    have hgap := (centeredCommonDivisor_iff hj).mp
      ⟨hleft'.2.2, hright'.2.2⟩
    exact ⟨hleft'.1, hleft'.2.1, hleft'.2.2, hgap.2⟩
  · rintro ⟨hq, hqn, hleft, hgap⟩
    have hcommon := (centeredCommonDivisor_iff hj).mpr ⟨hleft, hgap⟩
    exact ⟨mem_squareOffsetPrimeSupport.mpr ⟨hq, hqn, hcommon.1⟩,
      mem_squareOffsetPrimeSupport.mpr ⟨hq, hqn, hcommon.2⟩⟩

/-! ### PRIM-L024.5: disjoint support for a prime centered gap -/

/-- A prime odd gap larger than the anchor prevents common old-prime support. -/
theorem disjoint_squareOffsetPrimeSupport_centeredPair
    {n j : ℕ}
    (hj : j < n)
    (hgap : Nat.Prime (2 * j + 1))
    (hn : n < 2 * j + 1) :
    Disjoint
      (squareOffsetPrimeSupport n (centeredLeftOffset n j))
      (squareOffsetPrimeSupport n (centeredRightOffset n j)) := by
  rw [Finset.disjoint_left]
  intro q hleft hright
  have hcommon := (mem_common_squareOffsetPrimeSupport_iff hj).mp
    ⟨hleft, hright⟩
  have hqgap : q = 2 * j + 1 :=
    ((Nat.dvd_prime hgap).mp hcommon.2.2.2).resolve_left hcommon.1.ne_one
  omega

/-! ### PRIM-L024.6: a full-cover consumer -/

/-- Full cover supplies distinct old-prime witnesses for a prime-gap pair. -/
theorem exists_distinct_centeredPair_primeSupport_of_fullyCovered
    {n j : ℕ}
    (hj : j < n)
    (hgap : Nat.Prime (2 * j + 1))
    (hn : n < 2 * j + 1)
    (hfull : SquareOffsetsFullyCovered n) :
    ∃ p q,
      p ≠ q ∧
      p ∈ squareOffsetPrimeSupport n (centeredLeftOffset n j) ∧
      q ∈ squareOffsetPrimeSupport n (centeredRightOffset n j) := by
  have hleftOffset := squareOffset_centeredLeftOffset hj
  have hrightOffset := squareOffset_centeredRightOffset hj
  obtain ⟨p, hp⟩ := squareOffsetCovered_iff_primeSupport_nonempty.mp
    (hfull _ hleftOffset)
  obtain ⟨q, hq⟩ := squareOffsetCovered_iff_primeSupport_nonempty.mp
    (hfull _ hrightOffset)
  refine ⟨p, q, ?_, hp, hq⟩
  intro hpq
  subst q
  exact (Finset.disjoint_left.mp
    (disjoint_squareOffsetPrimeSupport_centeredPair hj hgap hn)) hp hq

end DkMath.NumberTheory.Legendre
