/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Gnomon.CosmicBridge
import DkMath.NumberTheory.Legendre.Frontier

#print "file: DkMath.NumberTheory.Legendre.GnomonBridge"

/-!
# Legendre open unit-gnomon bridge

The offsets in the open interval between consecutive squares are exactly the
open interior of the unit square gnomon.  This module is a coordinate
identification and restatement layer only: it proves no new prime-existence,
full-cover, capacity, or Legendre result.
-/

namespace DkMath.NumberTheory.Legendre

open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.StructuralArithmetic
open scoped BigOperators

/-- Square offsets are the open interior of one neutral unit gnomon. -/
theorem squareOffset_iff_open_oddGnomon
    {n r : ℕ} :
    SquareOffset n r ↔
      1 ≤ r ∧ r < DkMath.Gnomon.oddGnomon n := by
  simp only [SquareOffset, DkMath.Gnomon.oddGnomon]
  omega

/-- The finite square-offset shell is the corresponding open gnomon interval. -/
theorem squareOffsets_eq_Ico_oddGnomon
    (n : ℕ) :
    squareOffsets n =
      Finset.Ico 1 (DkMath.Gnomon.oddGnomon n) := by
  ext r
  simp only [squareOffsets, Finset.mem_Icc, Finset.mem_Ico,
    DkMath.Gnomon.oddGnomon]
  omega

/-- The open unit-gnomon interval has the square shell's cardinality. -/
theorem card_open_oddGnomon_offsets (n : ℕ) :
    (Finset.Ico 1 (DkMath.Gnomon.oddGnomon n)).card = 2 * n := by
  rw [← squareOffsets_eq_Ico_oddGnomon]
  exact card_squareOffsets n

/-- The excluded upper gnomon endpoint is the next square. -/
theorem square_add_oddGnomon_eq_next_square
    (n : ℕ) :
    n ^ 2 + DkMath.Gnomon.oddGnomon n = (n + 1) ^ 2 :=
  DkMath.Gnomon.square_add_oddGnomon n

/-- A square cell is an open-gnomon offset from its lower square anchor. -/
theorem squareCell_iff_exists_open_oddGnomon_offset
    (n m : ℕ) :
    SquareCell n m ↔
      ∃ r,
        1 ≤ r ∧
        r < DkMath.Gnomon.oddGnomon n ∧
        m = n ^ 2 + r := by
  calc
    SquareCell n m ↔ ∃ r, SquareOffset n r ∧ m = n ^ 2 + r :=
      squareCell_iff_exists_squareOffset n m
    _ ↔ ∃ r,
          1 ≤ r ∧
          r < DkMath.Gnomon.oddGnomon n ∧
          m = n ^ 2 + r := by
      constructor
      · rintro ⟨r, hr, hmr⟩
        exact ⟨r, (squareOffset_iff_open_oddGnomon.mp hr).1,
          (squareOffset_iff_open_oddGnomon.mp hr).2, hmr⟩
      · rintro ⟨r, hlow, hhigh, hmr⟩
        exact ⟨r, squareOffset_iff_open_oddGnomon.mpr ⟨hlow, hhigh⟩, hmr⟩

/-- Square offsets can equivalently be written using the unit Cosmic shell. -/
theorem squareOffset_iff_open_GTail_two_one_unit
    {n r : ℕ} :
    SquareOffset n r ↔
      1 ≤ r ∧
      r < DkMath.CosmicFormula.GTail 2 1 1 n := by
  simpa only [DkMath.Gnomon.oddGnomon_eq_GTail_two_one_unit n] using
    (squareOffset_iff_open_oddGnomon (n := n) (r := r))

/-- Legendre's conjecture in open-gnomon prime coordinates. -/
theorem legendreConjecture_iff_open_oddGnomon_prime :
    LegendreConjecture ↔
      ∀ n : ℕ, 0 < n →
        ∃ p r,
          Nat.Prime p ∧
          1 ≤ r ∧
          r < DkMath.Gnomon.oddGnomon n ∧
          p = n ^ 2 + r := by
  unfold LegendreConjecture
  constructor
  · intro h n hn
    obtain ⟨p, hp, hcell⟩ := h n hn
    obtain ⟨r, hlow, hhigh, hpr⟩ :=
      (squareCell_iff_exists_open_oddGnomon_offset n p).mp hcell
    exact ⟨p, r, hp, hlow, hhigh, hpr⟩
  · intro h n hn
    obtain ⟨p, r, hp, hlow, hhigh, hpr⟩ := h n hn
    exact ⟨p, hp,
      (squareCell_iff_exists_open_oddGnomon_offset n p).mpr
        ⟨r, hlow, hhigh, hpr⟩⟩

/-- The existing support-escape provider in open unit-gnomon coordinates. -/
theorem squareAnchoredSupportEscape_iff_open_oddGnomon :
    SquareAnchoredSupportEscape ↔
      ∀ n : ℕ, 0 < n →
        ∃ r,
          1 ≤ r ∧
          r < DkMath.Gnomon.oddGnomon n ∧
          SupportDisjointFrom
            (primeScalesUpTo n)
            (n ^ 2 + r) := by
  unfold SquareAnchoredSupportEscape
  constructor
  · intro h n hn
    obtain ⟨r, hr, hdisj⟩ := h n hn
    obtain ⟨hlow, hhigh⟩ := squareOffset_iff_open_oddGnomon.mp hr
    exact ⟨r, hlow, hhigh, hdisj⟩
  · intro h n hn
    obtain ⟨r, hlow, hhigh, hdisj⟩ := h n hn
    exact ⟨r, squareOffset_iff_open_oddGnomon.mpr ⟨hlow, hhigh⟩, hdisj⟩

example : DkMath.Gnomon.oddGnomon 30 = 61 := by
  norm_num [DkMath.Gnomon.oddGnomon]

example : squareOffsets 30 = Finset.Ico 1 61 := by
  simpa [DkMath.Gnomon.oddGnomon] using squareOffsets_eq_Ico_oddGnomon 30

example : (squareOffsets 30).card = 60 := by
  simp

example : (30 : ℕ) ^ 2 + 61 = 31 ^ 2 := by
  norm_num

example : DkMath.Gnomon.oddGnomon 31 = 63 := by
  norm_num [DkMath.Gnomon.oddGnomon]

end DkMath.NumberTheory.Legendre
