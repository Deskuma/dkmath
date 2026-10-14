/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.CenteredPair
import DkMath.NumberTheory.Legendre.GnomonResidueCover

#print "file: DkMath.NumberTheory.Legendre.QuadraticGnomonFold"

/-! Exact half-lattice geometry and a finite unordered-pair normalization. -/
namespace DkMath.NumberTheory.Legendre
open scoped BigOperators

/-- Integer coordinates keep the negative left endpoint at n=0. -/
theorem centered_doubled_square_difference (n : ℤ) :
    (2 * n + 1) ^ 2 - (2 * n - 1) ^ 2 = 8 * n := by ring

/-- Nat needs positivity: at n=0 truncated subtraction would give 1. -/
theorem centered_doubled_square_difference_nat {n : ℕ} (hn : 0 < n) :
    (2 * n + 1) ^ 2 - (2 * n - 1) ^ 2 = 8 * n := by
  have he : (2 * n - 1) + 1 = 2 * n := by omega
  have hs : (2 * n - 1) ^ 2 + 8 * n = (2 * n + 1) ^ 2 := by nlinarith
  omega

theorem centered_doubled_square_difference_div_four {n : ℕ} (hn : 0 < n) :
    ((2 * n + 1) ^ 2 - (2 * n - 1) ^ 2) / 4 = 2 * n := by
  rw [centered_doubled_square_difference_nat hn]
  omega

/-- Translation of the centered integer window, with exact open endpoints. -/
theorem centered_window_translation (n m : ℕ) :
    m ∈ Finset.Icc (n ^ 2 - n + 1) (n ^ 2 + n) ↔ SquareCell n (m + n) := by
  have hsq : n ≤ n ^ 2 := by cases n <;> nlinarith
  have he : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
  rw [Finset.mem_Icc]
  unfold SquareCell
  rw [he]
  omega

theorem centered_window_card (n : ℕ) :
    (Finset.Icc (n ^ 2 - n + 1) (n ^ 2 + n)).card = 2 * n := by
  have hsq : n ≤ n ^ 2 := by cases n <;> nlinarith
  rw [Nat.card_Icc]
  omega

/-- Reflection around the half-integral midpoint n+1/2. -/
def squareOffsetFold (n r : ℕ) : ℕ := 2 * n + 1 - r

theorem squareOffsetFold_squareOffset {n r : ℕ} (hr : SquareOffset n r) :
    SquareOffset n (squareOffsetFold n r) := by
  dsimp [SquareOffset, squareOffsetFold] at hr ⊢
  omega

theorem squareOffsetFold_involutive {n r : ℕ} (hr : SquareOffset n r) :
    squareOffsetFold n (squareOffsetFold n r) = r := by
  dsimp [squareOffsetFold, SquareOffset] at hr ⊢
  omega

theorem squareOffsetFold_sum {n r : ℕ} (hr : SquareOffset n r) :
    r + squareOffsetFold n r = 2 * n + 1 := by
  dsimp [squareOffsetFold, SquareOffset] at hr ⊢
  omega

theorem squareOffsetFold_no_fixed {n r : ℕ} (hr : SquareOffset n r) :
    squareOffsetFold n r ≠ r := by
  have he := squareOffsetFold_sum hr
  omega

theorem squareOffsetFold_orbit_card {n r : ℕ} (hr : SquareOffset n r) :
    ({r, squareOffsetFold n r} : Finset ℕ).card = 2 := by
  simp [(squareOffsetFold_no_fixed hr).symm]

theorem squareOffsetFold_centeredLeft {n j : ℕ} (hj : j < n) :
    squareOffsetFold n (centeredLeftOffset n j) = centeredRightOffset n j := by
  dsimp [squareOffsetFold, centeredLeftOffset, centeredRightOffset]
  omega

theorem squareOffsetFold_centeredRight {n j : ℕ} (hj : j < n) :
    squareOffsetFold n (centeredRightOffset n j) = centeredLeftOffset n j := by
  dsimp [squareOffsetFold, centeredLeftOffset, centeredRightOffset]
  omega

/-- Existing CenteredPair coordinates, as an unordered two-seat fiber. -/
def centeredFoldPair (n j : ℕ) : Finset ℕ :=
  {centeredLeftOffset n j, centeredRightOffset n j}

def squareOffsetFoldPairs (n : ℕ) : Finset (Finset ℕ) :=
  (Finset.range n).image (centeredFoldPair n)

theorem centeredFoldPair_sum {n j : ℕ} (hj : j < n) :
    centeredLeftOffset n j + centeredRightOffset n j = 2 * n + 1 := by
  dsimp [centeredLeftOffset, centeredRightOffset]
  omega

theorem centeredFoldPair_card {n j : ℕ} (hj : j < n) :
    (centeredFoldPair n j).card = 2 := by
  rw [centeredFoldPair, ← squareOffsetFold_centeredLeft hj]
  exact squareOffsetFold_orbit_card (squareOffset_centeredLeftOffset hj)

theorem centeredFoldPair_injective (n : ℕ) :
    Set.InjOn (centeredFoldPair n) (Finset.range n) := by
  intro j hj k hk he
  have hj := Finset.mem_range.mp hj
  have hk := Finset.mem_range.mp hk
  have hm : centeredLeftOffset n j ∈ centeredFoldPair n k :=
    he ▸ Finset.mem_insert_self _ _
  simp only [centeredFoldPair, Finset.mem_insert, Finset.mem_singleton] at hm
  dsimp [centeredLeftOffset, centeredRightOffset] at hm
  omega

/-- Canonical pair index, without a quotient type. -/
theorem squareOffsetFold_pair_index {n r : ℕ} (hr : SquareOffset n r) :
    ∃! j, j < n ∧ {r, squareOffsetFold n r} = centeredFoldPair n j := by
  have hn : 0 < n := by dsimp [SquareOffset] at hr; omega
  have hex : ∃ j, j < n ∧ ({r, squareOffsetFold n r} : Finset ℕ) = centeredFoldPair n j := by
    by_cases hl : r ≤ n
    · refine ⟨n - r, by dsimp [SquareOffset] at hr; omega, ?_⟩
      have he : centeredLeftOffset n (n - r) = r := by
        dsimp [centeredLeftOffset]; omega
      have hf := squareOffsetFold_centeredLeft (show n - r < n by dsimp [SquareOffset] at hr; omega)
      rw [he] at hf
      simp only [centeredFoldPair, he, hf]
    · refine ⟨r - (n + 1), by dsimp [SquareOffset] at hr; omega, ?_⟩
      have he : centeredRightOffset n (r - (n + 1)) = r := by
        dsimp [centeredRightOffset]; omega
      have hf := squareOffsetFold_centeredRight
        (show r - (n + 1) < n by dsimp [SquareOffset] at hr; omega)
      rw [he] at hf
      simp only [centeredFoldPair, he, hf, Finset.pair_comm]
  obtain ⟨j, hj, he⟩ := hex
  refine ⟨j, ⟨hj, he⟩, ?_⟩
  intro k hk
  exact centeredFoldPair_injective n (Finset.mem_range.mpr hk.1)
    (Finset.mem_range.mpr hj) (hk.2.symm.trans he)

theorem squareOffsetFoldPairs_card (n : ℕ) : (squareOffsetFoldPairs n).card = n := by
  rw [squareOffsetFoldPairs, Finset.card_image_of_injOn (centeredFoldPair_injective n), Finset.card_range]

theorem centeredFoldPair_disjoint {n j k : ℕ} (hj : j < n) (hk : k < n) (he : j ≠ k) :
    Disjoint (centeredFoldPair n j) (centeredFoldPair n k) := by
  rw [Finset.disjoint_left]
  intro r hr hs
  simp only [centeredFoldPair, Finset.mem_insert, Finset.mem_singleton] at hr hs
  dsimp [centeredLeftOffset, centeredRightOffset] at hr hs
  omega

theorem centeredFoldPairs_union (n : ℕ) :
    (Finset.range n).biUnion (centeredFoldPair n) = squareOffsets n := by
  ext r
  rw [Finset.mem_biUnion, mem_squareOffsets]
  constructor
  · rintro ⟨j, hj, hr⟩
    have hj := Finset.mem_range.mp hj
    simp only [centeredFoldPair, Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact squareOffset_centeredLeftOffset hj
    · exact squareOffset_centeredRightOffset hj
  · intro hr
    obtain ⟨j, ⟨hj, he⟩, _⟩ := squareOffsetFold_pair_index hr
    exact ⟨j, Finset.mem_range.mpr hj, he ▸ Finset.mem_insert_self _ _⟩

/-- Internal odd gaps, up to 2n-1, not the outer gap 2n+1. -/
def centeredInternalGaps (n : ℕ) : Finset ℕ :=
  (Finset.range n).image DkMath.Gnomon.oddGnomon

theorem centered_offset_difference {n j : ℕ} (hj : j < n) :
    centeredRightOffset n j - centeredLeftOffset n j = DkMath.Gnomon.oddGnomon j := by
  have h := centeredPoint_difference hj
  unfold DkMath.Gnomon.oddGnomon
  omega

theorem centeredInternalGaps_eq_odd_interval (n : ℕ) :
    centeredInternalGaps n = (Finset.Icc 1 (2 * n - 1)).filter Odd := by
  ext g
  rw [centeredInternalGaps, Finset.mem_image, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨j, hj, rfl⟩
    have hj := Finset.mem_range.mp hj
    exact ⟨by unfold DkMath.Gnomon.oddGnomon; omega, DkMath.Gnomon.oddGnomon_odd j⟩
  · rintro ⟨⟨hg, hgn⟩, j, he⟩
    refine ⟨j, Finset.mem_range.mpr ?_, ?_⟩
    · omega
    · unfold DkMath.Gnomon.oddGnomon; omega

theorem centeredInternalGaps_card (n : ℕ) : (centeredInternalGaps n).card = n := by
  rw [centeredInternalGaps, Finset.card_image_of_injective _ DkMath.Gnomon.oddGnomon_injective,
    Finset.card_range]

/-- The internal gap is the unit degree-two GN kernel at j, not at anchor n. -/
theorem centered_gap_eq_GTail {n j : ℕ} (hj : j < n) :
    centeredRightOffset n j - centeredLeftOffset n j =
      DkMath.CosmicFormula.GTail 2 1 1 j := by
  rw [centered_offset_difference hj, DkMath.Gnomon.oddGnomon_eq_GTail_two_one_unit]

end DkMath.NumberTheory.Legendre
