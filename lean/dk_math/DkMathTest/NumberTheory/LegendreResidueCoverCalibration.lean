/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMathTest.NumberTheory.LegendreResidueCoverRegression
import DkMathTest.NumberTheory.LegendreSqrtQuotientCalibration

#print "file: DkMathTest.NumberTheory.LegendreResidueCoverCalibration"

namespace DkMathTest.LegendreResidueCoverCalibration
open DkMath.NumberTheory.Legendre DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.PrimorialUniverse
open DkMathTest.LegendreResidueCoverRegression DkMathTest.LegendreSqrtQuotientCalibration
open scoped BigOperators

/-- The near-miss minimizing the survivor count among the inspected anchors n≥5. -/
theorem near_miss_five_escape : escapingSquareOffsets 5 = {4, 6} := by
  have hb : primeScalesUpTo 5 = {2, 3, 5} := by decide +kernel
  ext r
  simp only [mem_escapingSquareOffsets, SquareOffsetCovered, hb, SquareOffsetForbiddenBy]
  simp only [Finset.mem_insert, Finset.mem_singleton, exists_eq_or_imp, exists_eq_left]
  simp only [SquareOffset, Nat.dvd_iff_mod_eq_zero]
  by_cases hr : r ≤ 10
  · interval_cases r <;> norm_num at *
  · omega

theorem near_miss_five_survivors : squareShellWheelSurvivorImage 5 = {29, 1} := by
  rw [squareShell_survivor_filter_eq_image_escaping (by decide), near_miss_five_escape]
  decide +kernel

theorem near_miss_five_uncovered : (paritySafeUncoveredCandidates 5).card = 2 := by
  rw [← escapingSquareOffsets_eq_paritySafeUncovered (by decide : 2 ≤ 5), near_miss_five_escape]
  decide

theorem near_miss_five_anchor_image : squareAnchorWheelProjection (primeScalesUpTo 5) 5 = 25 ∧
    (squareShellWheelImage 5).card = 10 ∧ ¬SquareAnchorWheelFullyReserved 5 := by
  refine ⟨by decide +kernel, squareShellWheelImage_card_of_injective (Or.inr (Or.inr (by decide))), ?_⟩
  rw [squareAnchorWheelFullyReserved_iff_full, fullyCovered_iff_uncovered_empty (by decide),
    ← Finset.card_eq_zero, near_miss_five_uncovered]
  decide

/-- Connect the old structural certificate to every counterexample/wheel formulation.
The lower bound 18 is inherited, not a recomputation of the exact 160 escapes. -/
theorem residue1031_not_full : ¬SquareOffsetsFullyCovered 1031 := by
  intro hf
  have he := (fullyCovered_iff_uncovered_empty (by decide : 2 ≤ 1031)).mp hf
  have hl := quotient1031_uncovered_lower
  rw [he, Finset.card_empty] at hl
  omega

theorem residue1031_wheel_survivor : ∃ x ∈ squareShellWheelImage 1031,
    IsPrimeBasisWheelSurvivor (primeScalesUpTo 1031) x :=
  (not_fullyCovered_iff_wheel_image_survivor (by decide)).mp residue1031_not_full

theorem residue1031_projected_survivor_lower : 18 ≤ (squareShellWheelSurvivorImage 1031).card := by
  rw [squareShell_survivor_card_eq_uncovered (by decide)]
  exact quotient1031_uncovered_lower

theorem residue1031_corrected_balance_fails :
    (∑ p ∈ roughActiveLabels 1031 (Nat.sqrt 1031), (sqrtRoughQuotientFiber 1031 p).card) ≠
      (canonicalRoughCandidates 1031 (Nat.sqrt 1031)).card + (sqrtRoughRepeatedKeys 1031).card +
      2 * (sqrtRoughTripleProductsInShell 1031).card +
      ∑ p ∈ roughActiveLabels 1031 (Nat.sqrt 1031), (sqrtRoughRejectedFiber 1031 p).card :=
  fun he => residue1031_not_full ((fullyCovered_iff_corrected_balance (by decide)).mpr he)

theorem residue1031_preserved_endpoint : ∃ p, p.Prime ∧ SquareCell 1031 p :=
  quotient1031_structural_endpoint

end DkMathTest.LegendreResidueCoverCalibration
