/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.ParitySafeSqrtRoughFactorization
import DkMathTest.NumberTheory.LegendreBlockLocalization

#print "file: DkMathTest.NumberTheory.LegendreSqrtRoughMomentRegression"

namespace DkMathTest.LegendreSqrtRoughMomentRegression
set_option maxRecDepth 10000
open DkMath.NumberTheory.Legendre DkMath.NumberTheory
open DkMathTest.LegendreBlockLocalization DkMathTest.LegendreFreshCost

theorem four_labels_break_truncation :
    ¬ ((if (4 : ℕ) = 0 then 1 else 0) + 4 + Nat.choose 4 3 = 1 + Nat.choose 4 2) ∧
    ¬ ((4 - 1 : ℕ) + Nat.choose 4 3 = Nat.choose 4 2) := by
  decide

theorem tiny_anchor_zero :
    (canonicalRoughCandidates 0 (Nat.sqrt 0)).card = 0 ∧
    (paritySafeUncoveredCandidates 0).card = 0 := by
  constructor
  · rw [canonicalRoughCandidates, candidate_eq_filter_Icc]
    decide
  · rw [sqrt_uncovered_card_eq_moment_margin]
    simp only [canonicalRoughCandidates, candidate_eq_filter_Icc, roughPairMoment,
      roughTripleMoment, canonicalRoughWave, oddActive_eq_filter_range]
    decide

set_option maxRecDepth 10000 in
theorem false_raw_triple_key : (23, 31, 71) ∈ roughTriples 503 (Nat.sqrt 503) := by
  simp only [mem_roughTriples, roughActiveLabels, Finset.mem_filter, oddActive_eq_filter_range,
    Finset.mem_range]
  decide +kernel

theorem false_raw_triple_point : 503 ^ 2 + 106 = 5 * (23 * 31 * 71) := by decide

theorem false_raw_triple_candidate : 106 ∈ paritySafeProductWaveOffsets 503 (23 * 31 * 71) := by
  simp only [paritySafeProductWaveOffsets, candidate_eq_filter_Icc, Finset.mem_filter, Finset.mem_Icc]
  decide +kernel

theorem false_raw_triple_floor_count : primeAnchorProductWaveCount 503 (23 * 31 * 71) = 1 := by
  decide

/-- Exact factorization removes this old odd/coprime product-wave hit without enumerating rough seats. -/
theorem false_raw_triple_rough_empty :
    (roughTripleWave 503 (Nat.sqrt 503) 23 31 71).card = 0 := by
  rw [sqrt_roughTripleWave_card_eq_product_indicator false_raw_triple_key]
  decide

theorem triple_bound_sharp :
    24 ∈ canonicalRoughCandidates 19 (Nat.sqrt 19) ∧
    paritySafeActiveSupport 19 24 = {5, 7, 11} ∧ 19 ^ 2 + 24 = 5 * 7 * 11 := by
  simp only [canonicalRoughCandidates, candidate_eq_filter_Icc, paritySafeActiveSupport,
    SquareOffsetForbiddenBy, oddActive_eq_filter_range]
  decide +kernel

theorem triple_exact_factorization_probe : 19 ^ 2 + 24 = 5 * 7 * 11 := by
  apply sqrt_roughTriple_point_eq_product triple_bound_sharp.1
  · simp only [mem_roughTriples, roughActiveLabels, Finset.mem_filter, oddActive_eq_filter_range,
      Finset.mem_range]
    decide +kernel
  · rw [triple_bound_sharp.2.1, mem_upperTriples]
    decide

theorem two_support_lower_repeat :
    6 ∈ canonicalRoughCandidates 13 (Nat.sqrt 13) ∧
    paritySafeActiveSupport 13 6 = {5, 7} ∧ 13 ^ 2 + 6 = 5 ^ 2 * 7 := by
  simp only [canonicalRoughCandidates, candidate_eq_filter_Icc, paritySafeActiveSupport,
    SquareOffsetForbiddenBy, oddActive_eq_filter_range]
  decide +kernel

theorem two_support_upper_repeat :
    6 ∈ canonicalRoughCandidates 29 (Nat.sqrt 29) ∧
    paritySafeActiveSupport 29 6 = {7, 11} ∧ 29 ^ 2 + 6 = 7 * 11 ^ 2 := by
  simp only [canonicalRoughCandidates, candidate_eq_filter_Icc, paritySafeActiveSupport,
    SquareOffsetForbiddenBy, oddActive_eq_filter_range]
  decide +kernel

end DkMathTest.LegendreSqrtRoughMomentRegression
