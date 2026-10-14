/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.ParitySafeSqrtRoughCensus
import DkMathTest.NumberTheory.LegendreBlockLocalization

#print "file: DkMathTest.NumberTheory.LegendreSqrtRoughCensusRegression"

namespace DkMathTest.LegendreSqrtRoughCensusRegression
open DkMath.NumberTheory.Legendre DkMathTest.LegendreBlockLocalization
set_option maxRecDepth 10000

theorem cube_key_five : 3 ∈ sqrtRoughCubeKeys 5 := by
  simp only [sqrtRoughCubeKeys, roughActiveLabels, Finset.mem_filter, oddActive_eq_filter_range]
  decide +kernel

theorem cube_seat_five : 2 ∈ roughSingletonSeats 5 ∧ paritySafeActiveSupport 5 2 = {3} :=
  sqrt_cube_offset_packet cube_key_five

theorem cross_key_seven : (3, 17) ∈ sqrtRoughCrossKeys 7 := by
  rw [mem_sqrtRoughCrossKeys]
  simp only [roughActiveLabels, Finset.mem_filter, oddActive_eq_filter_range]
  decide +kernel

theorem cross_seat_seven : 2 ∈ roughSingletonSeats 7 ∧ paritySafeActiveSupport 7 2 = {3} :=
  sqrt_cross_offset_packet cross_key_seven

theorem external_cofactor_is_not_active : 17 ∉ squareAnchorOddActivePrimes 7 := by
  simp only [mem_squareAnchorOddActivePrimes]
  decide

theorem repeated_lower_key : ((5, 7), false) ∈ sqrtRoughRepeatedKeys 13 := by
  simp only [sqrtRoughRepeatedKeys, sqrtRepeatedProduct]
  decide +kernel

theorem repeated_upper_key : ((7, 11), true) ∈ sqrtRoughRepeatedKeys 29 := by
  simp only [sqrtRoughRepeatedKeys, sqrtRepeatedProduct]
  decide +kernel

theorem repeated_lower_seat : 6 ∈ roughDoubleSeats 13 ∧ paritySafeActiveSupport 13 6 = {5, 7} :=
  sqrt_repeated_offset_packet repeated_lower_key

theorem repeated_upper_seat : 6 ∈ roughDoubleSeats 29 ∧ paritySafeActiveSupport 29 6 = {7, 11} :=
  sqrt_repeated_offset_packet repeated_upper_key

theorem triple_key_nineteen : (5, 7, 11) ∈ sqrtRoughTripleProductsInShell 19 := by
  simp only [sqrtRoughTripleProductsInShell, Finset.mem_filter, mem_roughTriples,
    roughActiveLabels, oddActive_eq_filter_range]
  decide +kernel

theorem triple_seat_nineteen : 24 ∈ roughTripleSeats 19 ∧ paritySafeActiveSupport 19 24 = {5, 7, 11} :=
  sqrt_triple_offset_packet triple_key_nineteen

theorem zero_anchor_census :
    (sqrtRoughCubeKeys 0).card = 0 ∧ (sqrtRoughCrossKeys 0).card = 0 ∧
    (sqrtRoughRepeatedKeys 0).card = 0 ∧ (sqrtRoughTripleProductsInShell 0).card = 0 := by
  simp only [sqrtRoughCubeKeys, sqrtRoughCrossKeys, sqrtRoughRepeatedKeys,
    sqrtRoughTripleProductsInShell, roughPairs, roughTriples, roughActiveLabels,
    oddActive_eq_filter_range, Internal.upperPairs, DkMath.NumberTheory.upperTriples]
  decide +kernel

end DkMathTest.LegendreSqrtRoughCensusRegression
