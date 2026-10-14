/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.ParitySafeIncidenceUpper
import DkMathTest.NumberTheory.LegendreBlockLocalization

#print "file: DkMathTest.NumberTheory.LegendreIncidenceUpper"

namespace DkMathTest.LegendreIncidenceUpper

open DkMath.NumberTheory.Legendre
open DkMathTest.LegendreBlockLocalization DkMathTest.LegendreFreshCost
open scoped BigOperators

-- Kernel mode unfolds the well-founded, irreducible Nat.primeFactorsList definition.
-- Numerical reduction is checked directly by the Lean kernel.
/-- Numerical normalization of the structural cap, without computing actual active supports. -/
theorem incidenceUpper_eq_finite (n : ℕ) :
    paritySafeIncidenceUpper n =
      ∑ q ∈ (Finset.range (n + 1)).filter (fun q => q.Prime ∧ ¬q ∣ n ∧ q ≠ 2),
        paritySafeWaveUpper n q := by
  rw [paritySafeIncidenceUpper, oddActive_eq_filter_range]

set_option maxRecDepth 20000 in
theorem mainBlock_structural_upper :
    (∑ i ∈ Finset.range 20, paritySafeIncidenceUpper (20 + i + 1)) = 425 := by
  simp_rw [incidenceUpper_eq_finite]
  decide +kernel

set_option maxRecDepth 20000 in
theorem mainBlock_odd_endpoint_upper :
    (∑ i ∈ Finset.range 20, ∑ q ∈ squareAnchorOddActivePrimes (20 + i + 1),
      paritySafeOddQuotientUpper (20 + i + 1) q) = 510 := by
  simp_rw [oddActive_eq_filter_range]
  decide +kernel

set_option maxRecDepth 20000 in
theorem mainBlock_uniform_spacing_upper :
    (∑ i ∈ Finset.range 20, ∑ q ∈ squareAnchorOddActivePrimes (20 + i + 1),
      shellFrequencyCap (2 * q) (2 * (20 + i + 1))) = 602 := by
  simp_rw [oddActive_eq_filter_range]
  decide +kernel

/-- The weakest uniform-spacing proposal cannot reach the checked main-block demand. -/
theorem uniform_spacing_main_threshold_false :
    ¬(∑ i ∈ Finset.range 20, ∑ q ∈ squareAnchorOddActivePrimes (20 + i + 1),
      shellFrequencyCap (2 * q) (2 * (20 + i + 1))) < 490 + 38 := by
  rw [mainBlock_uniform_spacing_upper]
  decide +kernel

/-- Structural recovery uses the cap425, candidate490 and checked temporal38;
it does not use the actual incidence418 theorem. -/
theorem mainBlock_structural_not_fullyCovered :
    ¬ (∀ i ∈ Finset.range 20, SquareOffsetsFullyCovered (20 + i + 1)) := by
  apply not_block_fullyCovered_of_upper_lt_candidate_add_freshBound 20 20
  rw [mainBlock_structural_upper, mainBlock_candidate_sum, mainBlock_required_seats,
    mainBlock_parity_capacity.1, mainBlock_first_slot_capacity]
  decide +kernel

/-- The unconditional deficit uses excess>=0, not the full-cover-only temporal38. -/
theorem mainBlock_uncovered_ge_sixtyFive :
    65 ≤ ∑ i ∈ Finset.range 20, (paritySafeUncoveredCandidates (20 + i + 1)).card := by
  have h := block_uncovered_ge_candidate_add_excess_sub_upper 20 20 0 (by omega)
  simpa only [mainBlock_candidate_sum, mainBlock_structural_upper] using h

/-- The disciplined width sequence is an exact calibration of caps and candidate demand. -/
def widthCalibration : Finset (ℕ × ℕ × ℕ) :=
  {(20, 425, 490), (10, 162, 200), (5, 73, 90), (4, 55, 70),
    (3, 45, 54), (2, 24, 32), (1, 7, 12)}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
-- Finite prime/floor caps and candidate filters are checked at the seven prescribed widths.
theorem width_cap_and_candidate_calibration :
    ∀ t ∈ widthCalibration,
      (∑ i ∈ Finset.range t.1, paritySafeIncidenceUpper (20 + i + 1)) = t.2.1 ∧
      (∑ i ∈ Finset.range t.1, (squareAnchorOddPointCoprimeOffsets (20 + i + 1)).card) = t.2.2 := by
  simp_rw [incidenceUpper_eq_finite, candidate_eq_filter_Icc]
  decide +kernel

theorem widths_uncovered_lower_bound :
    ∀ t ∈ widthCalibration,
      t.2.2 - t.2.1 ≤ ∑ i ∈ Finset.range t.1,
        (paritySafeUncoveredCandidates (20 + i + 1)).card := by
  intro t ht
  obtain ⟨hb, ha⟩ := width_cap_and_candidate_calibration t ht
  have h := block_uncovered_ge_candidate_add_excess_sub_upper 20 t.1 0 (by omega)
  simpa only [hb, ha, Nat.add_zero] using h

/-- Every calibrated width, including1, contains a square-cell prime through the deficit consumer. -/
theorem widths_structural_prime :
    ∀ t ∈ widthCalibration, ∃ i ∈ Finset.range t.1, ∃ p,
      Nat.Prime p ∧ SquareCell (20 + i + 1) p := by
  intro t ht
  obtain ⟨hb, ha⟩ := width_cap_and_candidate_calibration t ht
  apply exists_prime_squareCell_of_block_candidate_add_excess_gt_upper 20 t.1 0 (by omega)
  rw [hb, ha, Nat.add_zero]
  have hall : ∀ u ∈ widthCalibration, u.2.1 < u.2.2 := by decide +kernel
  exact hall t ht

theorem widths_structural_not_fullyCovered :
    ∀ t ∈ widthCalibration,
      ¬ (∀ i ∈ Finset.range t.1, SquareOffsetsFullyCovered (20 + i + 1)) := by
  intro t ht
  obtain ⟨hb, ha⟩ := width_cap_and_candidate_calibration t ht
  apply not_block_fullyCovered_of_upper_lt_candidate_add_freshBound 20 t.1
  rw [hb, ha]
  have hall : ∀ u ∈ widthCalibration, u.2.1 < u.2.2 := by decide +kernel
  have hlt := hall t ht
  omega

theorem shell21_cap_and_candidate :
    paritySafeIncidenceUpper 21 = 7 ∧ (squareAnchorOddPointCoprimeOffsets 21).card = 12 := by
  have h := width_cap_and_candidate_calibration (1, 7, 12) (by decide +kernel)
  simpa using h

theorem shell21_uncovered_ge_five :
    5 ≤ (paritySafeUncoveredCandidates 21).card := by
  have h := paritySafeUncovered_card_ge_candidate_add_excess_sub_upper 21 0 (by omega)
  simpa only [shell21_cap_and_candidate.1, shell21_cap_and_candidate.2] using h

theorem shell21_not_fullyCovered : ¬SquareOffsetsFullyCovered 21 := by
  intro hfull
  have he := paritySafeUncoveredCandidates_eq_empty_of_fullyCovered (by decide +kernel) hfull
  have h := shell21_uncovered_ge_five
  rw [he, Finset.card_empty] at h
  omega

theorem shell21_structural_prime :
    ∃ p, Nat.Prime p ∧ 21 ^ 2 < p ∧ p < 22 ^ 2 := by
  apply exists_prime_squareCell_of_candidate_add_excess_gt_upper (e := 0) (by decide +kernel) (by omega)
  rw [shell21_cap_and_candidate.1, shell21_cap_and_candidate.2]
  decide +kernel

/-- A width1 example is not a uniform bound: shell29's cap exceeds its candidates. -/
theorem shell29_zero_excess_threshold_fails :
    paritySafeIncidenceUpper 29 = 31 ∧ (squareAnchorOddPointCoprimeOffsets 29).card = 28 ∧
      ¬paritySafeIncidenceUpper 29 < (squareAnchorOddPointCoprimeOffsets 29).card := by
  simp_rw [incidenceUpper_eq_finite, candidate_eq_filter_Icc]
  decide +kernel

/-- Finite arithmetic normalization of an actual wave, only for diagnostic examples. -/
theorem activeWave_eq_finite (n q : ℕ) :
    paritySafeActiveWaveOffsets n q =
      ((Finset.Icc 1 (2 * n)).filter (fun r => Nat.Coprime n r ∧ (n ^ 2 + r) % 2 = 1)).filter
        (fun r => q ∣ n ^ 2 + r) := by
  ext r
  simp only [mem_paritySafeActiveWaveOffsets_iff_dvd, candidate_eq_filter_Icc, Finset.mem_filter]

/-- 2q divisibility does not imply adjacency: the first small skipped-step example. -/
theorem sameWave_exact_adjacency_false :
    paritySafeActiveWaveOffsets 18 5 = {1, 11, 31} ∧ (31 : ℕ) - 11 ≠ 2 * 5 := by
  rw [activeWave_eq_finite]
  decide +kernel

/-- The false exact-single-divisor formula leaves actual residual anchor exclusions. -/
theorem single_divisor_upper_not_exact :
    paritySafeWaveUpper 21 5 = 3 ∧ (paritySafeActiveWaveOffsets 21 5).card = 2 := by
  rw [activeWave_eq_finite]
  decide +kernel

/-- Exact incidence is consulted only after the structural proof, to measure its slack. -/
theorem mainBlock_upper_slack_diagnostic :
    (∑ i ∈ Finset.range 20, paritySafeIncidenceUpper (20 + i + 1)) -
      (∑ i ∈ Finset.range 20, paritySafeIncidenceCount (20 + i + 1)) = 7 := by
  rw [mainBlock_structural_upper, mainBlock_incidence_sum]

def residualWaveCalibration : Finset (ℕ × ℕ × ℕ × ℕ) :=
  {(21, 5, 3, 2), (30, 11, 2, 1), (35, 3, 10, 8),
    (39, 7, 3, 2), (39, 11, 3, 2), (39, 17, 1, 0)}

set_option maxRecDepth 20000 in
theorem residual_wave_slack_calibration :
    ∀ t ∈ residualWaveCalibration,
      paritySafeWaveUpper t.1 t.2.1 = t.2.2.1 ∧
      (paritySafeActiveWaveOffsets t.1 t.2.1).card = t.2.2.2 := by
  simp_rw [activeWave_eq_finite]
  decide +kernel

set_option maxRecDepth 20000 in
/-- Low primes dominate capacity, whereas the residual overcount is only seven. -/
theorem mainBlock_low_prime_upper_diagnostic :
    (∑ i ∈ Finset.range 20, ∑ q ∈ (squareAnchorOddActivePrimes (20 + i + 1)).filter
      (fun q => q ≤ 7), paritySafeWaveUpper (20 + i + 1) q) = 261 := by
  simp_rw [oddActive_eq_filter_range]
  decide +kernel

theorem shell21_seat_upper_diagnostic :
    (∑ r ∈ squareAnchorOddPointCoprimeOffsets 21, (21 ^ 2 + r).primeFactors.card) = 17 := by
  rw [candidate_eq_filter_Icc]
  decide +kernel

/-- The mature odd endpoint bound already succeeds here; exclusion improves its deficit. -/
theorem shell21_odd_endpoint_upper_diagnostic :
    (∑ q ∈ squareAnchorOddActivePrimes 21, paritySafeOddQuotientUpper 21 q) = 10 := by
  rw [oddActive_eq_filter_range]
  decide +kernel

end DkMathTest.LegendreIncidenceUpper
