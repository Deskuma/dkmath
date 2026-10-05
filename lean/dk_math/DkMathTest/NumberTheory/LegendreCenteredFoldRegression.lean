/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.CenteredFoldSupportNorm
import DkMath.CosmicFormula.QuadraticCenteredBridge
import DkMathTest.NumberTheory.LegendreResidueCoverCalibration

#print "file: DkMathTest.NumberTheory.LegendreCenteredFoldRegression"

namespace DkMathTest.LegendreCenteredFoldRegression
open DkMath.NumberTheory.Legendre DkMath.NumberTheory.Primitive

/-- Unit forward and second differences reuse the old gnomon API. -/
theorem unit_and_second_difference (n : ℕ) :
    (n + 1) ^ 2 - n ^ 2 = 2 * n + 1 ∧
    (n + 2) ^ 2 + n ^ 2 = 2 * (n + 1) ^ 2 + 2 ∧
    DkMath.Gnomon.oddGnomon (n + 1) = DkMath.Gnomon.oddGnomon n + 2 := by
  refine ⟨?_, by ring, DkMath.Gnomon.oddGnomon_succ n⟩
  have h := DkMath.Gnomon.square_add_oddGnomon n
  unfold DkMath.Gnomon.oddGnomon at h
  omega

theorem rational_steps (x : ℚ) :
    ((x + 1) ^ 2 - x ^ 2) / 1 = 2 * x + 1 ∧
    ((x + 1 / 2) ^ 2 - x ^ 2) / (1 / 2) = 2 * x + 1 / 2 ∧
    ((x + 1 / 4) ^ 2 - x ^ 2) / (1 / 4) = 2 * x + 1 / 4 ∧
    ((x + 1 / 8) ^ 2 - x ^ 2) / (1 / 8) = 2 * x + 1 / 8 := by
  exact ⟨DkMath.CosmicFormula.quadratic_forward_div x 1 (by norm_num),
    DkMath.CosmicFormula.quadratic_forward_div x (1 / 2) (by norm_num),
    DkMath.CosmicFormula.quadratic_forward_div x (1 / 4) (by norm_num),
    DkMath.CosmicFormula.quadratic_forward_div x (1 / 8) (by norm_num)⟩

theorem doubled_and_zero_boundary :
    (2 * (5 : ℕ) + 1) ^ 2 - (2 * 5 - 1) ^ 2 = 8 * 5 ∧
    (2 * (0 : ℤ) + 1) ^ 2 - (2 * 0 - 1) ^ 2 = 8 * 0 ∧
    (2 * (0 : ℕ) + 1) ^ 2 - (2 * 0 - 1) ^ 2 ≠ 8 * 0 := by
  exact ⟨centered_doubled_square_difference_nat (by decide),
    centered_doubled_square_difference 0, by decide⟩

theorem fold_and_gap {n r j : ℕ} (hr : SquareOffset n r) (hj : j < n) :
    squareOffsetFold n (squareOffsetFold n r) = r ∧
    squareOffsetFold n (centeredLeftOffset n j) = centeredRightOffset n j ∧
    centeredRightOffset n j - centeredLeftOffset n j = 2 * j + 1 :=
  ⟨squareOffsetFold_involutive hr, squareOffsetFold_centeredLeft hj,
    centered_offset_difference hj⟩

theorem three_pairs_and_gaps :
    squareOffsetFoldPairs 3 = {{3, 4}, {2, 5}, {1, 6}} ∧
    centeredInternalGaps 3 = {1, 3, 5} := by
  unfold squareOffsetFoldPairs centeredFoldPair centeredLeftOffset centeredRightOffset
    centeredInternalGaps DkMath.Gnomon.oddGnomon
  decide +kernel

/-- Translation preserves shell membership, but does not preserve divisibility. -/
theorem translation_divisibility_counterexample :
    (7 : ℕ) ∈ Finset.Icc (3 ^ 2 - 3 + 1) (3 ^ 2 + 3) ∧
    SquareCell 3 (7 + 3) ∧ ¬(2 : ℕ) ∣ 7 ∧ (2 : ℕ) ∣ 7 + 3 := by
  norm_num [SquareCell]

/-- Smallest shared old support in the bounded scan: owners differ, support 5 persists. -/
theorem six_shared_support :
    5 ∈ squareOffsetPrimeSupport 6 (centeredLeftOffset 6 2) ∧
    5 ∈ squareOffsetPrimeSupport 6 (centeredRightOffset 6 2) ∧
    squareResidueCoverOwner 6 (centeredLeftOffset 6 2) = 2 ∧
    squareResidueCoverOwner 6 (centeredRightOffset 6 2) = 3 := by
  rw [mem_squareOffsetPrimeSupport, mem_squareOffsetPrimeSupport]
  norm_num [centeredLeftOffset, centeredRightOffset, squareResidueCoverOwner]

theorem distinct_owner_does_not_imply_disjoint :
    squareResidueCoverOwner 6 (centeredLeftOffset 6 2) ≠
      squareResidueCoverOwner 6 (centeredRightOffset 6 2) ∧
    ¬Disjoint (squareOffsetPrimeSupport 6 (centeredLeftOffset 6 2))
      (squareOffsetPrimeSupport 6 (centeredRightOffset 6 2)) := by
  refine ⟨centeredPair_owner_ne (by decide), ?_⟩
  rw [Finset.disjoint_left]
  intro h
  exact h six_shared_support.1 six_shared_support.2.1

/-- Smallest scanned reverse implication failure: 5 divides gap 15, owners 5 and 2. -/
theorem eight_reverse_owner_counterexample :
    squareResidueCoverOwner 8 (centeredLeftOffset 8 7) = 5 ∧
    squareResidueCoverOwner 8 (centeredLeftOffset 8 7) ∣ 2 * 7 + 1 ∧
    squareResidueCoverOwner 8 (centeredRightOffset 8 7) = 2 := by
  norm_num [squareResidueCoverOwner, centeredLeftOffset, centeredRightOffset]

theorem prime_gap_forces_disjoint :
    Disjoint (squareOffsetPrimeSupport 3 (centeredLeftOffset 3 2))
      (squareOffsetPrimeSupport 3 (centeredRightOffset 3 2)) ∧
    squareResidueCoverOwner 3 (centeredLeftOffset 3 2) ≠
      squareResidueCoverOwner 3 (centeredRightOffset 3 2) :=
  centered_prime_gap_support_packet (by decide) (by decide) (by decide)

/-- Exact norm-activated address fiber, unlike the empty same-owner fiber. -/
theorem six_capacity_and_actual :
    centeredCommonSupportIndices 6 5 = {2} ∧
    (centeredOwnerGapCapacityIndices 6 5).card = 1 ∧
    centeredSameOwnerIndices 6 5 = ∅ := by
  classical
  refine ⟨?_, ?_, centeredSameOwnerIndices_empty 6 5⟩
  · rw [centeredCommonSupportIndices_eq_capacity (by decide : Nat.Prime 5),
      ite_eq_left (by norm_num [centeredFoldNorm]),
      centeredOwnerGapCapacityIndices_eq_residue (by decide) (by decide)]
    decide +kernel
  · rw [centeredOwnerGapCapacityIndices_card (by decide) (by decide)]

theorem fold_insert_smallest_mismatch :
    squareOffsetFold 2 (successorThresholdInsert 1 1) = 4 ∧
    successorThresholdInsert 1 (squareOffsetFold 1 1) = 3 ∧
    Disjoint (squareOffsetPrimeSupport 2 4) (squareOffsetPrimeSupport 2 3) := by
  refine ⟨by decide, by decide, ?_⟩
  exact fold_successor_support_disjoint (n := 1) (r := 1) (by norm_num [SquareOffset])

theorem norm_successor_packet : centeredFoldNorm 6 = 85 ∧ centeredFoldNorm 7 = 113 ∧
    Nat.Coprime (centeredFoldNorm 6) (centeredFoldNorm 7) ∧
    ¬(5 ∈ squareOffsetPrimeSupport 7 (centeredLeftOffset 7 2) ∧
      5 ∈ squareOffsetPrimeSupport 7 (centeredRightOffset 7 2)) := by
  exact ⟨by decide, by decide, centeredFoldNorm_succ_coprime 6,
    common_centered_support_no_successor (by decide) (by decide)
      ⟨six_shared_support.1, six_shared_support.2.1⟩⟩

/-- The old near miss is retained, and no same-owner example can exist. -/
theorem near_miss_five : (paritySafeUncoveredCandidates 5).card = 2 ∧
    centeredSameOwnerIndices 5 2 = ∅ ∧ (squareOffsetFoldPairs 5).card = 5 :=
  ⟨DkMathTest.LegendreResidueCoverCalibration.near_miss_five_uncovered,
    centeredSameOwnerIndices_empty 5 2, squareOffsetFoldPairs_card 5⟩

/-- At 297 the prime norm lies above the old-prime basis, so every common fiber is empty. -/
theorem near_miss_297_common_empty {p : ℕ} (hp : p.Prime) :
    centeredCommonSupportIndices 297 p = ∅ := by
  have hn : (centeredFoldNorm 297).Prime := by norm_num [centeredFoldNorm]
  rw [centeredCommonSupportIndices_eq_capacity hp]
  split_ifs with h
  · have he := (Nat.prime_dvd_prime_iff_eq hp hn).mp h.2
    have hpn := h.1
    norm_num [centeredFoldNorm] at he
    omega
  · rfl

/-- Two exact large-anchor support counts use the symbolic floor theorem. -/
theorem norm1031_support_counts : centeredFoldNorm 1031 = 2127985 ∧
    (centeredCommonSupportIndices 1031 5).card = 206 ∧
    (centeredCommonSupportIndices 1031 61).card = 17 := by
  refine ⟨by decide, ?_, ?_⟩
  · rw [centeredCommonSupportIndices_card (by decide : Nat.Prime 5) (by decide),
      ite_eq_left (by norm_num [centeredFoldNorm])]
  · rw [centeredCommonSupportIndices_card (by decide : Nat.Prime 61) (by decide),
      ite_eq_left (by norm_num [centeredFoldNorm])]

/-- Reuse the earlier kernel endpoint rather than recalculate a full 1031 census. -/
theorem preserved1031 : ¬SquareOffsetsFullyCovered 1031 ∧
    18 ≤ (squareShellWheelSurvivorImage 1031).card ∧
    ∃ p, p.Prime ∧ SquareCell 1031 p :=
  ⟨DkMathTest.LegendreResidueCoverCalibration.residue1031_not_full,
    DkMathTest.LegendreResidueCoverCalibration.residue1031_projected_survivor_lower,
    DkMathTest.LegendreResidueCoverCalibration.residue1031_preserved_endpoint⟩

/-- A covered local trajectory satisfies all fold and successor restrictions together. -/
theorem compatible_covered_trajectory :
    squareResidueCoverOwner 13 6 = 5 ∧ squareResidueCoverOwner 13 21 = 2 ∧
    squareResidueCoverOwner 14 6 = 2 ∧ squareResidueCoverOwner 14 23 = 3 ∧
    squareResidueCoverOwner 14 22 = 2 ∧
    SquareOffsetCovered 13 6 ∧ SquareOffsetCovered 13 21 ∧
    SquareOffsetCovered 14 6 ∧ SquareOffsetCovered 14 23 ∧ SquareOffsetCovered 14 22 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [squareResidueCoverOwner]
  · norm_num [squareResidueCoverOwner]
  · norm_num [squareResidueCoverOwner]
  · norm_num [squareResidueCoverOwner]
  · norm_num [squareResidueCoverOwner]
  · exact ⟨5, mem_primeScalesUpTo.mpr ⟨by decide, by decide⟩,
      by norm_num [SquareOffsetForbiddenBy]⟩
  · exact ⟨2, mem_primeScalesUpTo.mpr ⟨by decide, by decide⟩,
      by norm_num [SquareOffsetForbiddenBy]⟩
  · exact ⟨2, mem_primeScalesUpTo.mpr ⟨by decide, by decide⟩,
      by norm_num [SquareOffsetForbiddenBy]⟩
  · exact ⟨3, mem_primeScalesUpTo.mpr ⟨by decide, by decide⟩,
      by norm_num [SquareOffsetForbiddenBy]⟩
  · exact ⟨2, mem_primeScalesUpTo.mpr ⟨by decide, by decide⟩,
      by norm_num [SquareOffsetForbiddenBy]⟩

end DkMathTest.LegendreCenteredFoldRegression
