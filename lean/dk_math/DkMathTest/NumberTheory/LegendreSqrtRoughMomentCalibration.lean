/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMathTest.NumberTheory.LegendreSqrtRoughMomentCounts
import DkMath.NumberTheory.Legendre.ParitySafeSqrtRoughFactorization

#print "file: DkMathTest.NumberTheory.LegendreSqrtRoughMomentCalibration"

namespace DkMathTest.LegendreSqrtRoughMomentCalibration
-- Seven-field row membership needs a larger typeclass expression budget.
set_option synthInstance.maxSize 1024
open DkMath.NumberTheory.Legendre DkMathTest.LegendreBlockLocalization
open scoped BigOperators

theorem calibrationRough_eq {t : MomentRow} (ht : t ∈ momentData) :
    canonicalRoughCandidates t.1 (Nat.sqrt t.1) = calibrationRough t.1 := by
  obtain ⟨_, _, hA, hsmall⟩ := inventories_checked t ht
  classical
  ext r
  simp only [canonicalRoughCandidates, candidate_eq_filter_Icc, calibrationRough, Finset.mem_filter]
  rw [← hsmall]
  simp only [Finset.mem_filter]
  rw [hA]
  tauto

theorem calibrationSupport_eq {t : MomentRow} (ht : t ∈ momentData) (r : ℕ) :
    paritySafeActiveSupport t.1 r = calibrationSupport t.1 r := by
  have hA := (inventories_checked t ht).2.2.1
  ext q
  simp only [mem_paritySafeActiveSupport_iff_dvd, calibrationSupport, Finset.mem_filter, hA]

/-- Actual rough wave currency and moments, identified with kernel-checked finite normal forms. -/
theorem moment_inputs_checked : ∀ t ∈ momentData,
    (canonicalRoughCandidates t.1 (Nat.sqrt t.1)).card = t.2.2.1 ∧
    (∑ q ∈ squareAnchorOddActivePrimes t.1, (canonicalRoughWave t.1 (Nat.sqrt t.1) q).card) =
      t.2.2.2.1 ∧
    roughPairMoment t.1 (Nat.sqrt t.1) = t.2.2.2.2.1 ∧
    roughTripleMoment t.1 (Nat.sqrt t.1) = t.2.2.2.2.2.1 := by
  intro t ht
  rw [roughWave_sum_eq_support_sum]
  unfold roughPairMoment roughTripleMoment
  rw [calibrationRough_eq ht]
  simp_rw [calibrationSupport_eq ht]
  exact finite_moments_checked t ht

/-- U is recovered through the proved conservation law, with no direct uncovered enumeration. -/
theorem recovered_uncovered_checked : ∀ t ∈ momentData,
    (paritySafeUncoveredCandidates t.1).card = t.2.2.2.2.2.2 := by
  intro t ht
  obtain ⟨hR, hI, h2, h3⟩ := moment_inputs_checked t ht
  have hb := sqrt_rough_moment_balance t.1
  rw [hR, hI, h2, h3] at hb
  have hm := (row_margins_checked t ht).2.2
  omega

/-- Required product-wave regrouping checkpoints are instances of generic kernel proofs. -/
theorem product_regrouping_checked : ∀ t ∈ momentData,
    roughPairMoment t.1 (Nat.sqrt t.1) =
      ∑ a ∈ roughPairs t.1 (Nat.sqrt t.1), (roughPairWave t.1 (Nat.sqrt t.1) a.1 a.2).card ∧
    roughTripleMoment t.1 (Nat.sqrt t.1) =
      ∑ a ∈ roughTriples t.1 (Nat.sqrt t.1),
        (roughTripleWave t.1 (Nat.sqrt t.1) a.1 a.2.1 a.2.2).card := by
  intro t _
  exact ⟨roughPairMoment_eq_wave_sum _ _, sqrt_roughTripleMoment_eq_wave_sum _⟩

theorem checkpoints_prime_from_moments : ∀ t ∈ momentData,
    ∃ p, p.Prime ∧ SquareCell t.1 p := by
  intro t ht
  obtain ⟨hR, hI, h2, h3⟩ := moment_inputs_checked t ht
  obtain ⟨hpos, hmargin, _⟩ := row_margins_checked t ht
  apply prime_squareCell_of_sqrt_product_moment hpos
  rw [← roughPairMoment_eq_wave_sum, ← sqrt_roughTripleMoment_eq_wave_sum]
  rw [hR, hI, h2, h3]
  exact hmargin

theorem shell1019_prime : ∃ p, p.Prime ∧ SquareCell 1019 p :=
  checkpoints_prime_from_moments (1019, 31, 312, 196, 28, 9, 135) (by decide)

end DkMathTest.LegendreSqrtRoughMomentCalibration
