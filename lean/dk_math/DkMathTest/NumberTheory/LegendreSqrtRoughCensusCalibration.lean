/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMathTest.NumberTheory.LegendreSqrtRoughCensusCounts
import DkMath.NumberTheory.Legendre.ParitySafeSqrtRoughCensus

#print "file: DkMathTest.NumberTheory.LegendreSqrtRoughCensusCalibration"

namespace DkMathTest.LegendreSqrtRoughCensus
open DkMath.NumberTheory.Legendre DkMathTest.LegendreSqrtRoughMomentCalibration
open DkMathTest.LegendreBlockLocalization
open scoped BigOperators
set_option synthInstance.maxSize 1024
-- Rewriting the explicit 2042-offset finite carrier exceeds the default recursion budget.
set_option maxRecDepth 100000

/-- Prove the inventory adapter symbolically, before specializing to large closed intervals. -/
theorem rough_inventory_normal_form {n : ℕ} {A S : Finset ℕ}
    (hA : squareAnchorOddActivePrimes n = A)
    (hsmall : A.filter (fun p => p ≤ Nat.sqrt n) = S) :
    canonicalRoughCandidates n (Nat.sqrt n) =
      (((Finset.Icc 1 (2 * n)).filter (fun r => Nat.Coprime n r ∧ (n ^ 2 + r) % 2 = 1)).filter
        (fun r => ∀ a ∈ S, ¬a ∣ n ^ 2 + r)) := by
  classical
  ext r
  simp only [canonicalRoughCandidates, candidate_eq_filter_Icc, Finset.mem_filter]
  rw [← hsmall]
  simp only [Finset.mem_filter]
  rw [hA]
  tauto

theorem support_inventory_normal_form {n : ℕ} {A : Finset ℕ}
    (hA : squareAnchorOddActivePrimes n = A) (r : ℕ) :
    paritySafeActiveSupport n r = A.filter (fun p => p ∣ n ^ 2 + r) := by
  ext p
  simp only [mem_paritySafeActiveSupport_iff_dvd, Finset.mem_filter, hA]

theorem inputs1021 :
    (canonicalRoughCandidates 1021 (Nat.sqrt 1021)).card = 311 ∧
    (∑ q ∈ squareAnchorOddActivePrimes 1021, (canonicalRoughWave 1021 (Nat.sqrt 1021) q).card) = 201 ∧
    roughPairMoment 1021 (Nat.sqrt 1021) = 58 ∧ roughTripleMoment 1021 (Nat.sqrt 1021) = 19 := by
  have hA := active1021_checked.1
  have hrEq : canonicalRoughCandidates 1021 (Nat.sqrt 1021) = rough1021 :=
    rough_inventory_normal_form hA active1021_checked.2
  have hsupport (r : ℕ) : paritySafeActiveSupport 1021 r = support1021 r :=
    support_inventory_normal_form hA r
  rw [roughWave_sum_eq_support_sum]
  unfold roughPairMoment roughTripleMoment
  rw [hrEq]
  simp_rw [hsupport]
  exact rough1021_inputs_checked

/-- Prior five kernel-checked moment rows are reused; the sixth has its own finite check. -/
theorem census_moment_inputs : ∀ t ∈ censusData,
    (canonicalRoughCandidates t.n (Nat.sqrt t.n)).card = t.R ∧
    (∑ q ∈ squareAnchorOddActivePrimes t.n, (canonicalRoughWave t.n (Nat.sqrt t.n) q).card) =
      t.N1 + 2 * t.N2 + 3 * t.N3 ∧
    roughPairMoment t.n (Nat.sqrt t.n) = t.N2 + 3 * t.N3 ∧
    roughTripleMoment t.n (Nat.sqrt t.n) = t.N3 := by
  have hnew : ∀ t ∈ censusData, t.n = 1021 → t = ⟨1021, 311, 149, 142, 1, 19, 0, 142, 1, 19⟩ := by decide +kernel
  have hold : ∀ t ∈ censusData, t.n ≠ 1021 → ∃ u ∈ momentData,
      u.1 = t.n ∧ u.2.2.1 = t.R ∧ u.2.2.2.1 = t.N1 + 2 * t.N2 + 3 * t.N3 ∧
      u.2.2.2.2.1 = t.N2 + 3 * t.N3 ∧ u.2.2.2.2.2.1 = t.N3 := by decide +kernel
  intro t ht
  by_cases he : t.n = 1021
  · have := hnew t ht he
    subst t
    exact inputs1021
  · obtain ⟨u, hu, hn, hR, hI, h2, h3⟩ := hold t ht he
    have h := moment_inputs_checked u hu
    rw [hn, hR, hI, h2, h3] at h
    exact h

theorem census_cube_inputs : ∀ t ∈ censusData, (sqrtRoughCubeKeys t.n).card = t.cube := by
  intro t ht
  have hA := (census_inventory_checked t ht).2.2
  unfold sqrtRoughCubeKeys roughActiveLabels
  rw [hA]
  exact cube_inputs_checked t ht

theorem selected_cross_fibers_checked : (sqrtRoughCrossFiber 211 41).card = 3 ∧
    (sqrtRoughCrossFiber 1019 37).card = 7 ∧ (sqrtRoughCrossFiber 1021 41).card = 7 := by
  unfold sqrtRoughCrossFiber
  simp_rw [← trialPrime_iff]
  exact selected_fibers_checked

/-- All four stratum counts and all four product-key counts refer to the production carriers. -/
theorem full_census_checked : ∀ t ∈ censusData,
    (canonicalRoughCandidates t.n (Nat.sqrt t.n)).card = t.R ∧
    (paritySafeUncoveredCandidates t.n).card = t.U ∧
    (roughZeroSeats t.n).card = t.U ∧
    (roughSingletonSeats t.n).card = t.N1 ∧
    (roughDoubleSeats t.n).card = t.N2 ∧
    (roughTripleSeats t.n).card = t.N3 ∧
    (sqrtRoughCubeKeys t.n).card = t.cube ∧
    (sqrtRoughCrossKeys t.n).card = t.cross ∧
    (sqrtRoughRepeatedKeys t.n).card = t.repeated ∧
    (sqrtRoughTripleProductsInShell t.n).card = t.triple := by
  intro t ht
  obtain ⟨hR, hI, hM2, hM3⟩ := census_moment_inputs t ht
  have hC := census_cube_inputs t ht
  have h3 : (roughTripleSeats t.n).card = t.N3 := by
    rwa [rough_tripleMoment_eq_strata] at hM3
  have h2 : (roughDoubleSeats t.n).card = t.N2 := by
    rw [rough_pairMoment_eq_strata, h3] at hM2
    omega
  have h1 : (roughSingletonSeats t.n).card = t.N1 := by
    rw [rough_incidence_eq_strata, h2, h3] at hI
    omega
  obtain ⟨hN1, hN2, hN3, hrow, _⟩ := census_row_arithmetic_checked t ht
  have hX : (sqrtRoughCrossKeys t.n).card = t.cross := by
    have h := rough_singleton_card_eq_cube_cross t.n
    rw [h1, hC] at h
    omega
  have hD : (sqrtRoughRepeatedKeys t.n).card = t.repeated := by
    rwa [rough_double_card_eq_repeated, hN2] at h2
  have hT : (sqrtRoughTripleProductsInShell t.n).card = t.triple := by
    rwa [rough_triple_card_eq_products, hN3] at h3
  have hU : (paritySafeUncoveredCandidates t.n).card = t.U := by
    have h := sqrt_rough_factorization_census t.n
    rw [hR, hC, hX, hD, hT] at h
    omega
  exact ⟨hR, hU, by rw [roughZeroSeats_eq_uncovered, hU], h1,
    by rw [rough_double_card_eq_repeated, hD, ← hN2],
    by rw [rough_triple_card_eq_products, hT, ← hN3], hC, hX, hD, hT⟩

/-- Six numerical fiber sums are kernel consequences of the proved regrouping and recovered Cross counts. -/
theorem census_cross_fiber_sum_checked : ∀ t ∈ censusData,
    (∑ p ∈ roughActiveLabels t.n (Nat.sqrt t.n), (sqrtRoughCrossFiber t.n p).card) = t.cross := by
  intro t ht
  obtain ⟨_, _, _, _, _, _, _, hX, _, _⟩ := full_census_checked t ht
  rwa [← sqrt_cross_count_eq_fiber_sum]

/-- Endpoints consume the product census; whole E and whole I are never evaluated. -/
theorem census_endpoints : ∀ t ∈ censusData, ∃ p, p.Prime ∧ SquareCell t.n p := by
  intro t ht
  obtain ⟨hR, _, _, _, _, _, hC, hX, hD, hT⟩ := full_census_checked t ht
  apply prime_squareCell_of_sqrt_factorization_census (census_inventory_checked t ht).2.1
  rw [hR, hC, hX, hD, hT]
  exact (census_row_arithmetic_checked t ht).2.2.2.2

theorem shell1021_prime_from_census : ∃ p, p.Prime ∧ SquareCell 1021 p :=
  census_endpoints ⟨1021, 311, 149, 142, 1, 19, 0, 142, 1, 19⟩ (by decide)

end DkMathTest.LegendreSqrtRoughCensus
