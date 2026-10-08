/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.ParitySafeSqrtQuotientConservation
import DkMathTest.NumberTheory.LegendreSqrtRoughCensusCalibration

#print "file: DkMathTest.NumberTheory.LegendreSqrtQuotientCalibration"

namespace DkMathTest.LegendreSqrtQuotientCalibration
open DkMath.NumberTheory.Legendre DkMathTest.LegendreSqrtRoughCensus
open DkMathTest.LegendreSqrtRoughMomentCalibration
open scoped BigOperators
set_option maxRecDepth 100000
set_option synthInstance.maxSize 1024

/-- Total reduced quotients, exact rejection, and the three-small-prime rejection lower bound. -/
def quotientNumbers (n : ℕ) : ℕ × ℕ × ℕ :=
  if n = 211 then (129, 80, 71) else if n = 503 then (331, 226, 191) else
  if n = 1009 then (627, 439, 334) else if n = 1013 then (642, 461, 352) else
  if n = 1019 then (653, 457, 358) else (647, 446, 352)

/-- A computational copy only of the finite reduced quotient interval and three divisor tests. -/
def rejectedThreeCalc (n p : ℕ) : Finset ℕ :=
  ((Finset.Ioc (n ^ 2 / p) ((n ^ 2 + 2 * n) / p)).filter
    (fun q => Nat.Coprime (2 * n) q)).filter (fun q => 3 ∣ q ∨ 5 ∣ q ∨ 7 ∣ q)

theorem rejectedThree_normal_form (n p : ℕ) : rejectedThreeCalc n p =
    (sqrtRoughQuotientFiber n p).filter (fun q => ∃ u ∈ ({3, 5, 7} : Finset ℕ), u ∣ q) := by
  classical
  ext q
  simp only [rejectedThreeCalc, sqrtRoughQuotientFiber, paritySafeReducedQuotientInterval,
    Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton,
    or_and_right, exists_or, exists_eq_left]

/-- The lower bound uses divisibility only, with no external primality evaluation. -/
theorem rejectedThree_card_le {n p : ℕ}
    (hp : p ∈ roughActiveLabels n (Nat.sqrt n)) (hcut : 7 ≤ Nat.sqrt n) :
    (rejectedThreeCalc n p).card ≤ (sqrtRoughRejectedFiber n p).card := by
  rw [rejectedThree_normal_form]
  apply sqrt_rejected_card_lower_of_small_primes hp
  intro u hu
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu
  rcases hu with rfl | rfl | rfl <;> constructor <;> norm_num <;> omega

set_option maxHeartbeats 20000000 in
-- Kernel reduction of the finite quotient and rough-seat carriers needs a larger expression budget.
theorem quotient_floor_inputs_checked : ∀ t ∈ censusData,
    (∑ p ∈ (censusActive t.n).filter (fun p => Nat.sqrt t.n < p),
      primeAnchorProductWaveCount t.n p) = (quotientNumbers t.n).1 ∧
    (∑ p ∈ (censusActive t.n).filter (fun p => Nat.sqrt t.n < p),
      (rejectedThreeCalc t.n p).card) = (quotientNumbers t.n).2.2 := by
  decide +kernel

theorem quotient_row_arithmetic : ∀ t ∈ censusData,
    7 ≤ Nat.sqrt t.n ∧
    (quotientNumbers t.n).1 = t.N1 + 2 * t.N2 + 3 * t.N3 + (quotientNumbers t.n).2.1 ∧
    (quotientNumbers t.n).1 < t.R + (quotientNumbers t.n).2.2 := by
  decide +kernel

theorem quotient_total_checked : ∀ t ∈ censusData,
    (∑ p ∈ roughActiveLabels t.n (Nat.sqrt t.n), (sqrtRoughQuotientFiber t.n p).card) =
      (quotientNumbers t.n).1 := by
  intro t ht
  have hA := census_inventory_checked t ht
  rw [primeAnchor_quotient_range_eq_floor hA.1 (by
    have hn : ∀ t ∈ censusData, t.n ≠ 2 := by decide +kernel
    exact hn t ht) _ (fun _ hp => hp)]
  unfold roughActiveLabels
  rw [hA.2.2]
  exact (quotient_floor_inputs_checked t ht).1

theorem quotient_rejected_lower_checked : ∀ t ∈ censusData,
    (quotientNumbers t.n).2.2 ≤
      ∑ p ∈ roughActiveLabels t.n (Nat.sqrt t.n), (sqrtRoughRejectedFiber t.n p).card := by
  intro t ht
  have hsum := Finset.sum_le_sum (fun p (hp : p ∈ roughActiveLabels t.n (Nat.sqrt t.n)) =>
    rejectedThree_card_le hp (quotient_row_arithmetic t ht).1)
  have hA := (census_inventory_checked t ht).2.2
  have he : (∑ p ∈ roughActiveLabels t.n (Nat.sqrt t.n), (rejectedThreeCalc t.n p).card) =
      (quotientNumbers t.n).2.2 := by
    unfold roughActiveLabels
    rw [hA]
    exact (quotient_floor_inputs_checked t ht).2
  rwa [he] at hsum

/-- All six rows concern the production quotient, routed, rejected, and composite carriers. -/
theorem quotient_full_calibration : ∀ t ∈ censusData,
    (∑ p ∈ roughActiveLabels t.n (Nat.sqrt t.n), (sqrtRoughQuotientFiber t.n p).card) =
      (quotientNumbers t.n).1 ∧
    (∑ p ∈ roughActiveLabels t.n (Nat.sqrt t.n), (sqrtRoughRoutedFiber t.n p).card) =
      t.N1 + 2 * t.N2 + 3 * t.N3 ∧
    (∑ p ∈ roughActiveLabels t.n (Nat.sqrt t.n), (sqrtRoughRejectedFiber t.n p).card) =
      (quotientNumbers t.n).2.1 ∧
    (∑ p ∈ roughActiveLabels t.n (Nat.sqrt t.n), (sqrtRoughCompositeFiber t.n p).card) +
      t.cross = (quotientNumbers t.n).1 ∧
    t.cross + t.cube + 2 * t.repeated + 3 * t.triple + (quotientNumbers t.n).2.1 =
      (quotientNumbers t.n).1 := by
  intro t ht
  have htotal := quotient_total_checked t ht
  have hrough := (census_moment_inputs t ht).2.1
  have hrow := quotient_row_arithmetic t ht
  have hc := full_census_checked t ht
  have harith := census_row_arithmetic_checked t ht
  have hcon := sqrt_quotient_conservation t.n
  rw [htotal, hc.2.2.2.2.2.2.2.1, hc.2.2.2.2.2.2.1,
    hc.2.2.2.2.2.2.2.2.1, hc.2.2.2.2.2.2.2.2.2] at hcon
  have hroute := sqrt_routed_quotient_sum_eq_rough_incidence t.n
  rw [hrough] at hroute
  have hcomp := sqrt_cross_add_composite_eq_total t.n
  rw [htotal, hc.2.2.2.2.2.2.2.1] at hcomp
  exact ⟨htotal, hroute, by omega, by omega, by omega⟩

/-- These endpoints use floor capacity and a three-prime rejection lower bound, rather than Cross counts. -/
theorem quotient_structural_calibration_endpoints : ∀ t ∈ censusData,
    ∃ p, p.Prime ∧ SquareCell t.n p := by
  intro t ht
  apply prime_squareCell_of_quotient_routing_budget (census_inventory_checked t ht).2.1
    (quotient_rejected_lower_checked t ht)
  have hR := (census_moment_inputs t ht).1
  rw [quotient_total_checked t ht, hR]
  have := (quotient_row_arithmetic t ht).2.2
  omega

def active1031 : Finset ℕ := insert 1021 active1021

theorem active1031_checked : squareAnchorOddActivePrimes 1031 = active1031 ∧
    active1031.filter (fun p => p ≤ Nat.sqrt 1031) = calibrationSmall 1019 := by
  have h21 : Nat.Prime 1021 := by norm_num
  have h31 : Nat.Prime 1031 := by norm_num
  have hgap : ∀ p ∈ Finset.Icc 1022 1030, ¬p.Prime := by decide +kernel
  constructor
  · rw [active1031, ← active1021_checked.1]
    ext p
    rw [mem_squareAnchorOddActivePrimes, Finset.mem_insert, mem_squareAnchorOddActivePrimes]
    constructor
    · rintro ⟨hp, hle, hnd, hne⟩
      by_cases he : p = 1021
      · exact Or.inl he
      · right
        have hp31 : p ≠ 1031 := by intro he; subst p; exact hnd (dvd_refl _)
        have hbound : p ≤ 1021 := by
          by_contra h
          exact hgap p (Finset.mem_Icc.mpr (by omega)) hp
        exact ⟨hp, hbound, by intro hd; exact he ((Nat.prime_dvd_prime_iff_eq hp h21).mp hd), hne⟩
    · rintro (rfl | ⟨hp, hle, _, hne⟩)
      · exact ⟨h21, by decide, by norm_num, by decide⟩
      · exact ⟨hp, by omega, by intro hd; have := (Nat.prime_dvd_prime_iff_eq hp h31).mp hd; omega, hne⟩
  · decide +kernel

/-- Only rough-seat cardinality is evaluated at the new anchor; no full incidence is evaluated. -/
def rough1031 : Finset ℕ :=
  ((Finset.Icc 1 2062).filter (fun r => Nat.Coprime 1031 r ∧ (1031 ^ 2 + r) % 2 = 1)).filter
    (fun r => ∀ a ∈ calibrationSmall 1019, ¬a ∣ 1031 ^ 2 + r)

set_option maxHeartbeats 20000000 in
-- Kernel reduction of the finite quotient and rough-seat carriers needs a larger expression budget.
theorem quotient1031_inputs_checked : rough1031.card = 316 ∧
    (∑ p ∈ active1031.filter (fun p => Nat.sqrt 1031 < p), primeAnchorProductWaveCount 1031 p) = 661 ∧
    (∑ p ∈ active1031.filter (fun p => Nat.sqrt 1031 < p), (rejectedThreeCalc 1031 p).card) = 363 := by
  decide +kernel

/-- The three inputs of the new certificate use no Cross or full incidence computation. -/
theorem quotient1031_structural_inputs :
    (∑ p ∈ roughActiveLabels 1031 (Nat.sqrt 1031), (sqrtRoughQuotientFiber 1031 p).card) = 661 ∧
    363 ≤ (∑ p ∈ roughActiveLabels 1031 (Nat.sqrt 1031), (sqrtRoughRejectedFiber 1031 p).card) ∧
    (canonicalRoughCandidates 1031 (Nat.sqrt 1031)).card = 316 := by
  have htotal : (∑ p ∈ roughActiveLabels 1031 (Nat.sqrt 1031),
      (sqrtRoughQuotientFiber 1031 p).card) = 661 := by
    rw [primeAnchor_quotient_range_eq_floor (by norm_num) (by decide) _ (fun _ hp => hp)]
    unfold roughActiveLabels
    rw [active1031_checked.1]
    exact quotient1031_inputs_checked.2.1
  have hJ : 363 ≤ ∑ p ∈ roughActiveLabels 1031 (Nat.sqrt 1031),
      (sqrtRoughRejectedFiber 1031 p).card := by
    have hsum := Finset.sum_le_sum (fun p (hp : p ∈ roughActiveLabels 1031 (Nat.sqrt 1031)) =>
      rejectedThree_card_le hp (by decide +kernel))
    have he : (∑ p ∈ roughActiveLabels 1031 (Nat.sqrt 1031), (rejectedThreeCalc 1031 p).card) = 363 := by
      unfold roughActiveLabels
      rw [active1031_checked.1]
      exact quotient1031_inputs_checked.2.2
    rwa [he] at hsum
  have hR : (canonicalRoughCandidates 1031 (Nat.sqrt 1031)).card = 316 := by
    have he : canonicalRoughCandidates 1031 (Nat.sqrt 1031) = rough1031 :=
      rough_inventory_normal_form active1031_checked.1 active1031_checked.2
    rw [he]
    exact quotient1031_inputs_checked.1
  exact ⟨htotal, hJ, hR⟩

/-- A new kernel-checked endpoint uses the corrected quotient budget with J=363. -/
theorem quotient1031_structural_endpoint : ∃ p, p.Prime ∧ SquareCell 1031 p := by
  obtain ⟨htotal, hJ, hR⟩ := quotient1031_structural_inputs
  apply prime_squareCell_of_quotient_routing_budget (by decide : 0 < 1031) hJ
  rw [htotal, hR]
  omega

/-- The same certificate guarantees at least 18 uncovered seats, without enumerating them. -/
theorem quotient1031_uncovered_lower : 18 ≤ (paritySafeUncoveredCandidates 1031).card := by
  obtain ⟨htotal, hJ, hR⟩ := quotient1031_structural_inputs
  have hcon := sqrt_quotient_conservation 1031
  have hcensus := sqrt_rough_factorization_census 1031
  rw [htotal] at hcon
  rw [hR] at hcensus
  omega

end DkMathTest.LegendreSqrtQuotientCalibration
