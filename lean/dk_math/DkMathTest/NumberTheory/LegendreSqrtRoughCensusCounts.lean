/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMathTest.NumberTheory.LegendreSqrtRoughMomentCalibration
import DkMath.NumberTheory.Legendre.ParitySafeSqrtRoughSingleton

#print "file: DkMathTest.NumberTheory.LegendreSqrtRoughCensusCounts"

namespace DkMathTest.LegendreSqrtRoughCensus
open DkMath.NumberTheory.Legendre DkMathTest.LegendreSqrtRoughMomentCalibration
open DkMathTest.LegendreBlockLocalization
open scoped BigOperators
set_option maxRecDepth 100000
set_option synthInstance.maxSize 1024

structure CensusRow where
  n : ℕ
  R : ℕ
  U : ℕ
  N1 : ℕ
  N2 : ℕ
  N3 : ℕ
  cube : ℕ
  cross : ℕ
  repeated : ℕ
  triple : ℕ
  deriving DecidableEq

def censusData : Finset CensusRow :=
  {⟨211, 82, 42, 35, 1, 4, 0, 35, 1, 4⟩, ⟨503, 169, 81, 78, 3, 7, 0, 78, 3, 7⟩,
   ⟨1009, 307, 151, 138, 4, 14, 0, 138, 4, 14⟩, ⟨1013, 311, 147, 154, 3, 7, 0, 154, 3, 7⟩,
   ⟨1019, 312, 135, 167, 1, 9, 0, 167, 1, 9⟩, ⟨1021, 311, 149, 142, 1, 19, 0, 142, 1, 19⟩}

def active1021 : Finset ℕ := insert 1019 (calibrationActive 1019)

def censusActive (n : ℕ) : Finset ℕ :=
  if n = 1021 then active1021 else calibrationActive n

/-- Reuse the verified 1019 inventory; only the two new boundary integers need consideration. -/
theorem active1021_checked : squareAnchorOddActivePrimes 1021 = active1021 ∧
    (active1021.filter (fun p => p ≤ Nat.sqrt 1021)) = calibrationSmall 1019 := by
  have h19 : Nat.Prime 1019 := by norm_num
  have h21 : Nat.Prime 1021 := by norm_num
  have hold := inventories_checked (1019, 31, 312, 196, 28, 9, 135) (by decide)
  have hA : squareAnchorOddActivePrimes 1019 = calibrationActive 1019 := hold.2.2.1
  constructor
  · rw [active1021, ← hA]
    ext p
    rw [mem_squareAnchorOddActivePrimes, Finset.mem_insert, mem_squareAnchorOddActivePrimes]
    constructor
    · rintro ⟨hp, hle, hnd, hne⟩
      by_cases he : p = 1019
      · exact Or.inl he
      · right
        have hp21 : p ≠ 1021 := by intro he; subst p; exact hnd (dvd_refl _)
        have hp20 : p ≠ 1020 := by intro he; subst p; norm_num at hp
        exact ⟨hp, by omega, by intro hd; exact he ((Nat.prime_dvd_prime_iff_eq hp h19).mp hd), hne⟩
    · rintro (rfl | ⟨hp, hle, _, hne⟩)
      · exact ⟨h19, by decide, by norm_num, by decide⟩
      · exact ⟨hp, by omega, by intro hd; have := (Nat.prime_dvd_prime_iff_eq hp h21).mp hd; omega, hne⟩
  · have hs21 : Nat.sqrt 1021 = 31 := by decide +kernel
    have hs19 : Nat.sqrt 1019 = 31 := hold.2.1
    have hsmall : (calibrationActive 1019).filter (fun p => p ≤ Nat.sqrt 1019) =
        calibrationSmall 1019 := hold.2.2.2
    rw [active1021, Finset.filter_insert, hs21, ite_eq_right (by decide : ¬1019 ≤ 31)]
    simpa only [hs19] using hsmall


/-- Existing five inventories plus one checked extra inventory. -/
theorem census_inventory_checked : ∀ t ∈ censusData,
    t.n.Prime ∧ 0 < t.n ∧ squareAnchorOddActivePrimes t.n = censusActive t.n := by
  have hmatch : ∀ t ∈ censusData, t.n ≠ 1021 → ∃ u ∈ momentData, u.1 = t.n := by decide +kernel
  intro t ht
  by_cases he : t.n = 1021
  · rw [he]; exact ⟨by norm_num, by decide, by simpa [censusActive] using active1021_checked.1⟩
  · obtain ⟨u, hu, heq⟩ := hmatch t ht he
    have h := inventories_checked u hu
    rw [heq] at h
    exact ⟨h.1, h.1.pos, by simpa [censusActive, he] using h.2.2.1⟩

/-- Only the new anchor's rough seats and local support are evaluated. -/
def rough1021 : Finset ℕ :=
  ((Finset.Icc 1 2042).filter (fun r => Nat.Coprime 1021 r ∧ (1021 ^ 2 + r) % 2 = 1)).filter
    (fun r => ∀ a ∈ calibrationSmall 1019, ¬ a ∣ 1021 ^ 2 + r)

def support1021 (r : ℕ) : Finset ℕ := active1021.filter (fun p => p ∣ 1021 ^ 2 + r)

set_option maxHeartbeats 20000000 in
-- Kernel reduction of the explicit finite numerical carrier needs a larger expression budget.
theorem rough1021_inputs_checked : rough1021.card = 311 ∧
    (∑ r ∈ rough1021, (support1021 r).card) = 201 ∧
    (∑ r ∈ rough1021, Nat.choose (support1021 r).card 2) = 58 ∧
    (∑ r ∈ rough1021, Nat.choose (support1021 r).card 3) = 19 := by
  decide +kernel


def cubeCalc (n : ℕ) : Finset ℕ :=
  ((censusActive n).filter (fun p => Nat.sqrt n < p)).filter
    (fun p => n ^ 2 < p ^ 3 ∧ p ^ 3 ≤ n ^ 2 + 2 * n)

/-- Calibration-only bounded primality test, proved equivalent to Nat.Prime. -/
def trialPrime (q : ℕ) : Prop := 2 ≤ q ∧ ∀ m ∈ Finset.Icc 2 (Nat.sqrt q), ¬m ∣ q

instance instDecidableTrialPrime (q : ℕ) : Decidable (trialPrime q) :=
  inferInstanceAs (Decidable (2 ≤ q ∧ ∀ m ∈ Finset.Icc 2 (Nat.sqrt q), ¬m ∣ q))

theorem trialPrime_iff (q : ℕ) : trialPrime q ↔ q.Prime := by
  rw [Nat.prime_def_le_sqrt]
  simp only [trialPrime, Finset.mem_Icc]
  tauto

set_option maxHeartbeats 20000000 in
-- Kernel reduction of the explicit finite numerical carrier needs a larger expression budget.
theorem cube_inputs_checked : ∀ t ∈ censusData, (cubeCalc t.n).card = t.cube := by
  decide +kernel


/-- Independent selected quotient-window checks; all-anchor Cross counts are recovered structurally. -/
def fiberCalc (n p : ℕ) : Finset ℕ :=
  (Finset.Ioc (max n (n ^ 2 / p)) ((n ^ 2 + 2 * n) / p)).filter trialPrime

set_option maxHeartbeats 20000000 in
-- Kernel reduction of the explicit finite numerical carrier needs a larger expression budget.
theorem selected_fibers_checked : (fiberCalc 211 41).card = 3 ∧
    (fiberCalc 1019 37).card = 7 ∧ (fiberCalc 1021 41).card = 7 := by
  decide +kernel


theorem census_row_arithmetic_checked : ∀ t ∈ censusData,
    t.N1 = t.cube + t.cross ∧ t.N2 = t.repeated ∧ t.N3 = t.triple ∧
    t.R = t.U + t.cube + t.cross + t.repeated + t.triple ∧
    t.cube + t.cross + t.repeated + t.triple < t.R := by
  decide +kernel

end DkMathTest.LegendreSqrtRoughCensus
