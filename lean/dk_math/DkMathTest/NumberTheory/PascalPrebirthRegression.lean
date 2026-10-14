/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PascalPrebirthBirth

#print "file: DkMathTest.NumberTheory.PascalPrebirthRegression"

namespace DkMathTest.NumberTheory.PascalPrebirthRegression

open DkMath.NumberTheory
open scoped BigOperators

/-- Finite count of nonzero adjacent residues; it is not assumed monotone. -/
def nonzeroDefectCount (d p : ℕ) : ℕ :=
  ((Finset.range d).filter (fun k => (Nat.choose d k + Nat.choose d (k + 1)) % p ≠ 0)).card

/-- Phase mismatches for the prime moduli used in these bounded diagnostics. -/
def phaseMismatchCount (d p : ℕ) : ℕ :=
  ((Finset.range (d + 1)).filter (fun k =>
    Nat.choose d k % p ≠ (if k % 2 = 0 then 1 % p else (p - 1) % p))).card

/-- Sum of centered adjacent residue magnitudes, with no real-distance claim. -/
def centeredDefectSum (d p : ℕ) : ℕ :=
  ∑ k ∈ Finset.range d, let r := (Nat.choose d k + Nat.choose d (k + 1)) % p
    min r (p - r)

/-- The natural diagnostic uses the production zero-defect criterion. -/
theorem diagnostic_residue_zero_iff (d p k : ℕ) :
    (Nat.choose d k + Nat.choose d (k + 1)) % p = 0 ↔
      pascalCancellationDefect d p k = 0 := by
  rw [pascalCancellationDefect_eq_zero_iff, ← Nat.dvd_iff_mod_eq_zero]
  simp only [Nat.choose_succ_succ]

/-- All three raw observables increase in the smallest prime-power scan example. -/
theorem binary_raw_increase_checked :
    nonzeroDefectCount 1 2 = 0 ∧ nonzeroDefectCount 2 2 = 2 ∧
    phaseMismatchCount 1 2 = 0 ∧ phaseMismatchCount 2 2 = 1 ∧
    centeredDefectSum 1 2 = 0 ∧ centeredDefectSum 2 2 = 2 := by decide

/-- Prime targets also have increases in raw defect and centered magnitude. -/
theorem prime_raw_increase_checked :
    nonzeroDefectCount 1 5 = 1 ∧ nonzeroDefectCount 2 5 = 2 ∧
    centeredDefectSum 1 5 = 2 ∧ centeredDefectSum 2 5 = 4 := by decide

/-- The prime-target phase mismatch increases before the exact boundary. -/
theorem prime_phase_increase_checked :
    phaseMismatchCount 2 5 = 1 ∧ phaseMismatchCount 3 5 = 3 := by decide

/-- Exact rational normalized counterexamples, including prime centered magnitude. -/
theorem normalized_increase_checked :
    (nonzeroDefectCount 1 2 : ℚ) / 1 < (nonzeroDefectCount 2 2 : ℚ) / 2 ∧
    (phaseMismatchCount 2 5 : ℚ) / 3 < (phaseMismatchCount 3 5 : ℚ) / 4 ∧
    (centeredDefectSum 1 7 : ℚ) / 1 < (centeredDefectSum 2 7 : ℚ) / 2 := by
  obtain ⟨h10, h22, _, _, _, _⟩ := binary_raw_increase_checked
  obtain ⟨h21, h33⟩ := prime_phase_increase_checked
  have hc1 : centeredDefectSum 1 7 = 2 := by decide
  have hc2 : centeredDefectSum 2 7 = 6 := by decide
  rw [h10, h22, h21, h33, hc1, hc2]
  norm_num

/-- The original binary endpoint includes the collapse of minus one and one. -/
theorem modulus_two_checked : PascalPrebirthAlternationMod 1 2 ∧ (-1 : ZMod 2) = 1 := by
  refine ⟨prime_prebirthAlternation (by norm_num : Nat.Prime 2), ?_⟩
  decide

/-- Modulus zero and modulus one require no extra assumptions in the generic theorem. -/
theorem degenerate_moduli_checked :
    PascalPrebirthAlternationMod 0 0 ∧ PascalPrebirthAlternationMod 3 1 := by
  constructor
  · apply (pascalPrebirthAlternationMod_iff_allInnerChooseDivisible _ _).mpr
    intro k hk0 hk; omega
  · apply (pascalPrebirthAlternationMod_iff_allInnerChooseDivisible _ _).mpr
    intro k _ _; exact one_dvd _

theorem row2_checked :
    pascalInnerCommonDivisor 2 = 2 ∧
    PascalPrebirthAlternationMod 1 2 ∧ AllInnerChooseDivisible 2 2 := by
  have hp : Nat.Prime 2 := by norm_num
  have ha : 0 < 1 := by omega
  have hg := pascalInnerCommonDivisor_prime_pow hp ha
  have hpacket := prime_power_prebirth_packet hp ha
  norm_num at hg hpacket
  exact ⟨hg, hpacket⟩

theorem row3_checked :
    pascalInnerCommonDivisor 3 = 3 ∧
    PascalPrebirthAlternationMod 2 3 ∧ AllInnerChooseDivisible 3 3 := by
  have hp : Nat.Prime 3 := by norm_num
  have ha : 0 < 1 := by omega
  have hg := pascalInnerCommonDivisor_prime_pow hp ha
  have hpacket := prime_power_prebirth_packet hp ha
  norm_num at hg hpacket
  exact ⟨hg, hpacket⟩

theorem row5_checked :
    pascalInnerCommonDivisor 5 = 5 ∧
    PascalPrebirthAlternationMod 4 5 ∧ AllInnerChooseDivisible 5 5 := by
  have hp : Nat.Prime 5 := by norm_num
  have ha : 0 < 1 := by omega
  have hg := pascalInnerCommonDivisor_prime_pow hp ha
  have hpacket := prime_power_prebirth_packet hp ha
  norm_num at hg hpacket
  exact ⟨hg, hpacket⟩

theorem row7_checked :
    pascalInnerCommonDivisor 7 = 7 ∧
    PascalPrebirthAlternationMod 6 7 ∧ AllInnerChooseDivisible 7 7 := by
  have hp : Nat.Prime 7 := by norm_num
  have ha : 0 < 1 := by omega
  have hg := pascalInnerCommonDivisor_prime_pow hp ha
  have hpacket := prime_power_prebirth_packet hp ha
  norm_num at hg hpacket
  exact ⟨hg, hpacket⟩

theorem row4_checked :
    pascalInnerCommonDivisor 4 = 2 ∧
    PascalPrebirthAlternationMod 3 2 ∧ AllInnerChooseDivisible 4 2 := by
  have hp : Nat.Prime 2 := by norm_num
  have ha : 0 < 2 := by omega
  have hg := pascalInnerCommonDivisor_prime_pow hp ha
  have hpacket := prime_power_prebirth_packet hp ha
  norm_num at hg hpacket
  exact ⟨hg, hpacket⟩

theorem row8_checked :
    pascalInnerCommonDivisor 8 = 2 ∧
    PascalPrebirthAlternationMod 7 2 ∧ AllInnerChooseDivisible 8 2 := by
  have hp : Nat.Prime 2 := by norm_num
  have ha : 0 < 3 := by omega
  have hg := pascalInnerCommonDivisor_prime_pow hp ha
  have hpacket := prime_power_prebirth_packet hp ha
  norm_num at hg hpacket
  exact ⟨hg, hpacket⟩

theorem row9_checked :
    pascalInnerCommonDivisor 9 = 3 ∧
    PascalPrebirthAlternationMod 8 3 ∧ AllInnerChooseDivisible 9 3 := by
  have hp : Nat.Prime 3 := by norm_num
  have ha : 0 < 2 := by omega
  have hg := pascalInnerCommonDivisor_prime_pow hp ha
  have hpacket := prime_power_prebirth_packet hp ha
  norm_num at hg hpacket
  exact ⟨hg, hpacket⟩

theorem row25_checked :
    pascalInnerCommonDivisor 25 = 5 ∧
    PascalPrebirthAlternationMod 24 5 ∧ AllInnerChooseDivisible 25 5 := by
  have hp : Nat.Prime 5 := by norm_num
  have ha : 0 < 2 := by omega
  have hg := pascalInnerCommonDivisor_prime_pow hp ha
  have hpacket := prime_power_prebirth_packet hp ha
  norm_num at hg hpacket
  exact ⟨hg, hpacket⟩

theorem row27_checked :
    pascalInnerCommonDivisor 27 = 3 ∧
    PascalPrebirthAlternationMod 26 3 ∧ AllInnerChooseDivisible 27 3 := by
  have hp : Nat.Prime 3 := by norm_num
  have ha : 0 < 3 := by omega
  have hg := pascalInnerCommonDivisor_prime_pow hp ha
  have hpacket := prime_power_prebirth_packet hp ha
  norm_num at hg hpacket
  exact ⟨hg, hpacket⟩

/-- Non-prime-power rows have unit common gcd; no custom detector is introduced. -/
theorem nonpower_rows_checked :
    ∀ N ∈ ({6, 10, 12, 15} : Finset ℕ),
      pascalInnerCommonDivisor N = 1 ∧ ¬ IsPrimePow N := by
  intro N hN
  have hg : pascalInnerCommonDivisor N = 1 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hN
    rcases hN with rfl | rfl | rfl | rfl <;> decide
  refine ⟨hg, ?_⟩
  intro hpow
  have hp := Nat.minFac_prime hpow.ne_one
  have he := pascalInnerCommonDivisor_eq_minFac hpow
  rw [← he, hg] at hp
  exact Nat.not_prime_one hp

/-- Selected exact prime-power dial heights retain index valuation depth. -/
theorem dials_checked :
    pascalPrimeDialHeight 2 8 1 = 3 ∧ pascalPrimeDialHeight 2 8 2 = 2 ∧
    pascalPrimeDialHeight 2 8 4 = 1 ∧ pascalPrimeDialHeight 3 9 3 = 1 ∧
    pascalPrimeDialHeight 5 25 5 = 1 ∧ pascalPrimeDialHeight 3 27 3 = 2 := by
  let : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  let : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h4 : padicValNat 2 4 = 2 := by
    simpa using (padicValNat.prime_pow (p := 2) 2)
  have h81 := pascalPrimeDialHeight_prime_pow (p := 2) (n := 3) (k := 1)
    (by norm_num) (by norm_num) (by norm_num)
  have h82 := pascalPrimeDialHeight_prime_pow (p := 2) (n := 3) (k := 2)
    (by norm_num) (by norm_num) (by norm_num)
  have h84 := pascalPrimeDialHeight_prime_pow (p := 2) (n := 3) (k := 4)
    (by norm_num) (by norm_num) (by norm_num)
  have h93 := pascalPrimeDialHeight_prime_pow (p := 3) (n := 2) (k := 3)
    (by norm_num) (by norm_num) (by norm_num)
  have h255 := pascalPrimeDialHeight_prime_pow (p := 5) (n := 2) (k := 5)
    (by norm_num) (by norm_num) (by norm_num)
  have h273 := pascalPrimeDialHeight_prime_pow (p := 3) (n := 3) (k := 3)
    (by norm_num) (by norm_num) (by norm_num)
  norm_num [padicValNat_self, h4] at h81 h82 h84 h93 h255 h273
  exact ⟨h81, h82, h84, h93, h255, h273⟩

/-- Higher powers are synchronized coordinates, not new base-coordinate births. -/
theorem resynchronization_checked :
    2 ∉ pascalPrimeCoordinateBirthSupport 8 ∧ 3 ∉ pascalPrimeCoordinateBirthSupport 9 := by
  constructor
  · rw [show 8 = 2 ^ 3 by norm_num, prime_power_coordinate_birth_iff (by norm_num) (by omega)]
    omega
  · rw [show 9 = 3 ^ 2 by norm_num, prime_power_coordinate_birth_iff (by norm_num) (by omega)]
    omega

end DkMathTest.NumberTheory.PascalPrebirthRegression
