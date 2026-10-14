/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.GnomonDivisorCarry
import DkMathTest.NumberTheory.SquareShellPrimePowerCalibration

#print "file: DkMathTest.NumberTheory.GnomonDivisorCarryCalibration"

namespace DkMathTest.NumberTheory.GnomonDivisorCarryCalibration

open DkMath.NumberTheory DkMath.NumberTheory.Legendre

/-- A symbolic finite packet checks every requested carry coordinate. -/
theorem carry_packet {n d p a : ℕ} (hp : p.Prime) (ha : 0 < a)
    (hpow : p ^ a = d) (hlo : 1 ≤ d) (hold : d ≤ n ^ 2)
    (hc : gnomonLowDivisorCarryBit n d = 1) :
    d ∈ gnomonPascalLowCarryEvents n ∧ IsPrimePow d ∧
    gnomonLowDivisorCarryBit n d = 1 ∧ d ≤ n ^ 2 % d + (2 * n) % d ∧
    gnomonShellMultipleCount n d = (2 * n) / d + 1 ∧
    ArithmeticFunction.vonMangoldt d = Real.log (p : ℝ) := by
  have hpp := (isPrimePow_nat_iff d).mpr ⟨p, a, hp, ha, hpow⟩
  refine ⟨mem_gnomonPascalLowCarryEvents.mpr ⟨hlo, hold, hpp, hc⟩, hpp, hc,
    (gnomonLowDivisorCarryBit_eq_one_iff hlo).mp hc, ?_, ?_⟩
  · rw [gnomonShellMultipleCount_eq_div_add_carry hlo, hc]
  · rw [← hpow]; exact gnomonCarry_prime_pow_weight hp ha

/-- Large packets certify the constructed multiple and its universal uniqueness. -/
theorem large_packet {n d m : ℕ} (hd : 2 * n < d)
    (hc : gnomonLowDivisorCarryBit n d = 1) (he : gnomonNextShellMultiple n d = m) :
    SquareCell n m ∧ d ∣ m ∧ gnomonShellMultipleCount n d = 1 ∧
    ∀ m', SquareCell n m' → d ∣ m' → m' = m := by
  have h := gnomonNextShellMultiple_packet hd hc
  refine ⟨he ▸ h.1, he ▸ h.2, ?_, ?_⟩
  · rw [gnomonShellMultipleCount_eq_div_add_carry (by omega : 0 < d),
      Nat.div_eq_of_lt hd, hc]
  · intro m' hm' hdiv
    exact (gnomonNextShellMultiple_unique hd hc hm' hdiv).trans he

/-- Complete finite old carry carrier at anchor 3. -/
theorem events3_checked : gnomonPascalLowCarryEvents 3 = {5, 7} := by
  decide +kernel

/-- Complete finite old carry carrier at anchor 5. -/
theorem events5_checked : gnomonPascalLowCarryEvents 5 = {7, 11, 13, 16, 17} := by
  decide +kernel

/-- Complete finite old carry carrier at anchor 11. -/
theorem events11_checked : gnomonPascalLowCarryEvents 11 = {13, 23, 25, 27, 31, 32, 41, 43, 47, 61, 64, 67, 71} := by
  decide +kernel

/-- Prime base, depth, bit, remainder, multiple count and exact weight at 3:5. -/
theorem carry3_5_checked :
    5 ∈ gnomonPascalLowCarryEvents 3 ∧ IsPrimePow 5 ∧
    gnomonLowDivisorCarryBit 3 5 = 1 ∧
    5 ≤ 3 ^ 2 % 5 + (2 * 3) % 5 ∧
    gnomonShellMultipleCount 3 5 = (2 * 3) / 5 + 1 ∧
    ArithmeticFunction.vonMangoldt 5 = Real.log (5 : ℝ) := by
  exact carry_packet (p := 5) (a := 1) (by norm_num) (by omega)
    (by norm_num) (by omega) (by norm_num) (by decide +kernel)

/-- Prime base, depth, bit, remainder, multiple count and exact weight at 3:7. -/
theorem carry3_7_checked :
    7 ∈ gnomonPascalLowCarryEvents 3 ∧ IsPrimePow 7 ∧
    gnomonLowDivisorCarryBit 3 7 = 1 ∧
    7 ≤ 3 ^ 2 % 7 + (2 * 3) % 7 ∧
    gnomonShellMultipleCount 3 7 = (2 * 3) / 7 + 1 ∧
    ArithmeticFunction.vonMangoldt 7 = Real.log (7 : ℝ) := by
  exact carry_packet (p := 7) (a := 1) (by norm_num) (by omega)
    (by norm_num) (by omega) (by norm_num) (by decide +kernel)

/-- A large event has the indicated shell multiple and no other one. -/
theorem multiple3_7_checked :
    SquareCell 3 14 ∧ 7 ∣ 14 ∧ gnomonShellMultipleCount 3 7 = 1 ∧
    ∀ m', SquareCell 3 m' → 7 ∣ m' → m' = 14 := by
  exact large_packet (by omega) (by decide +kernel) (by decide +kernel)

/-- Prime base, depth, bit, remainder, multiple count and exact weight at 5:7. -/
theorem carry5_7_checked :
    7 ∈ gnomonPascalLowCarryEvents 5 ∧ IsPrimePow 7 ∧
    gnomonLowDivisorCarryBit 5 7 = 1 ∧
    7 ≤ 5 ^ 2 % 7 + (2 * 5) % 7 ∧
    gnomonShellMultipleCount 5 7 = (2 * 5) / 7 + 1 ∧
    ArithmeticFunction.vonMangoldt 7 = Real.log (7 : ℝ) := by
  exact carry_packet (p := 7) (a := 1) (by norm_num) (by omega)
    (by norm_num) (by omega) (by norm_num) (by decide +kernel)

/-- Prime base, depth, bit, remainder, multiple count and exact weight at 5:16. -/
theorem carry5_16_checked :
    16 ∈ gnomonPascalLowCarryEvents 5 ∧ IsPrimePow 16 ∧
    gnomonLowDivisorCarryBit 5 16 = 1 ∧
    16 ≤ 5 ^ 2 % 16 + (2 * 5) % 16 ∧
    gnomonShellMultipleCount 5 16 = (2 * 5) / 16 + 1 ∧
    ArithmeticFunction.vonMangoldt 16 = Real.log (2 : ℝ) := by
  exact carry_packet (p := 2) (a := 4) (by norm_num) (by omega)
    (by norm_num) (by omega) (by norm_num) (by decide +kernel)

/-- A large event has the indicated shell multiple and no other one. -/
theorem multiple5_16_checked :
    SquareCell 5 32 ∧ 16 ∣ 32 ∧ gnomonShellMultipleCount 5 16 = 1 ∧
    ∀ m', SquareCell 5 m' → 16 ∣ m' → m' = 32 := by
  exact large_packet (by omega) (by decide +kernel) (by decide +kernel)

/-- Prime base, depth, bit, remainder, multiple count and exact weight at 11:13. -/
theorem carry11_13_checked :
    13 ∈ gnomonPascalLowCarryEvents 11 ∧ IsPrimePow 13 ∧
    gnomonLowDivisorCarryBit 11 13 = 1 ∧
    13 ≤ 11 ^ 2 % 13 + (2 * 11) % 13 ∧
    gnomonShellMultipleCount 11 13 = (2 * 11) / 13 + 1 ∧
    ArithmeticFunction.vonMangoldt 13 = Real.log (13 : ℝ) := by
  exact carry_packet (p := 13) (a := 1) (by norm_num) (by omega)
    (by norm_num) (by omega) (by norm_num) (by decide +kernel)

/-- Prime base, depth, bit, remainder, multiple count and exact weight at 11:32. -/
theorem carry11_32_checked :
    32 ∈ gnomonPascalLowCarryEvents 11 ∧ IsPrimePow 32 ∧
    gnomonLowDivisorCarryBit 11 32 = 1 ∧
    32 ≤ 11 ^ 2 % 32 + (2 * 11) % 32 ∧
    gnomonShellMultipleCount 11 32 = (2 * 11) / 32 + 1 ∧
    ArithmeticFunction.vonMangoldt 32 = Real.log (2 : ℝ) := by
  exact carry_packet (p := 2) (a := 5) (by norm_num) (by omega)
    (by norm_num) (by omega) (by norm_num) (by decide +kernel)

/-- A large event has the indicated shell multiple and no other one. -/
theorem multiple11_32_checked :
    SquareCell 11 128 ∧ 32 ∣ 128 ∧ gnomonShellMultipleCount 11 32 = 1 ∧
    ∀ m', SquareCell 11 m' → 32 ∣ m' → m' = 128 := by
  exact large_packet (by omega) (by decide +kernel) (by decide +kernel)

/-- Prime base, depth, bit, remainder, multiple count and exact weight at 11:64. -/
theorem carry11_64_checked :
    64 ∈ gnomonPascalLowCarryEvents 11 ∧ IsPrimePow 64 ∧
    gnomonLowDivisorCarryBit 11 64 = 1 ∧
    64 ≤ 11 ^ 2 % 64 + (2 * 11) % 64 ∧
    gnomonShellMultipleCount 11 64 = (2 * 11) / 64 + 1 ∧
    ArithmeticFunction.vonMangoldt 64 = Real.log (2 : ℝ) := by
  exact carry_packet (p := 2) (a := 6) (by norm_num) (by omega)
    (by norm_num) (by omega) (by norm_num) (by decide +kernel)

/-- A large event has the indicated shell multiple and no other one. -/
theorem multiple11_64_checked :
    SquareCell 11 128 ∧ 64 ∣ 128 ∧ gnomonShellMultipleCount 11 64 = 1 ∧
    ∀ m', SquareCell 11 m' → 64 ∣ m' → m' = 128 := by
  exact large_packet (by omega) (by decide +kernel) (by decide +kernel)

/-- Prime base, depth, bit, remainder, multiple count and exact weight at 297:25. -/
theorem carry297_25_checked :
    25 ∈ gnomonPascalLowCarryEvents 297 ∧ IsPrimePow 25 ∧
    gnomonLowDivisorCarryBit 297 25 = 1 ∧
    25 ≤ 297 ^ 2 % 25 + (2 * 297) % 25 ∧
    gnomonShellMultipleCount 297 25 = (2 * 297) / 25 + 1 ∧
    ArithmeticFunction.vonMangoldt 25 = Real.log (5 : ℝ) := by
  exact carry_packet (p := 5) (a := 2) (by norm_num) (by omega)
    (by norm_num) (by omega) (by norm_num) (by decide +kernel)

/-- Prime base, depth, bit, remainder, multiple count and exact weight at 297:625. -/
theorem carry297_625_checked :
    625 ∈ gnomonPascalLowCarryEvents 297 ∧ IsPrimePow 625 ∧
    gnomonLowDivisorCarryBit 297 625 = 1 ∧
    625 ≤ 297 ^ 2 % 625 + (2 * 297) % 625 ∧
    gnomonShellMultipleCount 297 625 = (2 * 297) / 625 + 1 ∧
    ArithmeticFunction.vonMangoldt 625 = Real.log (5 : ℝ) := by
  exact carry_packet (p := 5) (a := 4) (by norm_num) (by omega)
    (by norm_num) (by omega) (by norm_num) (by decide +kernel)

/-- A large event has the indicated shell multiple and no other one. -/
theorem multiple297_625_checked :
    SquareCell 297 88750 ∧ 625 ∣ 88750 ∧ gnomonShellMultipleCount 297 625 = 1 ∧
    ∀ m', SquareCell 297 m' → 625 ∣ m' → m' = 88750 := by
  exact large_packet (by omega) (by decide +kernel) (by decide +kernel)

/-- Prime base, depth, bit, remainder, multiple count and exact weight at 1031:27. -/
theorem carry1031_27_checked :
    27 ∈ gnomonPascalLowCarryEvents 1031 ∧ IsPrimePow 27 ∧
    gnomonLowDivisorCarryBit 1031 27 = 1 ∧
    27 ≤ 1031 ^ 2 % 27 + (2 * 1031) % 27 ∧
    gnomonShellMultipleCount 1031 27 = (2 * 1031) / 27 + 1 ∧
    ArithmeticFunction.vonMangoldt 27 = Real.log (3 : ℝ) := by
  exact carry_packet (p := 3) (a := 3) (by norm_num) (by omega)
    (by norm_num) (by omega) (by norm_num) (by decide +kernel)

/-- Prime base, depth, bit, remainder, multiple count and exact weight at 1031:4096. -/
theorem carry1031_4096_checked :
    4096 ∈ gnomonPascalLowCarryEvents 1031 ∧ IsPrimePow 4096 ∧
    gnomonLowDivisorCarryBit 1031 4096 = 1 ∧
    4096 ≤ 1031 ^ 2 % 4096 + (2 * 1031) % 4096 ∧
    gnomonShellMultipleCount 1031 4096 = (2 * 1031) / 4096 + 1 ∧
    ArithmeticFunction.vonMangoldt 4096 = Real.log (2 : ℝ) := by
  exact carry_packet (p := 2) (a := 12) (by norm_num) (by omega)
    (by norm_num) (by omega) (by norm_num) (by decide +kernel)

/-- A large event has the indicated shell multiple and no other one. -/
theorem multiple1031_4096_checked :
    SquareCell 1031 1064960 ∧ 4096 ∣ 1064960 ∧ gnomonShellMultipleCount 1031 4096 = 1 ∧
    ∀ m', SquareCell 1031 m' → 4096 ∣ m' → m' = 1064960 := by
  exact large_packet (by omega) (by decide +kernel) (by decide +kernel)

/-- Explicit same-base collision invalidates label injectivity. -/
theorem collision11_checked :
    32 ∈ gnomonPascalLargeCarryEvents 11 ∧ 64 ∈ gnomonPascalLargeCarryEvents 11 ∧
    (32 : ℕ) ≠ 64 ∧ gnomonNextShellMultiple 11 32 = 128 ∧
    gnomonNextShellMultiple 11 64 = 128 := by
  decide +kernel

/-- The map on the exact large carrier is not injective. -/
theorem large_map11_not_injective :
    ¬ Set.InjOn (gnomonNextShellMultiple 11) (gnomonPascalLargeCarryEvents 11) := by
  intro h
  have c := collision11_checked
  have he := h c.1 c.2.1 (c.2.2.2.1.trans c.2.2.2.2.symm)
  exact c.2.2.1 he

/-- No collision occurs at any earlier positive anchor; this is a finite certificate. -/
theorem earlier_large_maps_injective :
    ∀ n ∈ Finset.Icc 1 10, ∀ d ∈ gnomonPascalLargeCarryEvents n,
      ∀ e ∈ gnomonPascalLargeCarryEvents n,
        gnomonNextShellMultiple n d = gnomonNextShellMultiple n e → d = e := by
  decide +kernel

/-- The inherited complete higher-event certificate fixes a zero correction. -/
theorem higher19_zero_checked : gnomonPascalShellHigherPrimePowerMass 19 = 0 := by
  rw [gnomonPascalShellHigherPrimePowerMass_eq_events,
    DkMathTest.NumberTheory.SquareShellPrimePowerCalibration.anchor19_events_checked]
  simp

/-- Zero higher correction identifies the old budget with the binary carrier mass. -/
theorem ledger19_checked :
    gnomonPascalOldLogBudget 19 = gnomonPascalLowDivisorCarryMass 19 ∧
    Real.log (GnomonPascalCell 19 : ℝ) =
      gnomonPascalShellVonMangoldtMass 19 + gnomonPascalLowDivisorCarryMass 19 := by
  constructor
  · simpa only [higher19_zero_checked, zero_add] using
      gnomonPascalOldLogBudget_eq_higher_add_lowCarryMass (n := 19) (by omega)
  · exact gnomonPascalCell_log_eq_shellVM_add_lowCarryMass (by omega)

/-- The inherited complete higher-event certificate fixes a zero correction. -/
theorem higher297_zero_checked : gnomonPascalShellHigherPrimePowerMass 297 = 0 := by
  rw [gnomonPascalShellHigherPrimePowerMass_eq_events,
    DkMathTest.NumberTheory.SquareShellPrimePowerCalibration.anchor297_events_checked]
  simp

/-- Zero higher correction identifies the old budget with the binary carrier mass. -/
theorem ledger297_checked :
    gnomonPascalOldLogBudget 297 = gnomonPascalLowDivisorCarryMass 297 ∧
    Real.log (GnomonPascalCell 297 : ℝ) =
      gnomonPascalShellVonMangoldtMass 297 + gnomonPascalLowDivisorCarryMass 297 := by
  constructor
  · simpa only [higher297_zero_checked, zero_add] using
      gnomonPascalOldLogBudget_eq_higher_add_lowCarryMass (n := 297) (by omega)
  · exact gnomonPascalCell_log_eq_shellVM_add_lowCarryMass (by omega)

/-- The inherited complete higher-event certificate fixes a zero correction. -/
theorem higher1031_zero_checked : gnomonPascalShellHigherPrimePowerMass 1031 = 0 := by
  rw [gnomonPascalShellHigherPrimePowerMass_eq_events,
    DkMathTest.NumberTheory.SquareShellPrimePowerCalibration.anchor1031_events_checked]
  simp

/-- Zero higher correction identifies the old budget with the binary carrier mass. -/
theorem ledger1031_checked :
    gnomonPascalOldLogBudget 1031 = gnomonPascalLowDivisorCarryMass 1031 ∧
    Real.log (GnomonPascalCell 1031 : ℝ) =
      gnomonPascalShellVonMangoldtMass 1031 + gnomonPascalLowDivisorCarryMass 1031 := by
  constructor
  · simpa only [higher1031_zero_checked, zero_add] using
      gnomonPascalOldLogBudget_eq_higher_add_lowCarryMass (n := 1031) (by omega)
  · exact gnomonPascalCell_log_eq_shellVM_add_lowCarryMass (by omega)

/-- Total conventions and the strictly next multiple on an aligned boundary. -/
theorem zero_and_aligned_checked :
    gnomonShellMultipleCount 5 0 = 0 ∧ gnomonLowDivisorCarryBit 5 0 = 0 ∧
    nextMultipleGap 25 0 = 0 ∧ nextMultipleGap 25 5 = 5 := by
  decide +kernel

end DkMathTest.NumberTheory.GnomonDivisorCarryCalibration
