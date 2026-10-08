/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.SquareShellPrimePowerGauge

#print "file: DkMathTest.NumberTheory.SquareShellPrimePowerCalibration"

namespace DkMathTest.NumberTheory.SquareShellPrimePowerCalibration

open DkMath.NumberTheory DkMath.NumberTheory.Legendre

/-- The first shell has exactly its two prime labels and no higher events. -/
theorem prime_only_shell_checked :
    (Finset.Icc (1 ^ 2 + 1) (1 ^ 2 + 2 * 1)).filter Nat.Prime = {2, 3} ∧
    shellHigherPrimePowerEvents 1 = ∅ := by decide +kernel

/-- The first higher event is a cube, not prime birth. -/
theorem first_cube_shell_checked : shellHigherPrimePowerEvents 2 = {8} := by decide +kernel

/-- The first multiple-event shell has two different odd depths and bases. -/
theorem anchor5_events_checked : shellHigherPrimePowerEvents 5 = {27, 32} := by decide +kernel

theorem anchor5_depths_checked :
    27 = 3 ^ 3 ∧ 32 = 2 ^ 5 ∧ (27 : ℕ).factorization (27 : ℕ).minFac = 3 ∧
    (32 : ℕ).factorization (32 : ℕ).minFac = 5 := by decide +kernel

/-- A seventh-power event is present at the next preserved anchor. -/
theorem anchor11_events_checked : shellHigherPrimePowerEvents 11 = {125, 128} := by decide +kernel

theorem anchor11_depths_checked : 125 = 5 ^ 3 ∧ 128 = 2 ^ 7 := by norm_num

theorem anchor19_events_checked : shellHigherPrimePowerEvents 19 = ∅ := by decide +kernel

theorem anchor29_events_checked : shellHigherPrimePowerEvents 29 = ∅ := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- The finite base/depth computation certifies complete absence at a large anchor.
/-- Compact cube-cutoff certificate checks only small prime bases and finite depths. -/
theorem anchor297_bounded_powers_checked :
    ∀ p ∈ Nat.primesLE 44, ∀ a ∈ Finset.Icc 3 (Nat.log 2 ((297 + 1) ^ 2)),
      ¬ SquareCell 297 (p ^ a) := by
  unfold SquareCell
  decide +kernel

theorem anchor297_events_checked : shellHigherPrimePowerEvents 297 = ∅ :=
  shellHigherPrimePowerEvents_eq_empty_of_bounded_exclusion 297 44
    (by norm_num) anchor297_bounded_powers_checked

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- The finite base/depth computation certifies complete absence at a large anchor.
/-- Compact cube-cutoff certificate checks only small prime bases and finite depths. -/
theorem anchor1031_bounded_powers_checked :
    ∀ p ∈ Nat.primesLE 102, ∀ a ∈ Finset.Icc 3 (Nat.log 2 ((1031 + 1) ^ 2)),
      ¬ SquareCell 1031 (p ^ a) := by
  unfold SquareCell
  decide +kernel

theorem anchor1031_events_checked : shellHigherPrimePowerEvents 1031 = ∅ :=
  shellHigherPrimePowerEvents_eq_empty_of_bounded_exclusion 1031 102
    (by norm_num) anchor1031_bounded_powers_checked

/-- The exact nonempty correction for the first multiple-event shell. -/
theorem anchor5_higher_mass_checked :
    gnomonPascalShellHigherPrimePowerMass 5 = Real.log 3 + Real.log 2 := by
  rw [gnomonPascalShellHigherPrimePowerMass_eq_events, anchor5_events_checked]
  have h27 : IsPrimePow (27 : ℕ) := (isPrimePow_nat_iff 27).mpr ⟨3, 3, by norm_num, by omega, by norm_num⟩
  have h32 : IsPrimePow (32 : ℕ) := (isPrimePow_nat_iff 32).mpr ⟨2, 5, by norm_num, by omega, by norm_num⟩
  norm_num [ArithmeticFunction.vonMangoldt_apply, h27, h32]

/-- Empty higher carrier makes psi mass equal to genuine prime birth mass. -/
theorem anchor1031_mass_split_checked :
    gnomonPascalShellVonMangoldtMass 1031 = gnomonPascalShellBirthLogMass 1031 := by
  have hz : gnomonPascalShellHigherPrimePowerMass 1031 = 0 := by
    rw [gnomonPascalShellHigherPrimePowerMass_eq_events, anchor1031_events_checked,
      Finset.sum_empty]
  rw [gnomonPascalShellVonMangoldtMass_eq_birth_add_higher, hz, add_zero]

/-- Higher events have a strictly separated log gauge. -/
theorem cube_gauge_checked : pascalPrimePowerLogGauge 3 3 = 1 / 3 :=
  pascalPrimePowerLogGauge_eq (by norm_num) (by omega)

theorem fifth_gauge_checked : pascalPrimePowerLogGauge 2 5 = 1 / 5 :=
  pascalPrimePowerLogGauge_eq (by norm_num) (by omega)

/-- No even exponent contributes, including an exponent beyond the cube case. -/
theorem even_depth_shell_checked : ¬ SquareCell 297 (19 ^ 8) :=
  not_squareCell_even_power 297 19 8 (by decide +kernel)

/-- A full-row gcd-one certificate is distinct from a selected-cell birth witness. -/
theorem anchor5_top_row_checked : pascalInnerCommonDivisor (5 ^ 2 + 2 * 5) = 1 :=
  gnomon_top_innerCommonDivisor_eq_one (by omega)

/-- Generic small-budget consumer, retaining the missing lower-mass hypothesis. -/
theorem logarithmic_budget_consumer (n : ℕ) (hn : 3 ≤ n)
    (h : shellHigherPrimePowerLogBudget n < gnomonPascalShellVonMangoldtMass n) :
    ∃ p, p.Prime ∧ SquareCell n p := exists_prime_squareCell_of_logBudget_lt hn h

end DkMathTest.NumberTheory.SquareShellPrimePowerCalibration
