/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.GnomonPascalCell
import DkMath.Pascal.WallisCellGrowth

#print "file: DkMathTest.NumberTheory.LegendrePascalCellCalibration"

namespace DkMathTest.NumberTheory.LegendrePascalCellCalibration

open DkMath.NumberTheory DkMath.NumberTheory.Legendre

/-- The existing arbitrary-cell growth evaluator lands on the new gnomon cell. -/
theorem wallisCellGrowth_bridge (n : ℕ) :
    DkMath.Pascal.WallisCellGrowth.pascalCellGrowthQ (n ^ 2 + 2 * n) (2 * n) =
      (GnomonPascalCell n : ℚ) :=
  DkMath.Pascal.WallisCellGrowth.pascalCellGrowthQ_eq_cast_choose _ _

/-- Preflight arithmetic agrees with the existing 024 proved support carriers. -/
theorem report024_arithmetic_checked :
    297 ^ 2 + 350 = 88559 ∧ 88559 = 19 * 59 * 79 ∧
    1031 ^ 2 + 90 = 1063051 ∧ 1063051 = 11 * 241 * 401 := by norm_num

/-- One prime witness checks both new interfaces without printing a binomial coefficient. -/
theorem anchor5_checked :
    29 ∣ GnomonPascalCell 5 ∧ (GnomonPascalCell 5).factorization 29 = 1 ∧
    0 < gnomonPascalShellBirthLogMass 5 := by
  have hp : Nat.Prime 29 := by norm_num
  have hc : SquareCell 5 29 := by norm_num [SquareCell]
  exact ⟨(prime_dvd_gnomonPascalCell_iff (by omega) hp hc.1).mpr hc,
    gnomonPascalCell_fresh_height_eq_one (by omega) hp hc,
    (gnomonPascalShellBirthLogMass_pos_iff 5).mpr ⟨29, hp, hc⟩⟩

/-- One prime witness checks both new interfaces without printing a binomial coefficient. -/
theorem anchor11_checked :
    127 ∣ GnomonPascalCell 11 ∧ (GnomonPascalCell 11).factorization 127 = 1 ∧
    0 < gnomonPascalShellBirthLogMass 11 := by
  have hp : Nat.Prime 127 := by norm_num
  have hc : SquareCell 11 127 := by norm_num [SquareCell]
  exact ⟨(prime_dvd_gnomonPascalCell_iff (by omega) hp hc.1).mpr hc,
    gnomonPascalCell_fresh_height_eq_one (by omega) hp hc,
    (gnomonPascalShellBirthLogMass_pos_iff 11).mpr ⟨127, hp, hc⟩⟩

/-- One prime witness checks both new interfaces without printing a binomial coefficient. -/
theorem anchor19_checked :
    367 ∣ GnomonPascalCell 19 ∧ (GnomonPascalCell 19).factorization 367 = 1 ∧
    0 < gnomonPascalShellBirthLogMass 19 := by
  have hp : Nat.Prime 367 := by norm_num
  have hc : SquareCell 19 367 := by norm_num [SquareCell]
  exact ⟨(prime_dvd_gnomonPascalCell_iff (by omega) hp hc.1).mpr hc,
    gnomonPascalCell_fresh_height_eq_one (by omega) hp hc,
    (gnomonPascalShellBirthLogMass_pos_iff 19).mpr ⟨367, hp, hc⟩⟩

/-- One prime witness checks both new interfaces without printing a binomial coefficient. -/
theorem anchor29_checked :
    853 ∣ GnomonPascalCell 29 ∧ (GnomonPascalCell 29).factorization 853 = 1 ∧
    0 < gnomonPascalShellBirthLogMass 29 := by
  have hp : Nat.Prime 853 := by norm_num
  have hc : SquareCell 29 853 := by norm_num [SquareCell]
  exact ⟨(prime_dvd_gnomonPascalCell_iff (by omega) hp hc.1).mpr hc,
    gnomonPascalCell_fresh_height_eq_one (by omega) hp hc,
    (gnomonPascalShellBirthLogMass_pos_iff 29).mpr ⟨853, hp, hc⟩⟩

/-- One prime witness checks both new interfaces without printing a binomial coefficient. -/
theorem anchor297_checked :
    88211 ∣ GnomonPascalCell 297 ∧ (GnomonPascalCell 297).factorization 88211 = 1 ∧
    0 < gnomonPascalShellBirthLogMass 297 := by
  have hp : Nat.Prime 88211 := by norm_num
  have hc : SquareCell 297 88211 := by norm_num [SquareCell]
  exact ⟨(prime_dvd_gnomonPascalCell_iff (by omega) hp hc.1).mpr hc,
    gnomonPascalCell_fresh_height_eq_one (by omega) hp hc,
    (gnomonPascalShellBirthLogMass_pos_iff 297).mpr ⟨88211, hp, hc⟩⟩

/-- One prime witness checks both new interfaces without printing a binomial coefficient. -/
theorem anchor1031_checked :
    1062977 ∣ GnomonPascalCell 1031 ∧ (GnomonPascalCell 1031).factorization 1062977 = 1 ∧
    0 < gnomonPascalShellBirthLogMass 1031 := by
  have hp : Nat.Prime 1062977 := by norm_num
  have hc : SquareCell 1031 1062977 := by norm_num [SquareCell]
  exact ⟨(prime_dvd_gnomonPascalCell_iff (by omega) hp hc.1).mpr hc,
    gnomonPascalCell_fresh_height_eq_one (by omega) hp hc,
    (gnomonPascalShellBirthLogMass_pos_iff 1031).mpr ⟨1062977, hp, hc⟩⟩

/-- Zero anchor has empty birth mass, so the positivity equivalence handles it cleanly. -/
theorem anchor_zero_checked : gnomonPascalShellBirthLogMass 0 = 0 := by
  simp [gnomonPascalShellBirthLogMass, squareOffsets]

/-- The rational ratio theorem cannot be extended to the zero anchor. -/
theorem ratio_zero_obstruction_checked :
    (2 * 0 : ℚ) / ((0 : ℚ) ^ 2 + 2 * 0) ≠ 2 / ((0 : ℚ) + 2) := by norm_num

/-- The exact old-budget deficit supplies only a conditional local witness. -/
theorem old_budget_consumer (n : ℕ) (hn : 3 ≤ n)
    (h : gnomonPascalOldLogBudget n < Real.log (GnomonPascalCell n : ℝ)) :
    ∃ p, p.Prime ∧ SquareCell n p := (gnomonPascalOldLogBudget_lt_iff hn).mp h

end DkMathTest.NumberTheory.LegendrePascalCellCalibration
