/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.GnomonNonSingletonCorrection

#print "file: DkMathTest.NumberTheory.GnomonNonSingletonCorrectionCalibration"

namespace DkMathTest.NumberTheory.GnomonNonSingletonCorrectionCalibration
open DkMath.NumberTheory.Legendre

/-- Repeated carry uses actual nonprime powers, distinct from singleton fibers. -/
theorem repeated32_checked :
    (gnomonPascalLargeCarryEvents 32).filter (fun d => ¬ d.Prime) = {81, 343, 361, 529} := by
  decide +kernel

/-- Low and large bands cannot double-charge the same prime-power label. -/
theorem separated32_checked :
    25 ∈ gnomonPascalSmallCarryEvents 32 ∧
    25 ∉ (gnomonPascalLargeCarryEvents 32).filter (fun d => ¬ d.Prime) ∧
    81 ∉ gnomonPascalSmallCarryEvents 32 := by
  decide +kernel

theorem anchor_compression {n : ℕ}
    (hn : n ∈ ({32, 69, 210, 297, 1031, 5000} : Finset ℕ)) :
    gnomonNonSingletonCorrection n ≤ gnomonNonSingletonBudget n := by
  apply gnomonNonSingletonCorrection_le_budget
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  omega

theorem anchor_exact_split {n : ℕ}
    (hn : n ∈ ({32, 69, 210, 297, 1031, 5000} : Finset ℕ)) :
    gnomonPascalOldLogBudget n = gnomonCofactorWindowMass n +
      gnomonNonSingletonCorrection n := by
  apply gnomonPascalOldLogBudget_eq_singleton_add_correction
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  omega

end DkMathTest.NumberTheory.GnomonNonSingletonCorrectionCalibration
