/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.GnomonSmallCarryPhase

#print "file: DkMathTest.NumberTheory.GnomonSmallCarryPhaseCalibration"

namespace DkMathTest.NumberTheory.GnomonSmallCarryPhaseCalibration
open DkMath.NumberTheory.Legendre
open scoped BigOperators

/-- Pointwise inclusion in central-binomial carry coordinates is false. -/
theorem pointwise4_counterexample :
    gnomonLowDivisorCarryBit 4 3 = 1 ∧
    ¬ 3 ≤ 4 % 3 + 4 % 3 ∧ (Nat.choose 8 4).factorization 3 = 0 := by
  decide +kernel

/-- The bounded exclusion deliberately does not enumerate the entire zero-carry complement. -/
theorem exclusion32_proper : gnomonLowDivisorCarryBit 32 53 = 0 ∧
    53 ∉ gnomonSmallPhaseExclusions 32 := by
  decide +kernel

theorem central27_product_checked :
    (∏ d ∈ gnomonPascalSmallCarryEvents 27, d.minFac) ≤ Nat.choose 54 27 := by
  rw [Nat.choose_eq_fast_choose]
  decide +kernel

/-- A finite proof at the difficult anchor, not a universal central-binomial bound. -/
theorem central27_checked : gnomonPascalSmallCarryMass 27 ≤
    Real.log (Nat.choose 54 27 : ℝ) := by
  have hs : gnomonPascalSmallCarryMass 27 =
      Real.log ((∏ d ∈ gnomonPascalSmallCarryEvents 27, d.minFac : ℕ) : ℝ) := by
    unfold gnomonPascalSmallCarryMass
    rw [Nat.cast_prod, Real.log_prod]
    · apply Finset.sum_congr rfl
      intro d hd
      have hp := (mem_gnomonPascalLowCarryEvents.mp (Finset.mem_filter.mp hd).1).2.2.1
      simp [ArithmeticFunction.vonMangoldt_apply, hp]
    · intro d _
      exact_mod_cast (Nat.minFac_pos d).ne'
  rw [hs]
  apply Real.log_le_log
  · exact_mod_cast (Finset.prod_pos (fun d _ => Nat.minFac_pos d) :
      0 < ∏ d ∈ gnomonPascalSmallCarryEvents 27, d.minFac)
  · exact_mod_cast central27_product_checked

theorem anchor_phase_bound {n : ℕ}
    (hn : n ∈ ({27, 32, 69, 210, 297, 1031, 5000} : Finset ℕ)) :
    gnomonNonSingletonCorrection n ≤ gnomonPhaseCorrectionBudget n ∧
      gnomonPhaseCorrectionBudget n ≤ gnomonNonSingletonBudget n := by
  refine ⟨gnomonNonSingletonCorrection_le_phaseBudget ?_,
    gnomonPhaseCorrectionBudget_le_previous n⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  omega

end DkMathTest.NumberTheory.GnomonSmallCarryPhaseCalibration
