/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Cosmic.GTailSevenValuation

#print "file: DkMathTest.CosmicFormula.GTailSevenValuation"

/-! Satisfiable exact-layer regressions and missing-premise counterexamples. -/

namespace DkMathTest.CosmicFormula.GTailSevenValuation

open DkMath.CosmicFormula

example : padicValNat 7 (GTail 7 1 7 (2 : ℕ)) = 1 :=
  padicValNat_gtail_seven_eq_one (by norm_num) (by norm_num)

example : padicValNat 7 (GTail 7 1 14 (2 : ℕ)) = 1 :=
  padicValNat_gtail_seven_eq_one (by norm_num) (by norm_num)

example : padicValNat 7 (7 * GTail 7 1 7 (2 : ℕ)) = 2 := by
  rw [padicValNat_gap_mul_gtail_seven (by norm_num) (by norm_num) (by norm_num)]
  norm_num

example : padicValNat 7 (14 * GTail 7 1 14 (2 : ℕ)) = 2 := by
  rw [padicValNat_gap_mul_gtail_seven (by norm_num) (by norm_num) (by norm_num)]
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  have h14 : (14 : ℕ) = 7 * 2 := by norm_num
  rw [h14, padicValNat.mul (by norm_num) (by norm_num)]
  norm_num [padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 7 ∣ (2 : ℕ))]

-- The residual theorem does not need a nonzero gap.
example : padicValNat 7 (GTail 7 1 0 (2 : ℕ)) = 1 :=
  padicValNat_gtail_seven_eq_one (dvd_zero _) (by norm_num)

-- At a zero gap, multiplicativity cannot contribute an extra layer.
example : padicValNat 7 (0 * GTail 7 1 0 (2 : ℕ)) ≠ padicValNat 7 0 + 1 := by
  simp

-- Dropping the endpoint unit allows at least two residual layers.
example : 7 ∣ (7 : ℕ) ∧ 7 ∣ (7 : ℕ) ∧
    49 ∣ GTail 7 1 7 (7 : ℕ) ∧ padicValNat 7 (GTail 7 1 7 (7 : ℕ)) ≠ 1 := by
  have ht0 : GTail 7 1 7 (7 : ℕ) ≠ 0 := by decide
  have hd : 7 ^ 2 ∣ GTail 7 1 7 (7 : ℕ) := by
    decide
  have hv := (DkMath.Lib.NumberTheory.padicValNat_le_iff_dvd
    (by decide : Nat.Prime 7) ht0 2).mpr hd
  exact ⟨dvd_refl _, dvd_refl _, by simpa using hd, by omega⟩

#print axioms padicValNat_gtail_seven_eq_one
#print axioms padicValNat_gap_mul_gtail_seven

end DkMathTest.CosmicFormula.GTailSevenValuation
