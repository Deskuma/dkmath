/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/


import DkMath.ABC.Rad

#print "file: DkMath.ABC.RadLogBasic"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/- Note:
※ `SliceDiagonalCounting.lean` から切り出した rad-log positivity owner。
-/

namespace DkMath.ABC

open scoped BigOperators

open Nat Real Rat Filter Finset
open MeasureTheory ProbabilityTheory

/-- For any natural number `n`, the real number `rad n` is at least 1. -/
lemma one_le_rad_real (n : ℕ) : (1 : ℝ) ≤ (rad n : ℝ) := by
  classical
  by_cases hn : n = 0
  · subst hn
    simp
  · exact_mod_cast abc_one_le_rad hn

/-- The natural logarithm of the radical of `n` is nonnegative. -/
lemma log_rad_nonneg (n : ℕ) : 0 ≤ Real.log (rad n : ℝ) :=
  Real.log_nonneg (one_le_rad_real n)

/-- The logarithm of the product of the radicals of two natural numbers is nonnegative. -/
lemma log_rad_mul_nonneg (a b : ℕ) : 0 ≤ Real.log (rad a * rad b : ℝ) := by
  classical
  have ha : 0 < rad a := by
    by_cases ha0 : a = 0
    · subst ha0
      simp
    · exact rad_pos (Nat.pos_of_ne_zero ha0)
  have hb : 0 < rad b := by
    by_cases hb0 : b = 0
    · subst hb0
      simp
    · exact rad_pos (Nat.pos_of_ne_zero hb0)
  have hprod : 0 < rad a * rad b := Nat.mul_pos ha hb
  have hge : (1 : ℕ) ≤ rad a * rad b := Nat.succ_le_of_lt hprod
  have hge_real : (1 : ℝ) ≤ (rad a * rad b : ℝ) := by exact_mod_cast hge
  exact Real.log_nonneg hge_real

end DkMath.ABC
