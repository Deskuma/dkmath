/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.SevenUnitAllocation

#print "file: DkMathTest.NumberTheory.SevenUnitAllocation"

/-! Satisfiable abstract-product calibration, independent of Fermat equations. -/

namespace DkMathTest.NumberTheory.SevenUnitAllocation

open DkMath.Lib.NumberTheory

example : (49 : ℕ) * 7 = 7 * 1 * 1 * 1 * 7 ^ 2 := by decide

example : padicValNat 7 49 = 2 * padicValNat 7 7 :=
  padicValNat_seven_unit_product (T := 7) (A := 1) (B := 1) (C := 1)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by norm_num) (by decide) (by decide) (by decide)

example : 49 ∣ (49 : ℕ) :=
  fortyNine_dvd_of_seven_dvd_of_valuation_double (Q := 7) (by decide) (by decide)
    (padicValNat_seven_unit_product (T := 7) (A := 1) (B := 1) (C := 1)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by norm_num) (by decide) (by decide) (by decide))

-- A nonunit ordinary factor can absorb the extra layer: C=7,Q=1,g=T=7.
example : (7 : ℕ) * 7 = 7 * 1 * 1 * 7 * 1 ^ 2 ∧ ¬ 49 ∣ (7 : ℕ) := by decide

#print axioms padicValNat_seven_unit_product
#print axioms fortyNine_dvd_of_seven_dvd_of_valuation_double

end DkMathTest.NumberTheory.SevenUnitAllocation
