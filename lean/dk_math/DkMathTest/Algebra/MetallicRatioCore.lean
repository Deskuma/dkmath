/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Algebra.MetallicRatioCore

#print "file: DkMathTest.Algebra.MetallicRatioCore"

namespace DkMathTest.Algebra.MetallicRatioCore

open DkMath.Algebra.MetallicRatioCore

/-- Complex source values can be observed by their real norms. -/
example (z w : ℂ) :
    (UnitPair.observe norm z w).x = ‖z‖ := by
  rfl

example (z w : ℂ) :
    (UnitPair.observe norm z w).u = ‖w‖ := by
  rfl

example (x u : ℚ) :
    unitAttachedCorePos x u - unitAttachedCoreNeg x u = 4 * x * u := by
  exact unitAttachedCore_sub x u

example (x u : ℝ) :
    unitAttachedCoreNeg x u = 0 ↔ x = u := by
  exact unitAttachedCoreNeg_eq_zero_iff x u

example (p : UnitPair ℝ) (hproduct : p.product = 1) :
    p.big = 4 ↔ p.gap = 0 := by
  exact p.big_eq_four_iff_gap_eq_zero_of_product_eq_one hproduct

example (p : UnitPair ℝ)
    (hx : 0 ≤ p.x) (hu : 0 ≤ p.u)
    (hproduct : p.product = 1)
    (hgap : p.gap = 0) :
    p.x = 1 ∧ p.u = 1 := by
  exact p.eq_one_of_nonneg_of_product_eq_one_of_gap_eq_zero
    hx hu hproduct hgap

end DkMathTest.Algebra.MetallicRatioCore
