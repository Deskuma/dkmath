/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PrimitiveSet.RealWeightedPath

#print "file: DkMath.NumberTheory.PrimitiveSet.RealLog"

namespace DkMath.NumberTheory.PrimitiveSet

/--
Natural-number log nonnegativity for the numerator side of the real/log route.

The boundary case `p = 1` is allowed: it gives `Real.log 1 = 0`.
-/
theorem real_log_nat_nonneg_of_one_le
    {p : ℕ} (hp : 1 ≤ p) :
    0 ≤ Real.log (p : ℝ) := by
  exact Real.log_nonneg (by exact_mod_cast hp)

/--
Natural-number log positivity for the denominator side of the real/log route.

This strict form is the one needed before dividing by `Real.log (n : ℝ)`.
-/
theorem real_log_nat_pos_of_one_lt
    {n : ℕ} (hn : 1 < n) :
    0 < Real.log (n : ℝ) := by
  exact Real.log_pos (by exact_mod_cast hn)

end DkMath.NumberTheory.PrimitiveSet
