/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: DkMath contributors.
-/

import DkMath.CosmicFormula.Projection.NormalizedGrid

#print "file: DkMathTest.CosmicFormula.ProjectionNormalizedGrid"

namespace DkMathTest.CosmicFormula.ProjectionNormalizedGrid

open DkMath.CosmicFormula.Projection

example :
    (3 : ℝ) / 5 ∈ normalizedGrid 5 := by
  exact mem_normalizedGrid (by norm_num)

example {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ∃ j : ℕ, j ≤ 5 ∧
      |x - (j : ℝ) / 5| ≤ 1 / 5 := by
  exact normalizedGrid_approx (by norm_num) hx0 hx1

example :
    ∃ j : ℕ, j ≤ 4 ∧
      |(3 / 10 : ℝ) - (j : ℝ) / 4| ≤ 1 / 4 := by
  exact normalizedGrid_approx (by norm_num) (by norm_num) (by norm_num)

#print axioms normalizedGrid_approx

end DkMathTest.CosmicFormula.ProjectionNormalizedGrid
