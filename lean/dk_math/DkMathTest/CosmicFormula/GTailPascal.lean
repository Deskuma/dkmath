/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Cosmic.GTailPascal

/-!
# Regression checks for the `GTail` Pascal surface
-/

namespace DkMathTest.CosmicFormula

open scoped BigOperators
open DkMath.CosmicFormula

example (x u : ℕ) :
    GTail 5 1 x u =
      (∑ k ∈ Finset.range 2,
        (Nat.choose 5 (1 + k) : ℕ) * x ^ k * u ^ (5 - (1 + k)))
        + x ^ 2 * GTail 5 3 x u := by
  exact GTail_split_at 5 1 3 x u (by omega) (by omega)

example (x u : ℤ) :
    GTail 7 2 x u =
      (∑ k ∈ Finset.range 5,
        (Nat.choose 7 (2 + k) : ℤ) * x ^ k * u ^ (7 - (2 + k)))
        + x ^ 5 * GTail 7 7 x u := by
  exact GTail_split_at 7 2 7 x u (by omega) (by omega)

end DkMathTest.CosmicFormula
