/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Cosmic.GTailBoundary

/-!
# Regression checks for the `GTail` boundary gcd surface
-/

namespace DkMathTest.CosmicFormula

open DkMath.CosmicFormula

example (x u : ℕ) :
    Nat.gcd x (GTail 5 2 x u) = Nat.gcd x (Nat.choose 5 2 * u ^ 3) := by
  exact gcd_GTail_eq_gcd_boundary 5 2 x u (by omega)

example (x u : ℕ) (hcop : Nat.Coprime x u) :
    Nat.gcd x (GTail 5 2 x u) = Nat.gcd x (Nat.choose 5 2) := by
  exact gcd_GTail_eq_gcd_choose 5 2 x u (by omega) hcop

example (x u : ℕ) :
    Nat.gcd x (GTail 5 5 x u) = Nat.gcd x (Nat.choose 5 5 * u ^ 0) := by
  exact gcd_GTail_eq_gcd_boundary 5 5 x u (by omega)

end DkMathTest.CosmicFormula
