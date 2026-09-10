/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Cosmic.GTailCongruence

/-!
# Regression checks for the prime-row `GTail` congruence surface
-/

namespace DkMathTest.CosmicFormula

open DkMath.CosmicFormula

example (x u : ℕ) (hp : Nat.Prime 5) (hpx : 5 ∣ x) :
    GTail 5 2 x u ≡ Nat.choose 5 2 * u ^ 3 [MOD 5 ^ 2] := by
  exact GTail_modEq_head_mod_sq_of_prime_dvd_x x u hp (by omega) (by omega) hpx

example (x u : ℕ) (hp : Nat.Prime 5) (hpx : 5 ∣ x) :
    GTail 5 1 x u ≡ Nat.choose 5 1 * u ^ 4 [MOD 5 ^ 2] := by
  exact GTail_modEq_head_mod_sq_of_prime_dvd_x x u hp (by omega) (by omega) hpx

example (x u : ℕ) (hp : Nat.Prime 5) (hpx : 5 ∣ x) :
    GTail 5 1 x u ≡ 5 * u ^ 4 [MOD 5 ^ 2] := by
  exact GN_modEq_head_mod_sq_of_prime_dvd_x x u hp (by omega) hpx

end DkMathTest.CosmicFormula
