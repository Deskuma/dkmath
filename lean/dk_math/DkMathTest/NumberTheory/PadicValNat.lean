/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.PadicValNat
import DkMath.ABC.PadicValNat

/-!
# Regression checks for the lower `padicValNat` provider
-/

namespace DkMathTest.NumberTheory.PadicValNat

example (hp : Nat.Prime 3) :
    padicValNat 3 (6 ^ 5) = 5 * padicValNat 3 6 := by
  exact DkMath.Lib.NumberTheory.padicValNat_pow hp 5 (by norm_num)

example (hp : Nat.Prime 3) :
    padicValNat 3 (6 ^ 5) = 5 * padicValNat 3 6 := by
  exact DkMath.ABC.padicValNat_pow hp 5 (by norm_num)

example (hp : Nat.Prime 3) (hn : (6 : ℕ) ≠ 0) :
    2 ≤ padicValNat 3 6 ↔ 3 ^ 2 ∣ 6 := by
  exact DkMath.Lib.NumberTheory.padicValNat_le_iff_dvd hp hn 2

end DkMathTest.NumberTheory.PadicValNat
