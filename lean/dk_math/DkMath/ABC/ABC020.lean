/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/


import DkMath.ABC.ABC019

#print "file: DkMath.ABC.ABC020"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/- Note:
※細分化前にエラー／警告を出さない補題・定理ファイル。
  ABC.lean で定義されるべき定理のうち、ABC.lean 内で定義されていた定理をここに移動している。
-/

namespace DkMath.ABC

open scoped BigOperators

open Nat Real Rat Filter Finset
open MeasureTheory ProbabilityTheory

/-! ### p-adic Valuation Counting Lemmas

For odd primes p, the equation p^k | (2n+1) has exactly one solution modulo p^k
(since 2 is invertible in ℤ/p^kℤ). This gives precise counts for layer-cake sums.
-/


/--
`padic_val_two_of_odd` は、任意の自然数 `n` に対して、`2*n+1` の 2 進 p-進値が 0 であることを示します。
これは、`2*n+1` が奇数であり、2 で割り切れないためです。
証明では、`padicValNat.eq_zero_of_not_dvd` を用いて、2 が `2*n+1` を割り切らないことから結論を導きます。
-/
-- Special case: p = 2, always v_2(2n+1) = 0
lemma padic_val_two_of_odd : ∀ n : ℕ, padicValNat 2 (2*n+1) = 0 := fun n => by
  apply padicValNat.eq_zero_of_not_dvd
  omega

end DkMath.ABC
