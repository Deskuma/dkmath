/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib

namespace DkMath.ABC

/--
補助補題：v_p(n) の分解
`padicValNat_split` は、p-進値 `padicValNat p n` を 1 以下の最小値と 1 を引いた値の最大値の和に分解する補助補題です。
具体的には、`padicValNat p n` が 0 の場合は 0 に等しくなり、1 の場合は 1 に等しくなり、それ以外の場合はそれらの和に等しくなります。
-/
lemma padicValNat_split (p n : ℕ) :
    padicValNat p n = min (padicValNat p n) 1 + max (padicValNat p n - 1) 0 := by
  by_cases h : padicValNat p n = 0
  · simp [h]
  · by_cases h1 : padicValNat p n = 1
    · simp [h1]
    · have : padicValNat p n ≥ 2 := by omega
      have : min (padicValNat p n) 1 = 1 := by omega
      have : max (padicValNat p n - 1) 0 = padicValNat p n - 1 := by omega
      omega


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

/--
`padic_val_two_of_even` は、任意の自然数 `n` に対して、`2*n` の 2 進 p-進値に関する性質を示します。
具体的には、`n = 0` の場合、`padicValNat 2 (2*n) = 0` かつ `1 + padicValNat 2 n = 1` が成り立ち、
`n ≠ 0` の場合、`padicValNat 2 (2*n) = 1 + padicValNat 2 n` が成り立ちます。
証明では、`n = 0` の場合と `n ≠ 0` の場合に分けて議論し、それぞれのケースで `padicValNat.mul` の性質を利用して結論を導きます。
-/
lemma padic_val_two_of_even (n : ℕ) :
    (n = 0 → padicValNat 2 (2 * n) = 0 ∧ 1 + padicValNat 2 n = 1) ∧
    (n ≠ 0 → padicValNat 2 (2 * n) = 1 + padicValNat 2 n) := by
  constructor
  · intro h
    rw [h, Nat.mul_zero, padicValNat.zero, Nat.add_zero]
    exact ⟨rfl, rfl⟩
  · intro h
    have hn : 0 < n := Nat.pos_of_ne_zero h
    have h2n : 2 * n ≠ 0 := Nat.mul_ne_zero (by norm_num) h
    rw [padicValNat.mul (by norm_num) h]
    simp

end DkMath.ABC
