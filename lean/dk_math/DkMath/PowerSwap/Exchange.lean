/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

-- PowerSwap module: Exchange conditions and minimal exchange theorems

import Mathlib

namespace DkMath
namespace PowerSwap

/-! ## Exchange: 粗視化 ↔ 微視化の最小交換則 -/

/--
`A = a^t` なら、任意の `m` で `A^m = a^(t*m)`（`ℕ` 版）。
-/
theorem exchange_condition_minimal_nat
    (a A t m : ℕ) (hA : A = a ^ t) :
    A ^ m = a ^ (t * m) := by
  simp [hA, pow_mul]

/--
`A = a^t` なら、任意の `m` で `A^m = a^(t*m)`（`ℤ` 版）。
-/
theorem exchange_condition_minimal_int
    (a A : ℤ) (t m : ℕ) (hA : A = a ^ t) :
    A ^ m = a ^ (t * m) := by
  simp [hA, pow_mul]

/-! ## 交換則の具体例 -/

theorem exchange_example_4_2_eq_2_4 :
    (4 : ℕ) ^ 2 = 2 ^ 4 := by
  have hA : (4 : ℕ) = 2 ^ 2 := by norm_num
  calc
    (4 : ℕ) ^ 2 = 2 ^ (2 * 2) := exchange_condition_minimal_nat 2 4 2 2 hA
    _ = 2 ^ 4 := by norm_num

theorem exchange_example_8_2_eq_2_6 :
    (8 : ℕ) ^ 2 = 2 ^ 6 := by
  have hA : (8 : ℕ) = 2 ^ 3 := by norm_num
  calc
    (8 : ℕ) ^ 2 = 2 ^ (3 * 2) := exchange_condition_minimal_nat 2 8 3 2 hA
    _ = 2 ^ 6 := by norm_num

theorem exchange_example_9_2_eq_3_4 :
    (9 : ℕ) ^ 2 = 3 ^ 4 := by
  have hA : (9 : ℕ) = 3 ^ 2 := by norm_num
  calc
    (9 : ℕ) ^ 2 = 3 ^ (2 * 2) := exchange_condition_minimal_nat 3 9 2 2 hA
    _ = 3 ^ 4 := by norm_num

theorem exchange_example_27_2_eq_3_6 :
    (27 : ℕ) ^ 2 = 3 ^ 6 := by
  have hA : (27 : ℕ) = 3 ^ 3 := by norm_num
  calc
    (27 : ℕ) ^ 2 = 3 ^ (3 * 2) := exchange_condition_minimal_nat 3 27 3 2 hA
    _ = 3 ^ 6 := by norm_num

end PowerSwap
end DkMath
