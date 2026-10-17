/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.Tactic.Group

#print "file: DkMath.Lib.Algebra.OddPowerRecovery"

/-!
# 平方が奇数冪であるときの明示的な冪根

可換群で `u² = v^(2k+1)` なら、`u*v^(-k)` が `u` の `(2k+1)` 乗根。
数体・単元分類・FLT に依存しない、ノルムと位相の解析後の共通操作である。
-/

namespace DkMath.Lib.Algebra

/-- 平方から奇数冪の根を復元する。根を選ぶ存在原理ではなく、積として与える。 -/
theorem oddPower_root_of_square {G : Type*} [CommGroup G] {u v : G} (k : ℕ)
    (h : u ^ 2 = v ^ (2 * k + 1)) :
    (u * v⁻¹ ^ k) ^ (2 * k + 1) = u := by
  calc
    (u * v⁻¹ ^ k) ^ (2 * k + 1) =
        u ^ (2 * k + 1) * ((v ^ (2 * k + 1))⁻¹) ^ k := by
      simp only [mul_pow, inv_pow, ← pow_mul, Nat.mul_comm]
    _ = u := by rw [← h]; group

end DkMath.Lib.Algebra
