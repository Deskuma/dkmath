/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib
import DkMath.Collatz.Basic
import DkMath.Collatz.V2

#print "file: DkMath.Collatz.Accelerated"

/-!
# Collatz: Accelerated Map

This module provides the implementation of the accelerated Collatz map T(n)
and the observation function s(n). These definitions were previously
axioms in Basic.lean, but are now fully implemented using the 2-adic
valuation v2 from V2.lean.
-/

namespace DkMath.Collatz

/-- Observation function: s(n) = v₂(3n+1) for odd n. -/
noncomputable def s (n : OddNat) : ℕ :=
  v2 (threeNPlusOne n.1)

/-- The accelerated Collatz map on odd naturals.
    T(n) = (3n+1) / 2^(v₂(3n+1))

    This is an OddNat because we divide out all factors of 2.
-/
noncomputable def T (n : OddNat) : OddNat := by
  classical
  let a : ℕ := threeNPlusOne n.1
  let k : ℕ := v2 a
  let t : ℕ := a / pow2 k
  refine ⟨t, ?_⟩
  have ha_pos : 0 < a := by
    -- n.1 is odd, so n.1 ≥ 1
    -- 3*n.1 + 1 ≥ 4
    change 0 < 3 * n.1 + 1
    omega
  have hk_dvd : pow2 k ∣ a := by
    -- padicValNat 2 a is the highest power of 2 dividing a
    simpa [v2, pow2] using (pow_padicValNat_dvd (p := 2) (n := a))
  have hk1_not_dvd : ¬ pow2 (k+1) ∣ a := by
    -- 2^(v2 a + 1) does not divide a
    simpa [v2, pow2] using (pow_succ_padicValNat_not_dvd ha_pos.ne')
  have ha_eq : a = pow2 k * t := by
    simpa [t] using (Nat.mul_div_cancel' hk_dvd).symm
  have ht_odd : t % 2 = 1 := by
    have ht_cases : t % 2 = 0 ∨ t % 2 = 1 := by
      exact Nat.mod_two_eq_zero_or_one t
    cases ht_cases with
    | inr ht1 => exact ht1
    | inl ht0 =>
        have ht_dvd : 2 ∣ t := Nat.dvd_iff_mod_eq_zero.mpr ht0
        have h_t_peel : t = 2 * (t/2) := by
          exact (Nat.mul_div_cancel' ht_dvd).symm
        have hk1_dvd : pow2 (k+1) ∣ a := by
          refine ⟨t/2, ?_⟩
          rw [ha_eq, h_t_peel]
          unfold pow2
          simp [Nat.pow_succ]
          ring
        exact (hk1_not_dvd hk1_dvd).elim
  simpa [t] using ht_odd

/-- Iterated application of T. -/
noncomputable def iterateT : ℕ → OddNat → OddNat
| 0, n => n
| m+1, n => iterateT m (T n)

/-- The partial sum of the observation sequence over m steps.
    S_m(n) := ∑_{i=0}^{m-1} s(T^i(n))
-/
noncomputable def sumS : OddNat → ℕ → ℕ
| _, 0 => 0
| n, m+1 => sumS n m + s (iterateT m n)

/-- The drift at step m.
    D_m(n) := m·log₂(3) - S_m(n)
-/
noncomputable def driftReal : OddNat → ℕ → ℝ := fun n m =>
  (m : ℝ) * (Real.log 3 / Real.log 2) - (sumS n m : ℝ)

end DkMath.Collatz

/- Note:
Completed: *Accelerated.lean を作成し、T と s を実装する* (2/3)

うむ、やり遂げたぞ！
循環 import を解消し、ついに `T`（加速コラッツ写像）と `s`（観測量）を **完全な定義（def）** として実装し終えた。

これで Basic.lean の「形式化の抜け穴（axiom）」は完全に塞がった。ぬしの城は、もはや仮初めの木門ではなく、揺るぎない石造りの門を手に入れたわけじゃな。

## やったこと
1. **Basic.lean**：
   * `axiom T`, `s` を削除し、`iterateT`, `sumS`, `driftReal` を移動させた。
   * これにより、このファイルは `v2` に依存せず、他のファイルから安全に import できる基礎となった。
2. **Accelerated.lean** (新規作成)：
   * `v2` を用いて、`T(n) = (3n+1) / 2^(v2(3n+1))` を厳密に実装。
   * 「$T(n)$ は常に奇数である」という性質を、`pow_padicValNat_dvd`（最大性）を用いて証明し、`OddNat` 型の整合性を保った。
3. **[Collatz2K26.lean](lean/dk_math/DkMath/Collatz/Collatz2K26.lean)**：
   * `Accelerated.lean` を import に加え、プロジェクト全体の統合を再構築した。

## 成果
`lake build` が警告なし（スタイル警告を除く）で通り、定義がすべて Mathlib と矛盾なく繋がった。
これで「観測量 $v_2$」を中心にしたコラッツ予想の解析が、完全に数学的な土台の上で動かせるようになった。

どうじゃ？ 公理なしで自分の理論が立ち上がるのは、実に清々しい気分ではないかえ？
次はこの $T$ や $s$ を使って、さらなる「花弁の不変性」や「ドリフト統計」の形式化に興じるとしようかの！

Made changes.
-/
