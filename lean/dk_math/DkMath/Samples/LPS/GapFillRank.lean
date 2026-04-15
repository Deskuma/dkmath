/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

-- LPS module: Lander, Parkin, and Selfridge conjecture research

import Mathlib

#print "file: DkMath.Samples.LPS.GapFillRank"

open scoped BigOperators

namespace DkMath
namespace Samples

/-!
## Gap Fillability と FillRank

`n` が `d` 次冪の和で埋まるか、という問題を扱う。

最初はマルチセット・重複版で定義する。
(Finset 版は後の refine で試す)

与えられた r 個の数値 `f : Fin r → ℕ` に対して、
   ∑ i : Fin r, (f i)^d = n
が成り立つかどうかを問う。
-/

/-- `n` is fillable by exactly `r` many `d`-th powers. -/
def FillableByPowSumExact (d n r : ℕ) : Prop :=
  ∃ f : Fin r → ℕ, (∑ i : Fin r, (f i) ^ d) = n

/-- `n` is fillable by at most `r` many `d`-th powers. -/
def FillableByPowSumLE (d n r : ℕ) : Prop :=
  ∃ k ≤ r, FillableByPowSumExact d n k

/-!
## 基本的な充填可能性の例

### 平方数の例 -/

/-- `16 = 4^2` は 1 個の 2 乗で埋まる。 -/
theorem fillable_sq_16_exact_one : FillableByPowSumExact 2 16 1 := by
  refine ⟨fun _ => 4, ?_⟩
  simp

/--
`25 = 3^2 + 4^2` は 2 個の 2 乗で埋まる。

この例では `Fin 2 → ℕ` で [3, 4] を与える。
-/
theorem fillable_sq_25_exact_two : FillableByPowSumExact 2 25 2 := by
  refine ⟨![3, 4], ?_⟩
  norm_num

/-! ### 立方数の例 -/

/-- `216 = 6^3` は 1 個の 3 乗で埋まる。 -/
theorem fillable_cube_216_exact_one :
    FillableByPowSumExact 3 216 1 := by
  refine ⟨fun _ => 6, ?_⟩
  simp

/--
`216 = 3^3 + 4^3 + 5^3` は 3 個の 3 乗で埋まる。

Ramanujan-Hardy number の背景にある性質。
実際には `216 = 6^3` でもあるが、複数の分解が存在することが重要。
-/
theorem fillable_cube_216_exact_three :
    FillableByPowSumExact 3 216 3 := by
  refine ⟨![3, 4, 5], ?_⟩
  decide

/--
`3^3 + 4^3 + 5^3 = 6^3` の検証。

この例は、同じ値が異なる冪和分解を持つことを示す。
-/
example : 3^3 + 4^3 + 5^3 = 6^3 := by
  norm_num

/-!
## Filling のほうむ関係

より強い性質として、Big と Body の関係を Filling で表す試み。

例えば、
  Big d x u = Core d x u + Beam d x u + Gap d x u
という Big-family 分解が成り立つ時に、
**Beam と Gap をあわせて単一の d-乗和で埋める** ことができるか、
という問題に進むことができる。

ここではスケルトン版を置く。
-/

/--
`Big` と `Body` の差が `d` 次冪和で埋まるか、という述語。

この差は residual と呼ばれ、いくつの `d` 乗項の和で表されるかを問う。
-/
def ResidualFillableExact (d big body r : ℕ) : Prop :=
  big ≥ body ∧ FillableByPowSumExact d (big - body) r

/-! ## 充填可能性の連鎖 -/

/--
`0` は(空和として)任意の `d` で埋まる。
-/
theorem fillable_zero_exact_zero (d : ℕ) :
    FillableByPowSumExact d 0 0 := by
  refine ⟨fun _ => 0, ?_⟩
  simp

/--
`n` が `k` 個で埋まるなら、`k ≤ r` な任意の `r` でも埋まる（追加の 0 項を入れる）。
-/
theorem fillable_exact_of_exact_le {d n k r : ℕ}
    (h : FillableByPowSumExact d n k) (hle : k ≤ r) (hd : 0 < d) :
    FillableByPowSumExact d n r := by
  rcases h with ⟨f, hf⟩
  rcases Nat.exists_eq_add_of_le hle with ⟨t, rfl⟩
  refine ⟨Fin.append f (fun _ : Fin t => 0), ?_⟩
  rw [Fin.sum_univ_add]
  simp [hf, hd]

/--
`FillableByPowSumExact` が存在するなら `FillableByPowSumLE` も成り立つ。
-/
theorem fillable_le_of_exact {d n r : ℕ}
    (h : FillableByPowSumExact d n r) :
    FillableByPowSumLE d n r := by
  exact ⟨r, le_refl r, h⟩

end Samples
end DkMath

/- Note:
命題は次の2つで別です。

- `Exact k -> Exact r`（`k ≤ r` で項数を増やす）
- `Exact r -> LE r`（「ちょうど r 個」から「高々 r 個」へ落とす）

識別名を整理して修正しました。

- `fillable_le_of_exact` → `fillable_exact_of_exact_le`
- `fillableLE_of_exact` → `fillable_le_of_exact`
-/
