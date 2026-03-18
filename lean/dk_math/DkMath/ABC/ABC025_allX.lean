/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.ABC025

#print "file: DkMath.ABC.ABC025_allX"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

namespace ABC

namespace Telescoping

open scoped BigOperators

open Nat Real Rat Filter Finset
open MeasureTheory ProbabilityTheory

variable {p : ℕ}

/-!
## 全 X で `2(X+1)` を取るには

このファイルでは、`ABC025` の既存補題を再利用しつつ、
「X ≥ 11 の場合」と「X < 11 の場合」を分岐して 2(X+1) を示す構造を用意する。

完全証明は手数が多いため、現状では構造のみを整え、
証明の本体には `sorry` を置いておく。

目的:
- `sum_pow_padicValNat_le_geom_two_for_large_X` を再利用
- small X の場合を補完する枠を用意
- 最終的に `ABC026` に import させることで、import チェーンに挟み込む
- 完全証明は別途埋める
-/

/--
全ての X ≥ 1 について `∑_{n=0}^X p^{t·v(n)} ≤ 2(X+1)` を主張するテンプレート。

こちらは「大きいX 用の補題 + 小さいX 用の数値評価」を組み合わせる構造を示す。
証明の本体は `sorry` で置いてある。
-/
lemma sum_pow_padicValNat_le_geom_two_all_X {p : ℕ} [hp : Fact p.Prime]
    (hp3 : p ≥ 3) {t : ℝ} (ht : 0 < t) (ht_half : t ≤ 1 / 2) {X : ℕ} (hX : X ≥ 1) :
    ∑ n ∈ Finset.Icc 0 X, (p : ℝ) ^ (t * (padicValNat p (2 * n + 1) : ℤ)) ≤
      2 * (X + 1) := by
  classical
  by_cases hXge11 : X ≥ 11
  · -- X ≥ 11 のときは既存補題で対応
    exact sum_pow_padicValNat_le_geom_two_for_large_X hp3 ht ht_half hXge11
  · -- X < 11 のときは、個別評価でカバーする
    have hXle10 : X ≤ 10 := by linarith
    -- TODO: small-X の個別評価をここに書く
    -- 例: X = 1, 2, ..., 10 のそれぞれについて、
    --  (p,t) の最大悪条件を検証して `2*(X+1)` 以内に収まることを証明する。
    -- 現状は構造のみを示すため `sorry` とする。
    sorry

end Telescoping

end ABC
