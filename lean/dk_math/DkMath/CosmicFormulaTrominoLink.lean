/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib
import DkMath.CosmicFormulaGeom
import DkMath.Tromino

open DkMath.CosmicFormulaGeom
open DkMath.Polyomino.Tromino

theorem cosmic_diff_int (x u : ℕ) :
    ((x+u : ℤ)^2 - (x : ℤ) * (x + 2*u) ) = (u : ℤ)^2 := by
  -- まず Nat の等式を取り、ℤ に写して整理
  have h : (x+u) * (x+u) = x * (x + 2*u) + u*u :=
    cosmic_area_identity x u
  -- ℤへ：等式全体を ℤ へ写す
  have hZ := congrArg (fun n : ℕ => (n : ℤ)) h
  norm_cast at hZ
  simpa [pow_two, sub_eq_iff_eq_add, add_comm] using hZ

-- 宇宙式とトロミノの橋渡し

/-- ℕ×ℕ → ℤ×ℤ の埋め込み -/
def castCell : (ℕ × ℕ) → (ℤ × ℤ) := fun p => (p.1, p.2)

/-- 図形の写像 -/
def castShape (S : DkMath.CosmicFormulaGeom.Shape) : DkMath.Polyomino.Shape :=
  S.image castCell

/--
`bridge_tromino_min` は、特定の形状の有限集合に関する定理です。
この定理は、以下の3つの形状が等しいことを示します：

1. `castShape (body 1 1)` は `L_tromino` に等しい。
2. `castShape (gap 1 1)` は `hole2` に等しい。
3. `castShape (big 1 1)` は `block2` に等しい。

この証明では、`castShape` 関数が `Finset.image` による単純な埋め込みであることを利用し、
各集合の要素を展開して、`castCell` の作用を計算することで、両辺が同じ有限集合であることを示します。

証明のテクニックとして、`decide` を用いて有限集合の等式を解くか、
`ext` を使用して要素ごとの所属判定を確認します。
-/
theorem bridge_tromino_min :
  castShape (body 1 1) = L_tromino ∧
  castShape (gap 1 1)  = hole2 ∧
  castShape (big 1 1)  = block2 := by
  -- body 1 1, gap 1 1, big 1 1 はすべて具体的な有限集合の構成であり、
  -- castShape は Finset.image による単純な埋め込み。
  -- 各セットの要素を展開し、castCell の作用を計算することで
  -- 両辺が同じ有限集合となることを示す。

  -- テクニック：decide を用いて有限集合の等式を解く
  -- または ext で要素ごとの所属判定を確認する
  constructor
  · -- castShape (body 1 1) = L_tromino
    -- 両辺を決定可能な有限集合として比較
    decide
  constructor
  · -- castShape (gap 1 1) = hole2
    decide
  · -- castShape (big 1 1) = block2
    decide

/--
この定理 `cosmic_is_tromino` は、特定のポリオミノの面積に関する関係を示しています。
具体的には、以下の等式を証明します：

\[
\text{area}(\text{castShape}(\text{body}(1, 1))) +
\text{area}(\text{castShape}(\text{gap}(1, 1))) =
\text{area}(\text{castShape}(\text{big}(1, 1)))
\]

ここで、`body`、`gap`、および `big` はそれぞれ異なる形状を表し、`castShape` はそれらの形状をポリオミノに変換します。
証明の過程では、`bridge_tromino_min` を用いて具体的な形状に置き換えた後、面積の計算を行います。
最終的に、トロミノの面積が 3、穴の面積が 1、ブロックの面積が 4 であることを示し、これにより等式が成り立つことを確認します。
-/
theorem cosmic_is_tromino :
  DkMath.Polyomino.area (castShape (body 1 1)) + DkMath.Polyomino.area (castShape (gap 1 1))
    = DkMath.Polyomino.area (castShape (big 1 1)) := by
  -- bridge_tromino_min を使って、castShape を具体的な形に置き換える
  rw [bridge_tromino_min.1, bridge_tromino_min.2.1, bridge_tromino_min.2.2]
  -- その後、面積計算：
  -- area L_tromino = 3
  -- area hole2 = 1
  -- area block2 = 4
  -- → 3 + 1 = 4
  simp only [DkMath.Polyomino.Tromino.area_L_tromino,
             DkMath.Polyomino.Tromino.area_hole2,
             DkMath.Polyomino.Tromino.area_block2]
