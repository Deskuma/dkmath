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

-- 目標：最小例の“形”が一致する（必要なら translate/rotate/reflect まで許す）
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

-- これが通れば、宇宙式 = トロミノ が一撃で出る
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
