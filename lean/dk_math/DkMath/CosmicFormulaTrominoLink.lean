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
  -- decide / simp / ext で押し切るのが勝ち筋
  sorry

-- これが通れば、宇宙式 = トロミノ が一撃で出る
theorem cosmic_is_tromino :
  DkMath.Polyomino.area (castShape (body 1 1)) + DkMath.Polyomino.area (castShape (gap 1 1))
    = DkMath.Polyomino.area (castShape (big 1 1)) := by
  -- 左は 3+1、右は 4 に落ちる
  sorry
