/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib
import DkMath.CellDim  -- お主の配置に合わせてパス調整

namespace DkMath
namespace CosmicFormulaCellDim

open scoped BigOperators
open DkMath.CellDim

variable {d : ℕ}

/-- 定数ベクトル（各軸同じ長さ） -/
def constVec (d : ℕ) (n : ℕ) : Fin d → ℕ := fun _ => n

/-- Big: (x+u)^d 個のセル（箱） -/
def Big (d x u : ℕ) : Finset (Cell d) :=
  Box (d := d) (constVec d (x + u))

/-- Gap: u^d 個のセル（箱） -/
def Gap (d u : ℕ) : Finset (Cell d) :=
  Box (d := d) (constVec d u)

@[simp] lemma card_Big (x u : ℕ) :
    (Big (d := d) x u).card = ∏ _i : Fin d, (x + u) := by
  classical
  -- ここは `card_Box_eq_prod` を仕上げると一気に閉じる
  simp [Big, constVec]

@[simp] lemma card_Gap (u : ℕ) :
    (Gap (d := d) u).card = ∏ _i : Fin d, u := by
  classical
  simp [Gap, constVec]

/-
Body と disjoint 分解は次段。

狙い（構造）:
  Big = Body ∪ Gap
  Disjoint Body Gap
  card Big = card Body + card Gap
そして card を (x+u)^d, x*G_{d-1}(x,u), u^d に同定する。

Body を差集合で作るより、
「どの軸が u 以上か」で disjoint な箱の合併として構成するのが実装が強い。
-/

end CosmicFormulaCellDim
end DkMath
