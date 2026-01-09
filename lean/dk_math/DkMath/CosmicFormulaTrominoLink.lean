/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib
import DkMath.CosmicFormulaGeom
import DkMath.Tromino

open DkMath.CosmicFormulaGeom

theorem cosmic_diff_int (x u : ℕ) :
    ((x+u : ℤ)^2 - (x : ℤ) * (x + 2*u) ) = (u : ℤ)^2 := by
  -- まず Nat の等式を取り、ℤ に写して整理
  have h : (x+u) * (x+u) = x * (x + 2*u) + u*u :=
    cosmic_area_identity x u
  -- ℤへ
  -- （ここは `zify` / `simp` / `ring` で整える。）
  -- 具体整形は既存宇宙式側の型に合わせて調整するのがよい。
  -- 例としては:
  --   simpa [pow_two] using ...
  ring
