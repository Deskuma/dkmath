/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib
import DkMath.UnitCycle.Core

#print "file: DkMath.UnitCycle.Examples"

namespace DkMath.UnitCycle

/-! # Examples

このファイルは、`Core.lean` の抽象定理が
- **どこまで刺さるか**（u>0 / 不等式増分）
- **どこから刺さらないか**（u=0 / 周期写像）

を、最小の例で確認するためのサンプル集。
-/

/-- 最小の State の例：`val : ℕ` を持つ。 -/
structure State where
  val : ℕ
  deriving Repr, Inhabited

/-- 周回遷移：値を 1 増やす。 -/
def T (s : State) : State := { val := s.val + 1 }

/-- 不変量：`I s = s.val` とする。 -/
def I (s : State) : ℕ := s.val

/-! ## 1) u > 0 系：閉路は潰れる -/

section PositiveIncrement

/-- 周回遷移：値を 1 増やす。 -/
def T1 (s : State) : State := { val := s.val + 1 }

theorem I_T1 (s : State) : I (T1 s) = I s + 1 := by
  simp [I, T1]

/-- `u = 1`：閉路が存在しない。 -/
theorem no_cycle_u1 (k : ℕ) (s : State) (h : iterate T1 k s = s) : k = 0 :=
  no_nontrivial_cycle_unit (State := State) (T := T1) (I := I) (fun s => I_T1 s) k s h

/-- 周回遷移：値を 2 増やす。 -/
def T2 (s : State) : State := { val := s.val + 2 }

/-- `I (T2 s) = I s + 2` -/
theorem I_T2 (s : State) : I (T2 s) = I s + 2 := by
  simp [I, T2]

/-- `u = 2`：閉路が存在しない（一般定理）。 -/
theorem no_cycle_u2 (k : ℕ) (s : State) (h : iterate T2 k s = s) : k = 0 := by
  exact no_nontrivial_cycle_of_pos_u (State := State) (T := T2) (I := I)
    2 (fun s => I_T2 s) (by decide) k s h

end PositiveIncrement

/-! ## 2) 不等式増分：増分一定でなくても閉路は潰れる -/

section GeOneIncrement

/-- 例：条件を弱めて `I (T s) ≥ I s + 1` だけ仮定する（ここでは等号で成立）。 -/
def Tge (s : State) : State := { val := s.val + 1 }

theorem I_Tge_ge (s : State) : I (Tge s) ≥ I s + 1 := by
  -- 等号で成立
  simp [I, Tge]

/-- 不等式版定理で閉路が存在しないことを示す。 -/
theorem no_cycle_ge_one (k : ℕ) (s : State) (h : iterate Tge k s = s) : k = 0 :=
  no_nontrivial_cycle_of_ge_one (State := State) (T := Tge) (I := I) (fun s => I_Tge_ge s) k s h

end GeOneIncrement

/-! ## 3) 境界：u = 0 なら閉路は普通に存在する -/

section ZeroIncrement

/-- 恒等写像：単位増分 u = 0 の極限モデル。
    この場合は任意の k で閉路になる（非自明閉路が存在する）。 -/
def T0 (s : State) : State := s

/-- 不変量：`I s = s.val` とする。(u = 0) -/
theorem I_T0 (s : State) : I (T0 s) = I s + 0 := by simp [I, T0, add_zero]

/-- 恒等変換の反復は常に元に戻る。 -/
theorem iterate_T0 (k : ℕ) (s : State) : iterate T0 k s = s := by
  induction k with
  | zero => simp [iterate]
  | succ k ih => simp [iterate, T0, ih]

/-- 恒等変換には非自明な閉路が存在する。 -/
theorem identity_has_nontrivial_cycle :
  ∃ (k : ℕ) (s : State), k ≠ 0 ∧ iterate T0 k s = s := by
  use 1, default
  constructor
  · decide
  · simp [iterate, T0]

/-- 非自明閉路の例：k=3 でも元に戻る。 -/
example (s : State) : iterate T0 3 s = s := by
  simpa using iterate_T0 3 s


end ZeroIncrement

/-! ## 4) 境界：周期写像は閉路を持つ（増分不変量が無い例） -/

section SwapCycle

/-- 2状態（Bool）のスワップ：`not` は 2 回で元に戻る。 -/
def Tswap (b : Bool) : Bool := !b

example : iterate Tswap 2 true = true := by
  simp [iterate, Tswap]

example : iterate Tswap 1 true = false := by
  simp [iterate, Tswap]

end SwapCycle

end DkMath.UnitCycle
