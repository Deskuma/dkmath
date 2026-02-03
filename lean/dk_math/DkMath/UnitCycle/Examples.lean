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

/-! ## 5) 状態依存増分：g(s) = 1 + s.val（常に ≥1） -/

section StateDependent

def g (s : State) : ℕ := 1 + s.val

def Tg (s : State) : State := { val := s.val + g s }

lemma hg : ∀ s : State, 1 ≤ g s := by
  intro s
  simp [g]

lemma hTg : ∀ s : State, I (Tg s) ≥ I s + g s := by
  intro s
  simp [Tg, I, g]

/-- 状態依存増分が ≥1 の場合にも閉路は存在しない。 -/
theorem no_cycle_tg (k : ℕ) (s : State) (h : iterate Tg k s = s) : k = 0 :=
  no_nontrivial_cycle_of_ge_g (State := State) (T := Tg) (I := I) (g := g) hg hTg k s h

end StateDependent

/-! ## (B) 増分が局所的に大きい例（周期ごとにスパイク） -/
section LocalSpike

/-- 局所スパイク：10 の倍数のとき 5 それ以外は 1 -/
def g_spike (s : State) : ℕ := if s.val % 10 = 0 then 5 else 1

def T_spike (s : State) : State := { val := s.val + g_spike s }

lemma hg_spike : ∀ s : State, 1 ≤ g_spike s := by
  intro s
  dsimp [g_spike]
  split_ifs with h
  · decide
  · decide

lemma hT_spike : ∀ s : State, I (T_spike s) ≥ I s + g_spike s := by
  intro s; simp [T_spike, I, g_spike]

/-- 局所スパイクでも閉路は存在しない（≥1 が満たされれば一般定理で排除）。 -/
theorem no_cycle_spike (k : ℕ) (s : State) (h : iterate T_spike k s = s) : k = 0 :=
  no_nontrivial_cycle_of_ge_g
  (State := State) (T := T_spike) (I := I) (g := g_spike) hg_spike hT_spike k s h

end LocalSpike

/-! ## RelPolygon 最小モデル（相対多角数の試し刺し） -/
section RelPolygon

/-- 最小モデルの状態：周回位置 pos と蓄積 val を持つ。 -/
structure RState where
  pos : ℕ
  val : ℕ
  deriving Repr, Inhabited

/-- 局所スパイク：pos が 10 の倍数のとき 5, それ以外は 1 -/
def g_rel (s : RState) : ℕ := if s.pos % 10 = 0 then 5 else 1

/-- 周回写像：位置を 1 進め、ギャップを val に加算する。 -/
def T_rel (s : RState) : RState := { pos := s.pos + 1, val := s.val + g_rel s }

/-- 不変量は蓄積 val を取る。 -/
def I_rel (s : RState) : ℕ := s.val

lemma hg_rel : ∀ s : RState, 1 ≤ g_rel s := by
  intro s
  dsimp [g_rel]
  split_ifs with h
  · decide
  · decide

lemma hT_rel : ∀ s : RState, I_rel (T_rel s) ≥ I_rel s + g_rel s := by
  intro s; simp [I_rel, T_rel, g_rel]

/-- 総和版をそのまま適用する定理（単純な alias）。 -/
theorem rel_sum_lower (k : ℕ) (s : RState) :
  I_rel (iterate T_rel k s)
≥ I_rel s + Finset.sum (Finset.range k) fun i => g_rel (iterate T_rel i s) :=
  I_iterate_ge_sum_g (T := T_rel) (I := I_rel) (g := g_rel) hT_rel k s

-- s9 = pos=9,val=0, 2 ステップでの累積を直接計算して見せる（Finset の展開に依存しない実証）
def s9 : RState := { pos := 9, val := 0 }

lemma rel_example_k2_eq : I_rel (iterate T_rel 2 s9) = 6 := by
  have hI : ∀ s, I_rel (T_rel s) = I_rel s + g_rel s := by intro s; simp [I_rel, T_rel, g_rel]
  have H : I_rel (iterate T_rel 2 s9) = I_rel (T_rel (T_rel s9)) := by simp [iterate]
  rw [H]
  rw [hI (T_rel s9)]
  rw [hI s9]
  have h0 : I_rel s9 = 0 := by simp [I_rel, s9]
  have h1 : g_rel s9 = 1 := by simp [g_rel, s9]
  have h2 : g_rel (T_rel s9) = 5 := by simp [g_rel, T_rel, s9]
  simp [h0, h1, h2]

/-- 例の可視化：2 ステップで少なくとも 6 以上増える。 -/
theorem rel_example_k2 : I_rel (iterate T_rel 2 s9) ≥ 6 := by
  apply Nat.le_of_eq
  exact rel_example_k2_eq

end RelPolygon

/-! ## 6) 厳密増分の例：T1 は I を厳密増加させる -/

section Strict

lemma strict_T1 : ∀ s : State, I (T1 s) > I s := by
  intro s
  have : I (T1 s) = I s + 1 := by simp [T1, I]
  rw [this]
  -- I s < I s + 1
  exact Nat.lt_add_of_pos_right (Nat.succ_pos 0)

/-- 厳密増分から閉路を排除できる。 -/
theorem no_cycle_strict (k : ℕ) (s : State) (h : iterate T1 k s = s) : k = 0 :=
  no_nontrivial_cycle_of_strict (State := State) (T := T1) (I := I) strict_T1 k s h

end Strict

end DkMath.UnitCycle
