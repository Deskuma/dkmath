/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib
import DkMath.UnitCycle.Core

#print "file: DkMath.UnitCycle.Examples"

namespace DkMath.UnitCycle

/-- 最小の State の例。`val : ℕ` を持つ。 -/
structure State where
  val : ℕ
  deriving Repr, Inhabited

/-- 周回遷移：値を 1 増やす。 -/
def T (s : State) : State := { val := s.val + 1 }

/-- 不変量：`I s = s.val` とする。 -/
def I (s : State) : ℕ := s.val

/-- 値を 1 増やす遷移の例（u = 1）。コア定理を適用できる。 -/
theorem I_T (s : State) : I (T s) = I s + 1 := by simp [I, T]

/-- コア定理を適用して、この具体例に非自明な閉路は存在しないことを示す。 -/
theorem no_cycle_examples (k : ℕ) (s : State) (h : iterate T k s = s) : k = 0 :=
  no_nontrivial_cycle_unit (fun s => I_T s) k s h

/-- 値を 2 増やす遷移の例（u = 2）。一般定理を適用できる。 -/
def T2 (s : State) : State := { val := s.val + 2 }

/-- 不変量：`I s = s.val` とする。(u = 2) -/
theorem I_T2 (s : State) : I (T2 s) = I s + 2 := by simp [I, T2]

/-- コア定理を適用して、この具体例に非自明な閉路は存在しないことを示す。 -/
theorem no_cycle_examples_u2 (k : ℕ) (s : State) (h : iterate T2 k s = s) : k = 0 :=
  no_nontrivial_cycle_of_pos_u 2 (fun s => I_T2 s) (by decide) k s h

/-- 恒等変換（u = 0）の例：この場合は任意の k で閉路になる（非自明閉路が存在する）。 -/
def T0 (s : State) : State := s

/-- 不変量：`I s = s.val` とする。(u = 0) -/
theorem I_T0 (s : State) : I (T0 s) = I s + 0 := by simp [I, T0, add_zero]

/-- 恒等変換の反復は常に元に戻る。 -/
theorem iterate_T0 (k : ℕ) (s : State) : iterate T0 k s = s := by
  induction k generalizing s
  case zero => simp [iterate]
  case succ k ih =>
    calc
      iterate T0 (k + 1) s = iterate T0 k (T0 s) := by simp [iterate]
      _ = T0 s := by exact ih (T0 s)
      _ = s := by rfl

/-- 恒等変換には非自明な閉路が存在する。 -/
theorem identity_has_nontrivial_cycle :
  ∃ (k : ℕ) (s : State), k ≠ 0 ∧ iterate T0 k s = s := by
  use 1, default
  constructor
  · decide
  · simp [iterate, T0]

/-- 2 要素の巡回（スワップ）例。2 回で元に戻るため k = 2 の非自明閉路がある。 -/
structure State2 where v : Bool deriving Repr, Inhabited

/-- スワップ遷移。 -/
def Tswap (s : State2) : State2 := { v := not s.v }

/-- スワップは 2 回で元に戻る。 -/
theorem Tswap_involutive (s : State2) : Tswap (Tswap s) = s := by
  cases s
  simp [Tswap]

/-- スワップ遷移の 2 回反復は元に戻る。 -/
theorem iterate_Tswap_two (s : State2) : iterate Tswap 2 s = s := by
  simp [iterate, Tswap_involutive]

end DkMath.UnitCycle
