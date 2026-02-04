/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.DHNT.DHNT_Base
import DkMath.UnitCycle.Core

/-
Unit/Nat 層の最小 Lean 定義と交えない定理
-/

namespace DkMath.DHNT

open DkMath.UnitCycle

/-- Nat 層での「進歩」：毎ステップ I が 1 以上増える -/
def Progress {State : Type} (T : State → State) (I : State → Nat) : Prop :=
  ∀ s, I (T s) ≥ I s + 1

/-- Nat 層での「閉路」：k > 0 で反復が元へ戻る -/
def HasCycle {State : Type} (T : State → State) : Prop :=
  ∃ s k, k > 0 ∧ iterate T k s = s

/-- 「交える」＝（π 的）閉路と（e 的）進歩が同居すること -/
def Mixable {State : Type} (T : State → State) (I : State → Nat) : Prop :=
  HasCycle T ∧ Progress T I

/-- 進歩がある系では閉路は起きない（ゆえに交えない） -/
theorem not_mixable_of_progress {State : Type} {T : State → State} {I : State → Nat}
  (hP : Progress T I) : ¬ Mixable T I := by
  intro hM
  rcases hM with ⟨⟨s, k, hkpos, hk⟩, _⟩
  have hk0 := no_nontrivial_cycle_of_ge_one (State := State) (T := T) (I := I) hP k s hk
  exact (Nat.ne_of_gt hkpos) hk0

-- ----------------------------------------------------------------------------
-- Bridge 経由の閉路と進歩
-- ----------------------------------------------------------------------------
section BridgeBased

/-- 抽象的な橋渡し（Unit → ℕ） -/
class Bridge where
  phi : Unit → Nat
  pi  : Unit

/-- ある Unit の像の長さで閉路が生じることを表す -/
def HasCycleOfUnit {State : Type} (T : State → State) (B : Bridge) : Prop :=
  ∃ (u : Unit) (s : State), let k := B.phi u; k > 0 ∧ iterate T k s = s

/-- Bridge を経由した「交える」定義 -/
def MixableViaBridge {State : Type} (T : State → State) (I : State → Nat) (B : Bridge) : Prop :=
  HasCycleOfUnit T B ∧ Progress T I

/-- Bridge 経由でも進歩がある系では閉路は起きない -/
theorem not_mixable_via_bridge_of_progress {State : Type} {T : State → State} {I : State → Nat}
  {B : Bridge} (hP : Progress T I) : ¬ MixableViaBridge T I B := by
  intro hM
  rcases hM with ⟨⟨u, s, hk⟩, _⟩
  -- hk : let k := B.phi u; k > 0 ∧ iterate T k s = s
  have hkpos : (B.phi u) > 0 := by
    dsimp at hk
    exact hk.left
  have hk_eq : iterate T (B.phi u) s = s := by
    dsimp at hk
    exact hk.right
  have hk0 := no_nontrivial_cycle_of_ge_one (State := State) (T := T) (I := I) hP (B.phi u) s hk_eq
  exact (Nat.ne_of_gt hkpos) hk0

noncomputable section

open Real

/-- π を Unit として使う Bridge -/
def piUnit : Unit := ⟨Real.pi, Real.pi_pos⟩

/-- π を像とする Bridge -/
def piBridge : Bridge where
  phi := fun _ => 1
  pi  := piUnit

theorem not_mixable_piBridge {State : Type} {T : State → State} {I : State → Nat}
  (hP : Progress T I) : ¬ MixableViaBridge T I piBridge :=
  not_mixable_via_bridge_of_progress (hP := hP)

/-! 追加の具体例：floor による橋と倍率 10 のスケール橋 -/

/-- floor によって Unit の大きさを Nat に落とし、常に 1 以上にする Bridge -/
def floorBridge : Bridge where
  phi := fun u => Int.toNat (Int.floor u.val) + 1
  pi  := piUnit

/-- phi(u) > 0 を示す -/
theorem floorBridge_pos (u : Unit) : floorBridge.phi u > 0 := by
  dsimp [floorBridge]
  apply Nat.succ_pos

/-- u.val * 10 の floor を取ることで小数帯域を粗く量子化する Bridge -/
def scale10Bridge : Bridge where
  phi := fun u => Int.toNat (Int.floor (u.val * 10)) + 1
  pi  := piUnit

/-- phi(u) > 0 を示す -/
theorem scale10Bridge_pos (u : Unit) : scale10Bridge.phi u > 0 := by
  dsimp [scale10Bridge]
  apply Nat.succ_pos

/-! ## Small examples for CI: use `State := Nat`, `T := succ`, `I := id` which satisfy `Progress` -/

def T_succ (n : Nat) := n + 1
def I_id (n : Nat) := n

/-! ### 交えない例：T = succ, I = id のとき -/

/-- piBridge による交えない例 -/
example : ¬ MixableViaBridge (T := T_succ) (I := I_id) piBridge := by
  have hP : Progress T_succ I_id := by
    intro s
    dsimp [T_succ, I_id]
    exact Nat.le_refl (s + 1)
  exact not_mixable_piBridge hP

/-- floorBridge による交えない例 -/
example : ¬ MixableViaBridge (T := T_succ) (I := I_id) floorBridge := by
  have hP : Progress T_succ I_id := by intro s; dsimp [T_succ, I_id]; exact Nat.le_refl (s + 1)
  exact not_mixable_via_bridge_of_progress (hP := hP)

/-- scale10Bridge による交えない例 -/
example : ¬ MixableViaBridge (T := T_succ) (I := I_id) scale10Bridge := by
  have hP : Progress T_succ I_id := by intro s; dsimp [T_succ, I_id]; exact Nat.le_refl (s + 1)
  exact not_mixable_via_bridge_of_progress (hP := hP)

end -- noncomputable section

end BridgeBased

end DkMath.DHNT
