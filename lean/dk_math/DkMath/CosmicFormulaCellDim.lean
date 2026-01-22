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

instance decidableEqCell : DecidableEq (Cell d) :=
  Fintype.decidablePiFintype

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
  simp [Big, constVec]

@[simp] lemma card_Gap (u : ℕ) :
    (Gap (d := d) u).card = ∏ _i : Fin d, u := by
  classical
  simp [Gap, constVec]

  -- Body と disjoint 分解は次段。

  -- 狙い（構造）:
  --   Big = Body ∪ Gap
  --   Disjoint Body Gap
  --   card Big = card Body + card Gap
  -- そして card を (x+u)^d, x*G_{d-1}(x,u), u^d に同定する。

  -- Body を差集合で作るより、「どの軸が u 以上か」で disjoint な箱の合併として構成するのが実装が強い。

  -- 以下はまず `sdiff` 版の雛形：集合恒等式を整え、のちに差し替え可能な形にしておく.

def Body (d x u : ℕ) : Finset (Cell d) :=
  Big (d := d) x u \ Gap (d := d) u

lemma Gap_subset_Big (d x u : ℕ) :
    Gap (d := d) u ⊆ Big (d := d) x u := by
  classical
  -- 各軸で `u ≤ x + u` なので Box_mono を使う
  have : ∀ i, (constVec d u) i ≤ (constVec d (x + u)) i := fun _ => Nat.le_add_left u x
  simp only [Gap, Big]
  exact Box_mono (d := d) (a := constVec d u) (b := constVec d (x + u)) this

lemma Big_eq_Body_union_Gap (d x u : ℕ) :
    Big (d := d) x u = Body (d := d) x u ∪ Gap (d := d) u := by
  classical
  have hsub : Gap (d := d) u ⊆ Big (d := d) x u := Gap_subset_Big (d := d) x u
  simpa [Body] using (Finset.sdiff_union_of_subset hsub)

lemma Disjoint_Body_Gap (d x u : ℕ) :
    Disjoint (Body (d := d) x u) (Gap (d := d) u) := by
  classical
  refine Finset.disjoint_left.2 ?_
  intro a ha hb
  -- ha : a ∈ Big \ Gap なので a ∉ Gap
  exact (Finset.mem_sdiff.1 ha).2 hb

lemma card_Big_eq_card_Body_add_card_Gap (d x u : ℕ) :
    (Big (d := d) x u).card =
      (Body (d := d) x u).card + (Gap (d := d) u).card := by
  classical
  have hdis : Disjoint (Body (d := d) x u) (Gap (d := d) u) := Disjoint_Body_Gap (d := d) x u
  calc
    (Big (d := d) x u).card
        = ((Body (d := d) x u ∪ Gap (d := d) u)).card := by
            simp [Big_eq_Body_union_Gap (d := d) x u]
        _ = (Body (d := d) x u).card + (Gap (d := d) u).card := by
          simpa using (Finset.card_union_of_disjoint hdis)


end CosmicFormulaCellDim
end DkMath
