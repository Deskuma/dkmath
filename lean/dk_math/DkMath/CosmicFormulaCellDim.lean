/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib
import DkMath.CellDim

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

/-! ### 補題群: 積をべきに畳み、card を差で表す -/

namespace DkMath
namespace CosmicFormulaCellDim

open scoped BigOperators
open DkMath.CellDim

variable {d : ℕ}

/-- Fin d 上の定数積はべきに畳める: (∏ _ : Fin d, n) = n^d. -/
lemma prod_const_fin (n : ℕ) :
    (∏ _i : Fin d, n) = n ^ d := by
  classical
  simp [Finset.prod_const, Fintype.card_fin]

/-- card_Big をべき表示にする -/
theorem card_Big_pow (x u : ℕ) :
    (Big (d := d) x u).card = (x + u) ^ d := by
  classical
  simp only [card_Big, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- card_Gap をべき表示にする -/
theorem card_Gap_pow (u : ℕ) :
    (Gap (d := d) u).card = u ^ d := by
  classical
  simp only [card_Gap, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- Body の濃度は全体から gap を引いたものに等しい -/
theorem card_Body_eq_sub (d x u : ℕ) :
    (Body (d := d) x u).card =
      (Big (d := d) x u).card - (Gap (d := d) u).card := by
  classical
  have h := card_Big_eq_card_Body_add_card_Gap (d := d) x u
  calc
    (Body (d := d) x u).card
        = ((Body (d := d) x u).card + (Gap (d := d) u).card) - (Gap (d := d) u).card := by
          rw [Nat.add_sub_cancel (Body (d := d) x u).card (Gap (d := d) u).card]
    _ = (Big (d := d) x u).card - (Gap (d := d) u).card := by
          rw [h]

/-- 最終形: Body = (x+u)^d - u^d. -/
theorem card_Body_pow_form (d x u : ℕ) :
    (Body (d := d) x u).card = (x + u) ^ d - u ^ d := by
  classical
  simp only [card_Body_eq_sub (d := d) x u, card_Big_pow (d := d) x u, card_Gap_pow (d := d) u]

/-- 差のべきの因数分解に使う和 `G` -/
def G (d x u : ℕ) : ℕ :=
  Finset.sum (Finset.range d) fun k => (x + u)^(d - 1 - k) * u ^ k

/-- (x+u)^d - u^d = x * G x u -/
theorem pow_sub_pow_eq_mul_G (d x u : ℕ) :
    (x + u) ^ d - u ^ d = x * G d x u := by
  induction d with
  | zero =>
    -- range 0 の和は 0, 両辺とも 0
    simp [G]
  | succ d ih =>
    let a := x + u
    let b := u
    have h_ab : a - b = x := by simp [a, b]
    -- 幾何和の補題を使用します: (∑_{i < d+1} a^i b^{d-i})*(a-b) + b^{d+1} = a^{d+1}
    have h := (Commute.all (a - b) b).geom_sum₂_mul_add (d + 1)
    -- 合計インデックスを反映して、`∑ k ∈ Finset.range (d+1), a^(d-k) * b^k` 形式と一致するようにします。
    have h' : (a - b) * ∑ k ∈ Finset.range (d + 1), a ^ (d - k) * b ^ k
      = a ^ (d + 1) - b ^ (d + 1) := by
      -- 直接 `Finset.sum_range_reflect` を使って h の和の向きを反転する
      rw [← Finset.sum_range_reflect] at h
      -- eq_tsub_of_add_eq h は `(Finset.sum ... ) * (a - b) = a^(d+1) - b^(d+1)` を与えるので、
      -- それを目的形に合わせるために `mul_comm` で掛け算の順序を入れ替える。
      let h1 := eq_tsub_of_add_eq h
      rw [mul_comm] at h1
      -- 簡約: a - b + b = a, d + 1 - 1 - j = d - j
      simp only [Nat.add_sub_cancel] at h1
      -- a - b = x より a = x + b を先に確立する
      have ha_eq : a = x + b := by simp [a, b]
      convert h1 using 2
      · -- ⊢ ∑ k ∈ Finset.range (d + 1), a ^ (d - k) * b ^ k
        -- = ∑ x ∈ Finset.range (d + 1), (a - b + b) ^ (d - x) * b ^ (d - (d - x))
        refine Finset.sum_congr rfl ?_
        intro x_1 hx
        have hx' : x_1 ≤ d := Nat.le_of_lt_succ (Finset.mem_range.1 hx)
        have hsub : d - (d - x_1) = x_1 := by
          apply (Nat.sub_eq_iff_eq_add (a := d) (b := d - x_1) (c := x_1) (Nat.sub_le _ _)).2
          simpa using (Nat.add_sub_of_le hx').symm
        have hsum : a - b + b = a := by
          calc
            a - b + b = x + b := by simp [h_ab]
            _ = a := by simp [ha_eq]
        simp [hsub, hsum]
      · -- ⊢ a ^ (d + 1) = (a - b + b) ^ (d + 1)
        simp [ha_eq]
    simpa [h_ab] using (Eq.symm h')

/-- 最終形: Body = x * G d x u -/
theorem card_Body_eq_mul_G (d x u : ℕ) :
    (Body (d := d) x u).card = x * G d x u := by
  -- 既存の card_Body_pow_form と今回の pow_sub_pow_eq_mul_G を繋ぐ
  simpa [card_Body_pow_form (d := d) x u] using pow_sub_pow_eq_mul_G d x u

end CosmicFormulaCellDim
end DkMath
