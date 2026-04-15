/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib

#print "file: DkMath.Polyomino"

namespace DkMath
namespace Polyomino

abbrev Cell := ℤ × ℤ  -- セルは整数格子点のペアで表現
abbrev Shape := Finset Cell  -- 有限集合としてのポリオミノ

-- 面積（セル数）
def area {α : Type*} (P : Finset α) : ℕ := P.card  -- 有限集合の要素数

/-! ## セクション 1：L型トロミノの判定（平行移動版）

    IsLTromino の実装は Tromino.lean で提供される予定。
-/

variable {α : Type*} [DecidableEq α]

-- L型トロミノ（平行移動のみ）の判定述語
variable (IsLTromino : Finset α → Prop)

-- L型トロミノのセル数は常に3
variable (isLTromino_card_eq_three : ∀ {t : Finset α}, IsLTromino t → t.card = 3)

/-! ## セクション 2：Tiling 構造（partition） -/

section TilingSection

open scoped BigOperators
open Finset

/-- タイル族が領域を敷き詰める（partition）ことの定義 -/
structure Tiling (R : Finset α) (tiles : Finset (Finset α)) : Prop where
  /-- 各タイルは R に含まれる -/
  subset_R : ∀ {t}, t ∈ tiles → t ⊆ R
  /-- タイル同士は交わらない（pairwise disjoint） -/
  pairwise_disjoint : (tiles : Set (Finset α)).Pairwise Disjoint
  /-- タイルの和集合が R と一致 -/
  cover : tiles.biUnion id = R

/-- L型トロミノだけで敷き詰め可能 -/
def TileableByLTromino (R : Finset α) : Prop :=
  ∃ tiles : Finset (Finset α), Tiling R tiles ∧ (∀ t ∈ tiles, IsLTromino t)

/-! ## セクション 3：Pairwise Disjoint なら card は足し算 -/

/-- Pairwise Disjoint の場合、biUnion の card は sum card に等しい
    これが「スケール詐欺を禁止」する中核補題じゃ
-/
lemma card_biUnion_eq_sum_card_of_pairwise_disjoint
    {α : Type*} [DecidableEq α]
    {R : Finset α} {tiles : Finset (Finset α)}
    (hdis : (tiles : Set (Finset α)).Pairwise Disjoint)
    (_hsub : ∀ {t}, t ∈ tiles → t ⊆ R) :
    (tiles.biUnion id).card = ∑ t ∈ tiles, t.card := by
  exact card_biUnion hdis

/-- 彩色フィルタ版：Pairwise Disjoint ならフィルタ後の card も和になる -/
lemma card_biUnion_filter_eq_sum_card_filter
    {α : Type*} [DecidableEq α] (P : α → Prop) [DecidablePred P]
    {tiles : Finset (Finset α)}
    (hdis : (tiles : Set (Finset α)).Pairwise Disjoint) :
    ((tiles.biUnion id).filter P).card = ∑ t ∈ tiles, (t.filter P).card := by
  -- biUnion と filter は交換可能：(∪ t).filter P = ∪ (t.filter P)
  rw [filter_biUnion]
  -- Finset.card_biUnion を適用
  apply card_biUnion
  intros t1 ht1 t2 ht2 hne
  simp only [id_def]
  apply Disjoint.mono (filter_subset _ _) (filter_subset _ _)
  exact hdis ht1 ht2 hne

/-! ## セクション 4：敷き詰め可能なら card = 3k -/

/-- L型トロミノで敷き詰め可能なら、R の card は 3 の倍数で、かつ 3*tile数 -/
lemma tileableByLTromino_card_mul_three
    (isLTromino_card_eq_three : ∀ (t : Finset α), IsLTromino t → t.card = 3)
    {R : Finset α} (h : TileableByLTromino IsLTromino R) :
    ∃ tiles : Finset (Finset α), (Tiling R tiles) ∧ R.card = 3 * tiles.card := by
  classical
  rcases h with ⟨tiles, htil, hall⟩
  refine ⟨tiles, htil, ?_⟩
  -- cover で R = biUnion
  have hcover : tiles.biUnion id = R := htil.cover
  -- card を取り、disjoint から sum card へ
  have hsum : (tiles.biUnion id).card = ∑ t ∈ tiles, t.card := by
    exact card_biUnion_eq_sum_card_of_pairwise_disjoint (htil.pairwise_disjoint) (htil.subset_R)
  -- 各タイル card=3
  have ht3 : ∀ t ∈ tiles, t.card = 3 := by
    intro t ht
    exact isLTromino_card_eq_three t (hall t ht)
  -- sum を 3 * card に落とす
  have sum_eq : (∑ t ∈ tiles, t.card) = 3 * tiles.card := by
    rw [Finset.sum_congr rfl (fun t ht => ht3 t ht)]
    simp [mul_comm]
  -- まとめ
  calc
    R.card = (tiles.biUnion id).card := by simp [hcover]
    _ = ∑ t ∈ tiles, t.card := hsum
    _ = 3 * tiles.card := sum_eq

end TilingSection

end Polyomino
end DkMath
