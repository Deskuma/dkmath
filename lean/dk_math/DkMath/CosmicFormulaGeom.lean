/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib

namespace DkMath
namespace CosmicFormulaGeom

open Finset

/-- 格子セル（自然数格子） -/
abbrev Cell := ℕ × ℕ

/-- 図形（有限セル集合） -/
abbrev Shape := Finset Cell

/-- 面積（セル数） -/
def area (S : Shape) : ℕ := S.card

/-- 幅 w、高さ h の長方形：{0..w-1}×{0..h-1} -/
def rect (w h : ℕ) : Shape :=
  (Finset.range w).product (Finset.range h)

/-- 正方形 -/
def square (n : ℕ) : Shape := rect n n

@[simp] lemma area_rect (w h : ℕ) : area (rect w h) = w * h := by
  -- card (range w × range h) = w*h
  simp [area, rect, Finset.card_product]

@[simp] lemma area_square (n : ℕ) : area (square n) = n * n := by
  simp [square]

/-- rect への所属判定（座標不等式） -/
lemma mem_rect {w h : ℕ} {p : Cell} :
    p ∈ rect w h ↔ p.1 < w ∧ p.2 < h := by
  -- mem (range w × range h)
  simp only [rect, product_eq_sprod, mem_product, mem_range]

/-- 平行移動の埋め込み（ℕ格子） -/
def translateEmb (v : Cell) : Cell ↪ Cell :=
{ toFun := fun c => (c.1 + v.1, c.2 + v.2)
, inj' := by
    intro a b h
    have h1 : a.1 + v.1 = b.1 + v.1 := congrArg Prod.fst h
    have h2 : a.2 + v.2 = b.2 + v.2 := congrArg Prod.snd h
    have ha : a.1 = b.1 := Nat.add_right_cancel h1
    have hb : a.2 = b.2 := Nat.add_right_cancel h2
    exact Prod.ext ha hb
}

/-- 平行移動 -/
def translate (v : Cell) (S : Shape) : Shape :=
  S.map (translateEmb v)

lemma area_translate (v : Cell) (S : Shape) :
    area (translate v S) = area S := by
  simp [area, translate, Finset.card_map]

/-- 宇宙式の「大きい正方形」 (x+u)×(x+u) -/
def big (x u : ℕ) : Shape := square (x + u)

/-- 4分割の部品 -/
def partA (x : ℕ) : Shape := square x                      -- x×x
def partB (x u : ℕ) : Shape := translate (x, 0) (rect u x)  -- 右下 u×x
def partC (x u : ℕ) : Shape := translate (0, x) (rect x u)  -- 左上 x×u
def gapU (x u : ℕ) : Shape := translate (x, x) (square u)  -- 右上 u×u（余白）

/-- 相対本体（余白を除いた3領域） -/
def body (x u : ℕ) : Shape := (partA x ∪ partB x u) ∪ partC x u

/-- 余白（u^2） -/
def gap (x u : ℕ) : Shape := gapU x u

/-- 相対本体の面積（card）計算：x^2 + 2xu = x(x+2u) -/
lemma area_body (x u : ℕ) :
    area (body x u) = x * (x + 2*u) := by
  -- 各部品の面積を先に計算
  have aA : area (partA x) = x*x := by simp [partA]
  have aB : area (partB x u) = u*x := by
    simpa [partB] using (area_translate (v := (x,0)) (S := rect u x))
  have aC : area (partC x u) = x*u := by
    simpa [partC] using (area_translate (v := (0,x)) (S := rect x u))

  -- 各領域が互いに素であることを示す
  -- （座標の範囲が互いに排他的であることから従う）
  have disj_AB : Disjoint (partA x) (partB x u) := by
    -- partA: [0,x) × [0,x)、partB: [x,x+u) × [0,x) なので x座標が交わらない
    sorry  -- TODO: omega による座標不等式の証明（強化フェーズで完成）

  have disj_AC : Disjoint (partA x) (partC x u) := by
    -- partA: [0,x) × [0,x)、partC: [0,x) × [x,x+u) なので y座標が交わらない
    sorry  -- TODO: omega による座標不等式の証明（強化フェーズで完成）

  have disj_BC : Disjoint (partB x u) (partC x u) := by
    -- partB: [x,x+u) × [0,x)、partC: [0,x) × [x,x+u) なので x座標とy座標が交わらない
    sorry  -- TODO: omega による座標不等式の証明（強化フェーズで完成）

  -- body = (A ∪ B) ∪ C なので、段階的に card を足す
  simp only [body, area]
  rw [Finset.card_union_of_disjoint]
  · rw [Finset.card_union_of_disjoint disj_AB]
    simp only [area] at aA aB aC
    rw [aA, aB, aC]
    ring
  · rw [Finset.disjoint_union_left]
    exact ⟨disj_AC, disj_BC⟩

/-- 余白（u×u）の面積は u^2（平行移動で不変） -/
lemma area_gap (x u : ℕ) : area (gap x u) = u*u := by
  simpa [gap, gapU] using (area_translate (v := (x,x)) (S := square u))

/-- 宇宙式（Finset版の橋）：面積恒等式として
    (x+u)^2 = x(x+2u) + u^2 を得る -/
theorem cosmic_area_identity (x u : ℕ) :
    (x + u) * (x + u) = x * (x + 2*u) + u*u := by
  -- ここは純代数（量）として ring で閉じる：幾何層の「意味付け」と一致する核心
  ring

-- ========================================
-- トロミノ構造との同値写像（u=1 の特殊化）
-- ========================================

/-- u=1 のとき、相対本体の面積は x(x+2) -/
lemma area_body_u1 (x : ℕ) : area (body x 1) = x * (x + 2) := by
  simp [area_body]

/-- u=1 のとき、余白の面積は 1 -/
lemma area_gap_u1 (x : ℕ) : area (gap x 1) = 1 := by
  simp [area_gap]

/-- u=1 のとき、大きい正方形の面積は (x+1)² -/
lemma area_big_u1 (x : ℕ) : area (big x 1) = (x + 1) * (x + 1) := by
  simp [big, area_square]

/-- トロミノの最小例：x=1, u=1 -/
-- この場合、body 1 1 は 3セル（L型相当）、gap 1 1 は 1セル（余白）、big 1 1 は 4セル（2×2）
lemma tromino_instance :
    area (body 1 1) = 3 ∧
    area (gap 1 1) = 1 ∧
    area (big 1 1) = 4 := by
  constructor
  · simp [area_body]
  constructor
  · simp [area_gap]
  · simp [big, area_square]

/-- 宇宙式のトロミノ解釈：N + 1 = P（N=3, P=4） -/
theorem cosmic_tromino_correspondence :
    area (body 1 1) + area (gap 1 1) = area (big 1 1) := by
  have h := tromino_instance
  omega

/-- 一般化：任意の x, u に対して本体+余白=全体 -/
theorem cosmic_decomposition (x u : ℕ) :
    area (body x u) + area (gap x u) = area (big x u) := by
  rw [area_body, area_gap, big, area_square]
  ring

/-- 宇宙式の幾何的意味：差分が常に u² に閉じる -/
theorem cosmic_gap_invariant (x u : ℕ) :
    area (big x u) - area (body x u) = u * u := by
  -- area (big x u) = area (body x u) + area (gap x u) から導出
  have h := cosmic_decomposition x u
  -- h : area (body x u) + area (gap x u) = area (big x u)
  have gap_eq : area (gap x u) = u * u := area_gap x u
  rw [gap_eq] at h
  omega

/-- Cell 1個 ⇔ u²=1 の対応（u=1 の場合） -/
theorem cell_unit_correspondence :
    area (gap 1 1) = 1 * 1 := by
  simp [area_gap]

-- ========================================
-- 普遍性：x が関数 f(x) に置き換わっても、差分 u² は不変
-- ========================================

/-- 任意の関数 f に対して、宇宙式の差分は u² に閉じる -/
theorem cosmic_universality (f : ℕ → ℕ) (x u : ℕ) :
    (f x + u) * (f x + u) = (f x) * (f x + 2*u) + u * u := by
  -- 代数恒等式として ring で閉じる（加法形式）
  ring

/-- 関数による更新でも、幾何構造（分割）は保たれる -/
theorem cosmic_structure_invariant (f : ℕ → ℕ) (x u : ℕ) :
    area (gap (f x) u) = u * u := by
  -- gap の面積は x に依存しない
  simp [area_gap]

/-- トロミノ構造 ⇔ 宇宙式構造の対応まとめ -/
theorem tromino_cosmic_equivalence :
    -- トロミノ最小例（x=1, u=1）での対応
    (area (body 1 1) = 3 ∧ area (gap 1 1) = 1 ∧ area (big 1 1) = 4) ∧
    -- 面積の加法性
    (area (body 1 1) + area (gap 1 1) = area (big 1 1)) ∧
    -- 宇宙式への橋
    ((1 + 1) * (1 + 1) = 1 * (1 + 2*1) + 1*1) := by
  constructor
  · exact tromino_instance
  constructor
  · exact cosmic_tromino_correspondence
  · ring

end CosmicFormulaGeom
end DkMath
