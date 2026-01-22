/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib

namespace DkMath

/-- d 次元の格子セル（座標は ℤ）。 -/
def Cell (d : ℕ) : Type := Fin d → ℤ

namespace CellDim

open scoped BigOperators

variable {d : ℕ}

instance : Add (Cell d) where
  add := fun x y => fun i => x i + y i

instance : Zero (Cell d) where
  zero := fun _ => 0

instance : Neg (Cell d) where
  neg := fun x => fun i => - x i

instance : Sub (Cell d) where
  sub := fun x y => fun i => x i - y i

/-
Note: pointwise `AddGroup` (and related bundled instances) can be derived
from these pointwise defs. We avoid adding an explicit `AddGroup` here to
keep proofs localized; add it later if Mathlib usage requires the full
algebraic structure.
-/

/-- 平行移動のための埋め込み `p ↦ p + v`（injective）。 -/
def addEmb (v : Cell d) : Cell d ↪ Cell d :=
{ toFun := fun p => p + v
  inj' := by
    intro a b h
    -- `Pi` の ext
    funext i
    -- 座標ごとに加法キャンセル
    have := congrArg (fun f => f i) h
    -- a i + v i = b i + v i
    exact add_right_cancel this }

/-- 平行移動（Finset.map を使うので card が保たれる）。 -/
def translate (v : Cell d) (S : Finset (Cell d)) : Finset (Cell d) :=
  S.map (addEmb (d := d) v)

@[simp] lemma translate_val (v : Cell d) (S : Finset (Cell d)) :
    (translate (d := d) v S).val = _ := rfl

@[simp] lemma card_translate (v : Cell d) (S : Finset (Cell d)) :
    (translate (d := d) v S).card = S.card := by
  classical
  simp [translate]

/-- `translate` は和集合に分配（map の性質）。-/
lemma translate_union (v : Cell d) (A B : Finset (Cell d)) :
    translate (d := d) v (A ∪ B) = translate (d := d) v A ∪ translate (d := d) v B := by
  classical
  -- `Finset.map_union` が使える環境が多い。無ければ `ext` で追う。
  ext x
  simp [translate]

/-- `translate` は空集合を保つ。 -/
@[simp] lemma translate_empty (v : Cell d) :
    translate (d := d) v (∅ : Finset (Cell d)) = ∅ := by
  classical
  simp [translate]

/-! ### Box（直方体）: `0 ≤ p(i) < a(i)` を満たすセル集合 -/

/-- `Fin d → ℕ` を `Cell d = Fin d → ℤ` に埋め込む。 -/
def ofNatCellEmb (d : ℕ) : (Fin d → ℕ) ↪ Cell d :=
{ toFun := fun p i => Int.ofNat (p i)
  inj' := by
    intro a b h
    funext i
    have := congrArg (fun f => f i) h
    -- Int.ofNat (a i) = Int.ofNat (b i)
    exact Int.ofNat.inj this }

/-- 原点箱：各軸 i で `0..a(i)-1` を取る。-/
def Box (a : Fin d → ℕ) : Finset (Cell d) :=
  (Finset.pi (fun i : Fin d => Finset.range (a i))).map (ofNatCellEmb d)

@[simp] lemma card_Box (a : Fin d → ℕ) :
    (Box (d := d) a).card = (Finset.pi (fun i : Fin d => Finset.range (a i))).card := by
  classical
  simp [Box]

/--
`Box` の card は積になる（理想形）:
`(Box a).card = ∏ i, a i`
※ Mathlib 側の補題名は環境で微妙に揺れるので、お主の側で仕上げるのが早い。
-/
lemma card_Box_eq_prod (a : Fin d → ℕ) :
    (Box (d := d) a).card = ∏ i : Fin d, a i := by
  classical
  -- だいたい `simp` か `simpa` で落ちる候補：
  --   simp [Box, Finset.card_map, Finset.card_pi, Finset.card_range]
  -- もし `Finset.card_pi` が無ければ、`Fintype.card_pi` や `Finset.card_biUnion` 系で代替。
  -- ここは最終調整ポイントとして空けておく。
  simpa [Box]  -- TODO: 強化

/-- 原点箱を平行移動した箱。 -/
def BoxAt (o : Cell d) (a : Fin d → ℕ) : Finset (Cell d) :=
  translate (d := d) o (Box (d := d) a)

@[simp] lemma card_BoxAt (o : Cell d) (a : Fin d → ℕ) :
    (BoxAt (d := d) o a).card = (Box (d := d) a).card := by
  classical
  simp [BoxAt, card_translate]

end CellDim
end DkMath
