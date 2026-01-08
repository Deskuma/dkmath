import Mathlib
import DkMath.Polyomino

namespace DkMath
namespace Polyomino
namespace Tromino

-- 原点付近の基本形
/-- L字型のトリオミノを表す有限集合
```txt
🟦🟦
🟦
```
-/
def L_tromino : Shape :=
  { (0,0), (1,0),
    (0,1) }

/--
直線型のトリオミノを表す有限集合
```txt
🟦🟦🟦
```
-/
def I_tromino : Shape :=
  { (0,0), (1,0), (2,0) }

/--
2×2の正方形ブロックを表す有限集合
```txt
⬜️⬜️
⬜️⬜️
```
-/
def block2 : Shape :=
  { (0,0), (1,0),
    (0,1), (1,1) }

/--
2×2ブロックの中の1セルの穴を表す有限集合
```txt
⬜️⬜️
⬜️🟥
```
-/
def hole2 : Shape :=
  { (1,1) }

-- 面積の確認

/-- L字型トリオミノの面積は3 -/
lemma area_L_tromino : area L_tromino = 3 := by
  simp [area, L_tromino]

/-- 2×2ブロックの面積は4 -/
lemma area_block2 : area block2 = 4 := by
  simp [area, block2]

/-- 2×2ブロックの穴の面積は1 -/
lemma area_hole2 : area hole2 = 1 := by
  simp [area, hole2]

/-- 2×2ブロックは L字型トリオミノと穴の和集合に等しい -/
lemma block2_eq_L_union_hole : block2 = L_tromino ∪ hole2 := by
  -- 具体的な有限集合の等式は decidable なので decide が刺さることが多い
  decide
  -- 「2×2 = L + 余白1」を集合で言う（等式は decide が強い）

/-- L字型トリオミノと穴は交わらない -/
lemma disjoint_L_hole : Disjoint L_tromino hole2 := by
  decide
  -- L と hole は交わらない

-- 平行移動

/-- 平行移動の埋め込み -/
def translateEmb (v : Cell) : Cell ↪ Cell :=
{ toFun := fun c => (c.1 + v.1, c.2 + v.2)
, inj' := by
    intros a b h
    -- 逆写像を使って各成分の等式を導き、最後に Prod.ext で結合する
    have h1 : a.1 + v.1 = b.1 + v.1 := congrArg Prod.fst h
    have h2 : a.2 + v.2 = b.2 + v.2 := congrArg Prod.snd h
    have ha : a.1 = b.1 := by
      apply add_right_cancel h1
    have hb : a.2 = b.2 := by
      apply add_right_cancel h2
    exact Prod.ext ha hb
}

/-- 平行移動の埋め込み（短縮形） -/
def translateEmb' (v : Cell) : Cell ↪ Cell :=
{ toFun := fun c => (c.1 + v.1, c.2 + v.2)
, inj' := fun ⦃_ _⦄ h ↦
  have h1 := congrArg Prod.fst h;
  have h2 := congrArg Prod.snd h;
  have ha := add_right_cancel h1;
  have hb := add_right_cancel h2;
  Prod.ext ha hb
}

/-- translateEmb と translateEmb' は同じ定義 -/
lemma translateEmb_eq_translateEmb' (v : Cell) :
  translateEmb v = translateEmb' v := by
  rfl

/-- 平行移動 -/
def translate (v : Cell) (P : Shape) : Shape :=
  P.map (translateEmb' v)

-- test
#eval translate (1,2) L_tromino  -- {(1, 2), (2, 2), (1, 3)}

example : translate (1,2) L_tromino = {(1,2), (2,2), (1,3)} := by
  decide

-- lemmas about translate

/-- 平行移動しても面積（セル数）は変わらない -/
lemma area_translate (v : Cell) (P : Shape) :
    area (translate v P) = area P := by
  simp [area, translate]


/-- 交わらない2つのポリオミノの和集合の面積は足し算 -/
lemma area_union_of_disjoint (A B : Shape) (h : Disjoint A B) :
    area (A ∪ B) = area A + area B := by
  simpa [area] using (Finset.card_union_of_disjoint h)


/-- 2×2 ブロックは「Lトロミノ + 穴1セル」なので面積は 3+1 -/
lemma area_block2_eq_area_L_add_area_hole :
    area block2 = area L_tromino + area hole2 := by
  -- block2 を L ∪ hole に置換して card_union を使う
  simpa [block2_eq_L_union_hole] using
    (area_union_of_disjoint L_tromino hole2 disjoint_L_hole)


end Tromino
end Polyomino
end DkMath
