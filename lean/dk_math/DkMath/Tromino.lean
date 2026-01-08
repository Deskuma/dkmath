-- cid: 695fc5da-3614-8324-bc69-0417d227baba
import Mathlib
import DkMath.Polyomino

set_option linter.style.longLine true

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
  ext c <;> rfl

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
  simp only [area, translate, Finset.card_map]


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


-- =========================
-- Rotation / Reflection
-- =========================

/-- 90°回転（原点中心）: (x, y) ↦ (-y, x) -/
-- rotate 90 degree embedding
def rot90Emb : Cell ↪ Cell :=
{ toFun := fun c => (-c.2, c.1)
, inj' := by
    intro a b h
    -- h : (-a.2, a.1) = (-b.2, b.1)
    have h1 : -a.2 = -b.2 := congrArg Prod.fst h
    have h2 : a.1 = b.1 := congrArg Prod.snd h
    have ha2 : a.2 = b.2 := by
      -- -a.2 = -b.2 から a.2 = b.2
      simpa using (neg_inj.mp h1)
    -- Cell = ℤ×ℤ なので成分で ext
    exact Prod.ext h2 ha2
}

/-- 90°回転 -/
def rotate90 (P : Shape) : Shape :=
  P.map rot90Emb
-- 180°, 270°, 360°回転も定義しておく
def rotate180 (P : Shape) : Shape := rotate90 (rotate90 P)
def rotate270 (P : Shape) : Shape := rotate90 (rotate180 P)
def rotate360 (P : Shape) : Shape := rotate90 (rotate270 P)


/-- rot90Emb の適用例 -/
lemma rot90_apply (c : Cell) : rot90Emb c = (-c.2, c.1) := rfl


/-- x 軸反転（鏡映）: (x, y) ↦ (x, -y) -/
def reflectXEmb : Cell ↪ Cell :=
{ toFun := fun c => (c.1, -c.2)
, inj' := by
    intro a b h
    have h1 : a.1 = b.1 := congrArg (fun c => c.1) h
    have h2 : -a.2 = -b.2 := congrArg (fun c => c.2) h
    have ha2 : a.2 = b.2 := by
      simpa using (neg_inj.mp h2)
    exact Prod.ext h1 ha2
}

/-- x 軸反転 -/
def reflectX (P : Shape) : Shape :=
  P.map reflectXEmb

/-- y 軸反転（鏡映）: (x, y) ↦ (-x, y) -/
def reflectYEmb : Cell ↪ Cell :=
{ toFun := fun c => (-c.1, c.2)
, inj' := by
    intro a b h
    have h1 : -a.1 = -b.1 := congrArg Prod.fst h
    have h2 : a.2 = b.2 := congrArg (fun c => c.2) h
    have ha1 : a.1 = b.1 := by
      simpa using (neg_inj.mp h1)
    exact Prod.ext ha1 h2
}

/-- y 軸反転 -/
def reflectY (P : Shape) : Shape :=
  P.map reflectYEmb


/-- 90°回転しても面積は不変 -/
lemma area_rotate90 (P : Shape) :
    area (rotate90 P) = area P := by
  simp only [area, rotate90, Finset.card_map]

/-- x 軸反転しても面積は不変 -/
lemma area_reflectX (P : Shape) :
    area (reflectX P) = area P := by
  simp only [area, reflectX, Finset.card_map]

/-- y 軸反転しても面積は不変 -/
lemma area_reflectY (P : Shape) :
    area (reflectY P) = area P := by
  simp only [area, reflectY, Finset.card_map]

-- tests
#eval rotate90 L_tromino
#eval reflectX L_tromino
#eval reflectY L_tromino

example : area (rotate90 L_tromino) = 3 := by
  simpa [area_L_tromino] using (area_rotate90 (P := L_tromino))

example : area (reflectX L_tromino) = 3 := by
  simpa [area_L_tromino] using (area_reflectX (P := L_tromino))


/--
rotate360_eq (P : Shape) : rotate360 P = P

Proves that rotating a shape by 360 degrees (four successive 90° rotations)
leaves the shape unchanged. Here `rotate360` is implemented by mapping the
embedding `rot90Emb` four times over the finset of points of `P`. The proof
uses extensionality on finsets and the fundamental property `rot90_apply`
that `rot90Emb` composed with itself four times is the identity.

Proof sketch:
- For the direction `rotate360 P ⊆ P`, unpack the nested witnesses produced by
  the four maps (a chain `e → d → b → a → c`) and compose the equalities to
  obtain `c = rot90Emb^4 e = e`, hence `c ∈ P`.
- For the direction `P ⊆ rotate360 P`, given `c ∈ P` use the witness
  `rot90Emb^3 c` and its intermediate images `rot90Emb^2 c`, `rot90Emb c`, `c`
  to exhibit the required chain; `rot90_apply` simplifies the composed maps.

This lemma encapsulates the geometric intuition that a full 360° rotation is
the identity on shapes represented as finsets of embedded points.
-/
lemma rotate360_eq (P : Shape) : rotate360 P = P := by
  ext c
  simp only [rotate360, rotate90, rotate270, rotate180, Finset.mem_map]
  -- After simp, both sides expand to nested ∃ with ∧
  -- LHS: ∃ a, (∃ b, (∃ d, (∃ e, e ∈ P ∧ R90 e = d) ∧ R90 d = b) ∧ R90 b = a) ∧ R90 a = c
  -- RHS: c ∈ P
  constructor
  · intro ⟨a, ⟨b, ⟨d, ⟨e, he_mem, hd_eq⟩, hb_eq⟩, ha_eq⟩, hc_eq⟩
    -- We have: hd_eq : R90 e = d, hb_eq : R90 d = b, ha_eq : R90 b = a, hc_eq : R90 a = c
    -- So: R90 (R90 (R90 (R90 e))) = R90 (R90 (R90 d)) = R90 (R90 b) = R90 a = c
    -- By rot90_apply: R90^4 = id, so R90 (R90 (R90 (R90 e))) = e
    let e360 := rot90Emb (rot90Emb (rot90Emb (rot90Emb e)))
    let e270 := rot90Emb (rot90Emb (rot90Emb e))
    let e180 := rot90Emb (rot90Emb e)
    let e90 := rot90Emb e
    have h_id : e360 = e := by simp [e360, rot90_apply]
    have h_comp : e360 = c := by
      simp only [e360]
      calc rot90Emb (rot90Emb (rot90Emb (rot90Emb e)))
        = rot90Emb (rot90Emb (rot90Emb d)) := by rw [hd_eq]
        _ = rot90Emb (rot90Emb b) := by rw [hb_eq]
        _ = rot90Emb a := by rw [ha_eq]
        _ = c := by rw [hc_eq]
    rwa [← h_comp, h_id]
  · intro hc
    use rot90Emb (rot90Emb (rot90Emb c))
    refine ⟨?_, ?_⟩
    · use rot90Emb (rot90Emb c)
      refine ⟨?_, ?_⟩
      · use rot90Emb c
        refine ⟨?_, ?_⟩
        · exact ⟨c, hc, rfl⟩
        · simp [rot90_apply]
      · simp [rot90_apply]
    · simp [rot90_apply]


/-- Reflecting twice across the x-axis returns the original shape. -/
def reflectXX (P : Shape) : Shape := reflectX (reflectX P)


/--
For any shape `P : Shape`, `reflectXX P = P`.

`reflectXX` is defined by mapping `reflectXEmb` over the elements of `P` twice.
Since `reflectXEmb` is an involution (it is its own inverse), applying it twice
returns each element to itself, so the induced map on `Shape` is the identity.
This lemma records that fact.
-/
lemma reflectXX_eq (P : Shape) : reflectXX P = P := by
  ext c
  simp only [reflectXX, reflectX, Finset.mem_map]
  constructor
  · intro ⟨a, ⟨b, hb_mem, hb_eq⟩, ha_eq⟩
    -- hb_mem : b ∈ P
    -- hb_eq : reflectXEmb b = a
    -- ha_eq : reflectXEmb a = c
    -- Goal: c ∈ P
    -- Composition: reflectXEmb (reflectXEmb b) = reflectXEmb a = c
    -- But reflectXEmb (reflectXEmb b) = b by self-inverse property
    -- Therefore: b = c, so c ∈ P follows from hb_mem
    have h_comp : reflectXEmb (reflectXEmb b) = b := by simp [reflectXEmb]
    have h_eq : c = b := by
      calc c = reflectXEmb a := ha_eq.symm
        _ = reflectXEmb (reflectXEmb b) := by rw [← hb_eq]
        _ = b := h_comp
    rw [h_eq]
    exact hb_mem
  · intro hc
    -- hc : c ∈ P
    -- Goal: ∃ a, (∃ b, b ∈ P ∧ reflectXEmb b = a) ∧ reflectXEmb a = c
    -- Use b = c and a = reflectXEmb c
    use reflectXEmb c
    refine ⟨⟨c, hc, rfl⟩, ?_⟩
    simp [reflectXEmb]


-- tests
#eval rotate90 L_tromino  -- {(0, 0), (0, 1), (-1, 0)}
#eval reflectX L_tromino  -- {(0, 0), (1, 0), (0, -1)}
#eval reflectY L_tromino  -- {(0, 0), (-1, 0), (0, 1)}
#eval reflectXX L_tromino -- {(0, 0), (1, 0), (0, 1)}

example : rotate90 L_tromino ≠ L_tromino := by
  decide


end Tromino
end Polyomino
end DkMath
