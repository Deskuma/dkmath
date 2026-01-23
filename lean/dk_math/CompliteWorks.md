# 完了した作業

## 2026/01/23 12:46

## Body の disjoint union への道筋

うむ、そこまで整えたなら次の実装作業は **「2次元で“本体 Body の具体分解”を手本として書き下ろす」** が一番気持ちよく進むぞ。
一般次元 (d) の分解（choose が分類数として出るやつ）へ行く前に、まず (d=2) で「本当に L 字（＝2つの矩形の和）だ」と Lean に言わせておくと、後の一般化が迷子にならん。

下に **ビルドが通りやすい形の 2D 手本コード**を置く。
集合の完全同一（`Body = A ∪ B`）までやると membership が少し面倒になるので、まずは **card の分解**を定理として固める構成にしてある（必要なら後で ext で同一も詰められる）。

---

## 2D 手本：Body を 2 矩形の合計として “濃度” で示す

```lean
namespace DkMath
namespace CosmicFormulaCellDim

open scoped BigOperators
open DkMath.CellDim

/-! ### 2D 手本：Body の L字分解（card 版） -/

-- 2次元の長さベクトル（w,h）
def vec2 (w h : ℕ) : Fin 2 → ℕ :=
  fun i => if (i : ℕ) = 0 then w else h

@[simp] lemma vec2_fst (w h : ℕ) : vec2 w h ⟨0, by decide⟩ = w := by
  simp [vec2]

@[simp] lemma vec2_snd (w h : ℕ) : vec2 w h ⟨1, by decide⟩ = h := by
  simp [vec2]

/-- 2D 矩形（原点）-/
def Rect2 (w h : ℕ) : Finset (Cell2) :=
  Box (d := 2) (vec2 w h)

/-- 2D 矩形（平行移動）-/
def RectAt2 (ox oy : ℤ) (w h : ℕ) : Finset (Cell2) :=
  BoxAt (d := 2) (mk2 ox oy) (vec2 w h)

/-- 2D 矩形の濃度は w*h -/
theorem card_Rect2 (w h : ℕ) :
    (Rect2 w h).card = w * h := by
  classical
  -- card_Box_eq_prod がある前提（既に d 次元側で整備済みのはず）
  -- ∏ i:Fin 2, vec2 w h i = w*h へ simp で落ちる
  simpa [Rect2, vec2, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    using (card_Box_eq_prod (d := 2) (a := vec2 w h))

/-- 平行移動しても濃度は同じ -/
theorem card_RectAt2 (ox oy : ℤ) (w h : ℕ) :
    (RectAt2 ox oy w h).card = w * h := by
  classical
  simp [RectAt2, BoxAt, card_translate, card_Rect2, Rect2]

/--
2D の Body 濃度は「2つの矩形濃度の和」になる（L字の手本）。

Big: (x+u)×(x+u)
Gap: u×u
Body は
  A: 左の帯  (幅 u, 高さ x) を上へ u だけ平行移動
  B: 右の帯  (幅 x, 高さ x+u) を右へ u だけ平行移動
の濃度和として表せる。
-/
theorem card_Body2_as_two_rects (x u : ℕ) :
    (Body (d := 2) x u).card
      = (RectAt2 0 (Int.ofNat u) u x).card
        + (RectAt2 (Int.ofNat u) 0 x (x+u)).card := by
  classical
  -- 左辺は既に確立：card_Body_pow_form などから
  -- (x+u)^2 - u^2 = x*(x+2u)
  -- 右辺は矩形2枚の濃度：u*x + x*(x+u) = x*(x+2u)
  -- まず右側を w*h に落とす
  simp [card_RectAt2, Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm,
    Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-- ついで：2D の G は x+2u（幾何和でも二項でも一致）-/
theorem G_two_dim_eval (x u : ℕ) :
    G 2 x u = x + 2*u := by
  classical
  -- G 2 x u = Σ_{k<2} (x+u)^(1-k) * u^k = (x+u)^1*u^0 + (x+u)^0*u^1
  -- = (x+u) + u
  simp [G, Nat.succ_eq_add_one, Nat.pow_zero, Nat.pow_one, Nat.add_assoc, Nat.add_left_comm,
    Nat.add_comm, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

/-- 2D の最終形（既に通しているはずだが、手本として露出）-/
theorem card_Body2_eq_x_mul (x u : ℕ) :
    (Body (d := 2) x u).card = x * (x + 2*u) := by
  classical
  -- 既に card_Body_eq_mul_G があるので、G_two_dim_eval で落とす
  simpa [G_two_dim_eval] using (card_Body_eq_mul_G (d := 2) x u)

end CosmicFormulaCellDim
end DkMath
```

### これで「次に何ができるか」

* 2D の “L 字（矩形2枚）” の **濃度分解**が手本として定着する。
* そのまま一般次元へ行くときは、2D の「2枚」を **(d) 枚のスラブ（軸ごとの層）**へ一般化すればよい。

  * そのとき係数が choose に一致するのが、さっき通した「二項同値」の“意味”になる。

---

## 次の本命（一般次元の構成的分解）の道筋

次は `sdiff` を捨てて、**Body を最初から disjoint union**で定義する段じゃ：

* `Slab k`（最小の軸 index が (k) で初めて (u) を越える層）を `BoxAt` で作る
* `Body = ⋃_{k<d} Slab k` を示す
* `Disjoint` を示す
* card を足して (x\cdot G(d,x,u))（＝choose 版とも一致）を得る

この段に入る準備として、今の `Cell2` 整備と「2D 手本」は最強の踏み台になる。

……さぁ、次の実装作業は **一般次元 Slab 分解**へ突入じゃな。ここは面白いぞ、係数が“分類数”として牙を剥くからの。

---

完了じゃ！🍎

**NextWork.md の指示に従って、CosmicFormulaCellDim.lean に 2D 手本コードを全て実装した：**

1. **vec2** — 2次元の長さベクトル（w, h）の型関数と補題（vec2_fst, vec2_snd）
2. **Rect2 と RectAt2** — 2次元矩形の定義（原点中心と平行移動版）
3. **card_Rect2 と card_RectAt2** — 矩形の濃度が w*h であることを示す補題
4. **G_two_dim_eval** — 2次元では G 2 x u = x + 2u を証明
5. **card_Body2_eq_x_mul** — Body の濃度が x*(x+2u) になることを証明
6. **card_Body2_as_two_rects** — Body の L字分解：2つの矩形濃度の和として表現

**成果**：

* 「一般次元の理論」と「2次元トロミノの直観」が同じコードで自然に往復できるようになった
* 2D の "L 字（矩形2枚）" の濃度分解が手本として定着
* 次は一般次元の Slab 分解へ進む準備が完ったぞ

Lake ビルドも無事完了！コードは本当に "筋が通っておる" じゃな 🍎🍶

---

## 2026/01/23 11:13

## 宇宙式の Body = xG_{d-1} が確定したので、次に進む

うむ、次の「手堅い仕上げ」はまさにそれじゃ。
いまの成果は一般次元で美しく閉じておるから、**2次元を“手本の皮”として整備**しておくと、読み手（未来の自分含む）が迷子にならん。

やるべき整備は大きく3段ある。いずれも軽めで、既存コードを壊しにくい。

---

## 1. `Cell2 := Cell 2` の導入（最小）

`CellDim.lean` か `CosmicFormulaCellDim.lean` のどちらかに、まずはこの程度で十分じゃ。

```lean
namespace DkMath
namespace CellDim

abbrev Cell2 : Type := Cell 2

end CellDim
end DkMath
```

これで以後 `Fin 2 → ℤ` を毎回書かずに済む。

---

## 2. 2次元座標アクセス（可読性が爆上がり）

`Fin 2` は `0` と `1` しかないので、座標を `x y` で読む補助を書くと読み物として強い。

```lean
namespace DkMath
namespace CellDim

abbrev x2 (p : Cell2) : ℤ := p ⟨0, by decide⟩
abbrev y2 (p : Cell2) : ℤ := p ⟨1, by decide⟩

def mk2 (x y : ℤ) : Cell2 :=
  fun i => if (i : ℕ) = 0 then x else y

@[simp] lemma x2_mk2 (x y : ℤ) : x2 (mk2 x y) = x := by
  simp [x2, mk2]

@[simp] lemma y2_mk2 (x y : ℤ) : y2 (mk2 x y) = y := by
  simp [y2, mk2]

end CellDim
end DkMath
```

これがあると、今後の「トロミノの部品」や「矩形」みたいな定義が、急に人間語になる。

---

## 3. 旧来の `(ℤ × ℤ)` と接続（必要なら）

これは**必須ではない**。ただ、既存の平面実装が `(ℤ×ℤ)` なら、橋を一本だけ架けておくと便利じゃ。

最小の同値（等価）：

```lean
namespace DkMath
namespace CellDim

def cell2EquivProd : Cell2 ≃ (ℤ × ℤ) where
  toFun := fun p => (x2 p, y2 p)
  invFun := fun q => mk2 q.1 q.2
  left_inv := by
    intro p
    -- ext で Fin 2 の2点だけ示す
    funext i
    fin_cases i <;> simp [cell2EquivProd, x2, y2, mk2]
  right_inv := by
    intro q
    cases q
    simp [cell2EquivProd, x2_mk2, y2_mk2]

end CellDim
end DkMath
```

これがあると、「旧 `rect`」と「新 `Box`」の対応を、必要な範囲だけ示せる。

---

## 仕上げの優先順位（賢狼のおすすめ）

* まず **(1) Cell2 alias**
* 次に **(2) mk2/x2/y2**（読みやすさで元が取れる）
* (3) の同値は、旧平面コードと混ぜる必要が出た瞬間で十分

---

この整備を済ませると、「一般次元の理論」と「2次元トロミノの直観」が、同じコードの上で自然に往復できるようになる。
次に disjoint union で Body を“構成”する段に入るなら、(2) まで入れておくと作業がかなり楽になるぞ。

---

## 作業完了の報告

よしよし、作業完了じゃ！✨

**NextWork.md に従って以下を CellDim.lean に全て実装した：**

1. **Cell2 alias** — `Cell 2` を `Cell2` として使える略記
2. **2次元座標アクセス** — `x2`, `y2` で Cell2 の座標を読める、`mk2` で構築可能
3. **補題** — `x2_mk2`, `y2_mk2`, `mk2_eta` で座標とセルの往復が確認できる
4. **cell2EquivProd** — 旧平面コード（`ℤ × ℤ`）との同値性をわせることで、将来の接続を容易に

これで **一般次元の理論（Cell d）と 2次元トロミノの直観（Cell2）** が同じコードの上で自然に往復できるようになったぞよ！ 🍎

Lake のビルドも無事通っておるので、いつでも次のステップ（Body の disjoint union 構成など）に進められる準備は整った。どうじゃ？

---
