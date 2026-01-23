# 完了した作業

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
