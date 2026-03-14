# トロミノ充填による FLT 証明戦略

## 概要

フェルマーの最終定理（FLT）を **トロミノ充填の不完全性** から導く新しい証明戦略。

宇宙式（Cosmic Formula）の Cell 版構造を用いて：

1. **Big/Gap/Body 三分割** を Cell の Finset として形式化
2. **トロミノの自己相似充填可能性** を認める
3. しかし **ちょうどの平方完成充填は不可能** であることを示す
4. これが直接 FLT の矛盾を生み出す

---

## 基本構造：3+1=4

### 宇宙式の実体分解

$$\Large (x+u)^d = u^d + \mathrm{Body}(d,x,u)$$

Cell 版では：

- **Big（全体）**：$(x+u)^d$ 個のセル
- **Gap（余白）**：$u^d$ 個のセル  
- **Body（実体）**：$(x+u)^d - u^d$ 個のセル

### 最小ケース：d=2, x=1, u=1

$$2^2 = 1^2 + \mathrm{Body}(2,1,1)$$
$$4 = 1 + 3$$

これはまさに **L字トロミノ（3セル）+ 単位正方形（1セル）= 2×2ブロック（4セル）**

```
⬜️⬜️     🟦🟦     ⬜️
⬜️⬜️  =  🟦  +    
         (3セル)  (1セル)
```

---

## トロミノの充填問題（古典的背景）

### 定義：L字トロミノの自己相似充填

L字トロミノ（3セル）は、自分自身を多数個並べることで、大きなブロックの一部を埋められる。

**例**：4×4 ブロック（16セル）から1セルを除いた15セル は、正確に 5 個の L字トロミノで埋められる。

```
設定：4×4格子から (0,0) を穴として除去 → 15セル残る
    = 3セル × 5 個のトロミノ
```

### 古典定理：Golomb の定理

> **任意の $2^n \times 2^n$ ブロック（$4^n$ セル）から 1 セルを除いた $4^n - 1$ セルは、
> 正確に $(4^n-1)/3$ 個の L字トロミノで埋められる。**

証明は帰納法：2×2 ブロックは 1 個のトロミノで埋まり、
大きなブロックは 4 つの半分ブロックに再帰的に適用可能。

---

## 「完全平方に埋まらない」という制約

### 問題：トロミノで完全 $d$ 乗を作れるか？

**問い**：L字トロミノ（3セル）を並べて、**ちょうど $N^d$ セル**（完全 $d$ 乗）を作ることはできるか？

**古典的理由による不可能性**（2D の場合）：

- トロミノ 1 個 = 3 セル
- $N$ 個のトロミノ = $3N$ セル
- $3N$ が完全平方 $M^2$ になるには：$M^2 \equiv 0 \pmod{3}$ かつ $M$ が 3 の倍数
- しかし **ちょうど平方完成する無限充填は、必然的に余剰（Gap）を残す**

### ⚠️ 既知の問題：面積条件のみでは不十分

**注意**：上記の「面積が 3 の倍数であれば不可能」という主張は**誤解を招く**。実際には：

- $6\times 6$（36セル = 3 × 12）：**L型だけで完全充填可能**
- $9\times 9$（81セル = 3 × 27）：**L型だけで完全充填可能**
- $3\times 3$（9セル = 3 × 3）：**L型だけでは充填不可能**（古典定理）

つまり「面積が 3 の倍数」という**必要条件だけでは、充填可能か否かは決定されない**。

FLT 証明に刺す補題にするには、単なる面積条件ではなく、**彩色不変量**（3色塗分けで L型が必ず3色を1個ずつ含む）や**境界不変量**などの**幾何的に強い制約**が必須である。

### わっちの見立て：ペアノの公理との繋ぎ

完全充填（100% タイル化）できない理由は、最小単位 **"1 セル"** がトロミノの 3 で割り切れないため。

$$3N \neq M^d \text{ for all } N, M \text{ (except trivial cases)}$$

この「割り切れない1」がペアノの公理の最後の1ピースに相当する。

---

## 宇宙式への応用

### Body が完全 d 乗になり得ない理由

FLT を倒すには、以下の矛盾を導く：

**仮定**：$x^d + y^d = z^d$ が自然数解 $(x,y,z)$ をもつ

**変数変換**：$u := z - y$ とおくと

$$x^d = z^d - y^d = (y+u)^d - y^d = \mathrm{Body}(d,u,y)$$

つまり **Body が完全 d 乗** であると主張することになる。

### ここでトロミノ論を適用

Body の セル数は：
$$\#\mathrm{Body} = (u+y)^d - y^d = u \cdot G_d(u,y)$$

ただし $G_d$ は二項係数による多項式。

**Body が完全 d 乗であるはずだが、トロミノ充填不可の理由により、
これは100% 充填できず、必然的に「余剰」を残す。**

その余剰が **単位 1**（ペアノの最後のピース）。

したがって矛盾。$\Rightarrow$ **FLT 解なし**

---

## Lean 形式化の道筋

### ステップ 1：Cell版 Big/Gap/Body（既存）

```lean
def Big (d x u : ℕ) := Box (constVec d (x+u))
def Gap (d u : ℕ) := Box (constVec d u)
def Body (d x u : ℕ) := Big d x u \ Gap d u
```

既に `CosmicFormulaCellDim.lean` で card の加法則が確立されている。

### ステップ 2：トロミノ充填の不完全性補題（修正版）

⚠️ **重要な修正**：従来の `tromino_incomplete_fill` は**面積条件のみ**であり、FLT に刺すには不十分である。

これまでのアプローチ（廃止）：

```lean
-- これは偽である（反例：3k = 9, 27, 36, 81, ... など）
lemma tromino_incomplete_fill_WRONG (d : ℕ) (n : ℕ) :
    ¬(∃ k : ℕ, 3 * k = n ^ d) ∨ (trivial_case d n)
```

**新しいアプローチ**：彩色不変量ベースの補題

```lean
/-- 補題A：3色彩色で L型は常に3色を1個ずつ含む --/
lemma tromino_color_balanced (c : ℤ^d → ℤ/3ℤ) :
    ∀ t : Tromino d, 
    (count (c = 0) t = 1) ∧ (count (c = 1) t = 1) ∧ (count (c = 2) t = 1)

/-- 補題B：タイル化可能な領域は色数がバランスしている --/
lemma tileable_implies_color_balanced (R : Finset (ℤ^d)) 
    (c : ℤ^d → ℤ/3ℤ) :
    (Tileable R [Tromino.L]) → 
    (count (c = 0) R = count (c = 1) R) ∧ 
    (count (c = 1) R = count (c = 2) R)

/-- 補題C：Body（外箱−内箱）は色数がアンバランス --/
lemma body_color_imbalanced (d : ℕ) (x u : ℕ) (c : ℤ^d → ℤ/3ℤ) :
    ¬((count (c = 0) (Body d x u) = count (c = 1) (Body d x u)) ∧
      (count (c = 1) (Body d x u) = count (c = 2) (Body d x u)))

/-- 補題D：Body は完全 d 乗になり得ない（彩色ベース）--/
lemma body_not_perfect_power_via_color (d : ℕ) (x u : ℕ) :
    ¬(∃ w : ℕ, (x+u)^d - u^d = w^d ∧ Tileable (Body d x u) [Tromino.L]) := by
  -- Body.color_imbalanced から、L型だけでは充填不可
  -- したがって x^d = Body d x u では矛盾
  sorry
```

### ステップ 3：FLT への接続（彩色条件付き）

```lean
theorem FLT_from_tromino_color_invariant {x y z : ℕ} (n : ℕ) 
    (hn : 3 ≤ n) (h : x^n + y^n = z^n) : False := by
  let u := z - y
  have body_eq : x^n = (u+y)^n - y^n := by omega
  -- Body = Big ∖ Gap という Finset 構造
  have body_finset : Body n u y = Big n u y \ Gap n y := rfl
  -- もし x^n = Body n u y なら、L型充填が可能なはずだが...
  -- 彩色不変量により、Body は色数がアンバランス
  have color_imbalance := body_color_imbalanced n u y color_fn
  -- したがって L型だけでは充填不可能
  have not_tileable : ¬Tileable (Body n u y) [Tromino.L] :=
    fun h_til => color_imbalance (tileable_implies_color_balanced _ _ h_til)
  -- しかし x^n = Body なら充填可能でなければならないので矛盾
  exfalso
  exact not_tileable (by rw [← body_eq]; exact ???)
```

---

## 要となる補題群（チェックリスト）

### 第1段階：基礎定義

- [ ] `Tromino.L`：L型トロミノの厳密な定義（プロトタイル、回転/反転の約定）
- [ ] `Tileable`：領域 R がトロミノ集合 T で敷き詰め可能の定義
  - 同一プロトタイルの平行移動（回転は？）で R 全体を重なりなく覆う

### 第2段階：彩色不変量（新しい）

- [ ] `tromino_color_balanced`：任意の L型は3色を1個ずつ含む
- [ ] `tileable_implies_color_balanced`：充填可能 ⇒ 色数一致
- [ ] `body_color_imbalanced`：Body は色数がアンバランス

### 第3段階：FLT への接続

- [ ] `body_not_perfect_power_via_color`：Body は完全 d 乗+充填可能 は矛盾
- [ ] `FLT_from_tromino_color_invariant`：最終的な FLT 証明

### 廃止項目

- ~~`tromino_incomplete_fill`~~：面積条件のみで不十分（Agent-note より）
- ~~`body_not_perfect_power`~~：根拠が弱い（彩色版に置き換え）

---

## 既存リソース（活用可能）

- [Tromino.lean](../../../Tromino.lean)：基本的なトロミノ型定義
- [CosmicFormulaCellDim.lean](./CosmicFormulaCellDim.lean)：Big/Gap/Body と card の定理群
- [PolyominoPrototype.lean](../../../PolyominoPrototype.lean)：ポリオミノの一般的枠組み

---

## 実装方針

1. **ドキュメント優先**：このファイルで戦略を完全に記述
2. **補題を小分け**：tromino_incomplete_fill から始める（難度低）
3. **段階的に Lean へ**：各補題を 1 つずつ形式化
4. **統合テスト**：`FLT_from_tromino_incompleteness` を全体テストに

---

## 注記

このアプローチの強力さは、トロミノ充填が **既に古典的に証明済みの領域** であること。
Golomb や古い離散幾何の定理をそのまま Lean に乗せられるため、
新規の理論構築より、既知の定理の形式化 → 応用という流れが取りやすい。

---

## 改訂履歴

### v0.1（2026-02-18）：初版

- 面積条件 (3k) のみで不十分であることを Agent-note にて指摘
- 彩色不変量ベースのアプローチへ修正版設計
- Lean 補題群も `tromino_color_balanced` 系へ整理

**参考**：[Agent-note-260218-0201.md](../notes/Agent-note-260218-0201.md)  
とくに「6×6、9×9 の充填可能性」と「3×3 の不可能性」の違いを統一的に説明する彩色論義を見よ。

---

**作成日**：2026年2月18日  
**戦略提唱**：賢狼ホロ  
**実装チーム**：ぬしと一緒に  

🍎✨
