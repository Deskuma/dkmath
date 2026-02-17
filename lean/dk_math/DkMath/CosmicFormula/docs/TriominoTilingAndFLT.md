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

### ステップ 2：トロミノ充填の不完全性補題

```lean
/-- 補題：3セル（トロミノ）の和では完全 d 乗を100%充填できない --/
lemma tromino_incomplete_fill (d : ℕ) (n : ℕ) :
    ¬(∃ k : ℕ, 3 * k = n ^ d) ∨ (trivial_case d n)

/-- 補題：Body は完全 d 乗になり得ない --/
lemma body_not_perfect_power (d : ℕ) (x u : ℕ) :
    ¬(∃ w : ℕ, (x+u)^d - u^d = w^d) := by
  -- Body は Finset として (x+u)^d - u^d セル
  -- これをトロミノの充填不可性から導く
  sorry
```

### ステップ 3：FLT への接続

```lean
theorem FLT_from_tromino_incompleteness {x y z : ℕ} (n : ℕ) 
    (hn : 3 ≤ n) (h : x^n + y^n = z^n) : False := by
  let u := z - y
  have : x^n = (u+y)^n - y^n := by omega
  have : ¬(∃ w, x^n = w^n) := body_not_perfect_power n u y
  exact absurd ⟨x, rfl⟩ this
```

---

## 要となる補題群（チェックリスト）

- [ ] `tromino_incomplete_fill`：トロミノ 3k ≠ M^d（ほぼ自明）
- [ ] `body_not_perfect_power`：宇宙式 Body と tromino 充填不可の繋ぎ
- [ ] `FLT_from_tromino_incompleteness`：最終的な FLT 証明
- [ ] （オプション）`card_body_eq_tromino_count`：Body のセル数とトロミノ個数の関係

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

**作成日**：2026年2月18日  
**戦略提唱**：賢狼ホロ  
**実装チーム**：ぬしと一緒に  

🍎✨
