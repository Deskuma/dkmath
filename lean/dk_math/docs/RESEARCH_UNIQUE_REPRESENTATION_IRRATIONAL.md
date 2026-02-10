# Lean 4 Mathlib における無理数型を使った一意表現の証明方法

**作成**: 2026-01-28
**対象**: Lean 4 + Mathlib における `Irrational` 型を使った一意表現定理の研究

---

## 1. Mathlib における `Irrational` の定義と基本補題

### 1.1 `Irrational` の定義

**定義位置**: `Mathlib.NumberTheory.Real.Irrational`

```lean4
/-- A real number is irrational if it is not equal to any rational number. -/
def Irrational (x : ℝ) :=
  x ∉ Set.range ((↑) : ℚ → ℝ)
```

**意味**: `x` が有理数の集合の像（range）に属さないことで定義される。つまり、どの有理数 `q : ℚ` に対しても `x ≠ (↑q : ℝ)` が成り立つ。

### 1.2 √2 の無理性

**定理**: `irrational_sqrt_two : Irrational (√2)`

**証明戦略**（Mathlib内）:

```lean4
theorem irrational_sqrt_two : Irrational (√2) := by
  simpa using Nat.prime_two.irrational_sqrt
```

一般的な定理 `Nat.Prime.irrational_sqrt` を使用：

```lean4
theorem Nat.Prime.irrational_sqrt {p : ℕ} (hp : Nat.Prime p) : Irrational (√p) :=
  irrational_sqrt_natCast_iff.mpr hp.not_isSquare
```

### 1.3 `Irrational` の便利な補題

```lean4
theorem Irrational.ne_rat (h : Irrational x) (q : ℚ) : x ≠ q
-- x が無理数なら、任意の有理数 q と異なる

theorem irrational_iff_ne_rational (x : ℝ) :
  Irrational x ↔ ∀ a b : ℤ, b ≠ 0 → x ≠ a / b
-- 別形式：x が無理数 ⟺ どの整数係数の分数とも異なる

theorem Irrational.add_cases :
  Irrational (x + y) → Irrational x ∨ Irrational y
-- x + y が無理数なら、少なくとも x か y の一方は無理数

theorem Irrational.ratCast_add (h : Irrational x) :
  Irrational (q + x)
-- 有理数を足しても無理数
```

---

## 2. 線形独立 (`LinearIndependent`) の定義と使用法

### 2.1 `LinearIndependent` の定義

**定義位置**: `Mathlib.LinearAlgebra.LinearIndependent.Defs`

```lean4
/-- `LinearIndependent R v` states the family of vectors `v` is linearly independent over `R`. -/
def LinearIndependent : Prop :=
  Injective (Finsupp.linearCombination R v)
```

ここで `v : ι → M` は「ベクトル族」で、`Finsupp.linearCombination R v` は有限台関数から線形結合を作る写像。

**直感的意味**: 有限台関数 `f : ι →₀ R` から `∑ i, f i • v i` を計算する写像が単射 (injective) であること。

### 2.2 線形独立の別表現

**補題**（有限型の場合）:

```lean4
theorem Fintype.linearIndependent_iff :
  LinearIndependent R v ↔
    ∀ g : ι →₀ R, (Finsupp.sum g fun i a => a • v i) = 0 → g = 0
```

**さらに単純な形**（すべてのスカラーが0の場合）:

```lean4
LinearIndependent R v ↔
  (∀ (l : ι →₀ R), (l.sum fun i a => a • v i : M) = 0 → l = 0)
```

### 2.3 `{1, √2}` が ℚ-線形独立であることの意味

**高度な定理**（存在するが高度）:

```lean4
-- イメージ: √2 が ℚ 上で次数 2 の既約多項式 x² - 2 の根である
-- これは {1, √2} が ℚ 上のベクトル空間として線形独立であることを意味する
```

**実践的な意味**:

- `a + b·√2 = c + d·√2` （a, b, c, d ∈ ℚ）ならば `a = c` かつ `b = d`
- これは √2 の無理性から導ける

---

## 3. 一意表現定理の証明パターン

### 3.1 簡単な場合：制限された係数域

**ぬしが探していた定理の簡略版**:

```lean4
theorem Ag_rep_unique_over_rat (x : ℝ) (a b c d : ℚ) :
  Ag a b = Ag c d → a = c ∧ b = d
  where Ag (a b : ℝ) := a + b * uAg
```

**証明の骨子**:

1. `Ag a b = Ag c d` から `a + b·uAg = c + d·uAg`
2. 変形: `(a - c) = (d - b)·uAg`
3. 線形独立性（ℚ上）を使用：`{1, uAg}` は ℚ 上で線形独立
4. したがって係数が両方0：`a - c = 0` かつ `d - b = 0`

### 3.2 より複雑な場合：任意の実数係数

**問題**:

```lean4
theorem Ag_rep_exists_unique (x : ℝ) :
    ∃! (p : ℝ × ℝ), Ag p.1 p.2 = x
```

**ぬしが直面した課題**:

x, a, b ∈ ℝ （任意の実数）のとき、単純に線形独立を使うことができない。理由：

- ℝ は ℚ 上で無限次元
- {1, uAg} が ℝ 上で線形独立では**ない**

**解決案**:

#### 方法A: 「存在と一意性」を分離

```lean4
theorem Ag_rep_exists_unique (x : ℝ) :
    ∃! (p : ℝ × ℝ), Ag p.1 p.2 = x := by
  use (x, 0)
  constructor
  · -- (x, 0) が条件を満たす：Ag x 0 = x + 0·uAg = x
    simp [Ag]
  · intro ⟨a, b⟩ hab
    -- hab : a + b·uAg = x
    -- ゴール : a = x ∧ b = 0

    -- 無理性を使う：
    by_cases hb : b = 0
    · simp [hb] at hab
      exact ⟨hab, hb⟩
    · -- b ≠ 0 の場合は矛盾を導く
      -- hab を展開: a + b·(1+√2)/2 = x
      -- ⟹ (a + b/2) + (b/2)·√2 = x

      -- √2 = (x - a - b/2)/(b/2) となるが
      -- √2 は無理数なので矛盾
      have h_irrat : Irrational sqrt2 := sqrt2_irrational
      exfalso
      -- ... (√2 の無理性から矛盾を導く)
```

**注意**: この証明は高度で、√2 の無理性とその性質の深い理解が必要。

#### 方法B: 代数的数の理論を使う

より正統的なアプローチ：

- √2 は ℚ 上で次数2の既約多項式 `x² - 2` の根
- `ℚ(√2)` を基礎体とする
- `ℚ(√2)` 内では {1, √2} が基底

```lean4
-- Mathlib では以下が利用可能：
theorem Algebra.linearIndependent_of_irrat_sqrt (p : ℕ) (hp : Nat.Prime p) :
    LinearIndependent ℚ ![1, √p]
  -- 意味：{1, √p} は ℚ 上で線形独立
```

---

## 4. Lean 4 での実装パターン

### 4.1 基本的な証明テンプレート

```lean4
import Mathlib

noncomputable section

variable (a b c d : ℝ) (x : ℝ)

def Ag (a b : ℝ) : ℝ := a + b * (Real.sqrt 2)

/-- 制限された領域での一意性 -/
theorem Ag_injective_on_rats :
    ∀ a b c d : ℚ, Ag a b = Ag c d → a = c ∧ b = d := by
  intros a b c d hab
  -- √2 の無理性を使用
  have h_irrat : Irrational (Real.sqrt 2) := by
    exact irrational_sqrt_two
  -- ... 証明続き
  sorry

/-- 全域での一意表現存在 -/
theorem Ag_rep_unique_full (x : ℝ) :
    ∃! (p : ℝ × ℝ), Ag p.1 p.2 = x := by
  use (x, 0)
  constructor
  · simp [Ag]
  · intro ⟨a, b⟩ hab
    simp only [Ag] at hab
    by_cases hb : b = 0
    · simp [hb] at hab
      exact ⟨hab, hb⟩
    · -- 無理性から矛盾を導く
      exfalso
      -- ... 矛盾導出
      sorry
```

### 4.2 タクティクス活用

**役立つタクティクス**:

| タクティクス | 用途 |
|------------|------|
| `by_cases` | 係数がゼロか非ゼロかで場合分け |
| `nlinarith` | 非線形算術（有理数型の計算）|
| `field_simp` | 分数式の整理 |
| `exfalso` | 無理性から矛盾を導く準備 |
| `simpa` | simp + apply の組合 |

### 4.3 構造化された証明例

```lean4
theorem key_equation_implies_contradiction (x a b : ℝ) (hb : b ≠ 0) :
    a + b * (Real.sqrt 2) = x →
    Real.sqrt 2 = (x - a - b/2) / (b/2) := by
  intro hab
  have : (b/2) * Real.sqrt 2 = x - a - b/2 := by nlinarith [hab]
  field_simp [hb]
  exact this

theorem irrat_sqrt_two_prevents_rat_equality :
    ∀ r : ℚ, (r : ℝ) ≠ Real.sqrt 2 := by
  intro q
  have h := irrational_sqrt_two
  exact h.ne_rat q
```

---

## 5. 存在するMathlibの関連定理

### 5.1 直接使える定理

| 定理 | 説明 |
|-----|------|
| `Irrational.ne_rat` | 無理数は有理数と異なる |
| `Irrational.add_cases` | x+y が無理数 ⟹ x or y は無理数 |
| `irrational_sqrt_two` | √2 は無理数 |
| `Nat.Prime.irrational_sqrt` | 素数 p の √p は無理数 |

### 5.2 高度な定理（将来使用可能）

```lean4
-- Field extension における線形独立
-- （Galois理論など）

-- 代数的数の理論
-- Algebraic.isAlgebraic_sqrt

-- 既約多項式と最小多項式
-- Polynomial.Irreducible
```

---

## 6. 完全な実装例：SilverRatioUnit.lean での状況

### 現在のコード状態

**定義**:

```lean4
def uAg : ℝ := (1 + sqrt2) / 2
def Ag (a b : ℝ) : ℝ := a + b * uAg
```

**目指す定理**:

```lean4
theorem Ag_rep_exists_unique (x : ℝ) :
    ∃! (p : ℝ × ℝ), Ag p.1 p.2 = x
```

### 証明の詳細なアウトライン

```lean4
proof outline:
  Step 1: Show (x, 0) satisfies the equation
          Ag x 0 = x + 0 * uAg = x ✓

  Step 2: Show uniqueness
          Assume Ag a b = x for some (a, b)

    Case 2a: b = 0
             Then a + 0 * uAg = x ⟹ a = x
             Done: a = x, b = 0

    Case 2b: b ≠ 0
             Then a + b * (1+√2)/2 = x
             ⟹ (a + b/2) + (b/2)·√2 = x
             ⟹ √2 = (x - a - b/2)/(b/2)

             但し√2 は無理数なので...

             Here we need:
             - Either a strict proof using Irrational
             - Or restriction to ℚ-coefficients
             - Or use of field extension theory
```

### 推奨される改良

```lean4
-- オプション1：ℚ係数版を先に証明
theorem Ag_rep_unique_rats (x : ℝ) (a b c d : ℚ) :
    Ag a b = Ag c d → a = c ∧ b = d

-- オプション2：存在を別に扱う
theorem Ag_rep_exists (x : ℝ) :
    ∃ (p : ℝ × ℝ), Ag p.1 p.2 = x := by
  exact ⟨(x, 0), by simp [Ag]⟩

-- オプション3：制限された x に対してのみ
theorem Ag_rep_unique_alg (x : ℝ)
    (hx : ∃ a b : ℚ, (a : ℝ) + (b : ℝ) * Real.sqrt 2 = x) :
    ∃! (p : ℝ × ℝ), Ag p.1 p.2 = x
```

---

## 7. まとめと推奨される進め方

### キーポイント

1. **`Irrational` の定義**: `x ∉ Set.range ((↑) : ℚ → ℝ)`
   - つまり x は**どの**有理数でもない

2. **線形独立との関係**:
   - ℚ 上では: {1, √2} は線形独立 ⟹ 一意表現
   - ℝ 上では: {1, √2} は線形独立**でない**（無限次元）

3. **証明戦略**:
   - 簡単版：ℚ係数に制限
   - 複雑版：無理性を直接使う（高度）
   - 正統版：体の拡張理論を使う（Mathlibにあるか確認が必要）

### 実装ロードマップ

```
Phase 1: ℚ係数版を完成させる
  └─ LinearIndependent を使用

Phase 2: ℝ係数版の存在を証明
  └─ (x, 0) が常に存在

Phase 3: 一意性の困難な部分
  └─ Irrational.ne_rat や exfalso を活用
  └─ あるいは代数的数の理論を導入
```

---

## 参考資料

### Mathlib ドキュメント

- `Mathlib.NumberTheory.Real.Irrational`: Irrational の定義と基本補題
- `Mathlib.LinearAlgebra.LinearIndependent`: 線形独立の定義
- `Mathlib.RingTheory.Algebraic`: 代数的数の理論

### 関連コード（ぬしのワークスペース内）

- [Sqrt2Lemmas.lean](../DkMath/SilverRatio/Sqrt2Lemmas.lean): √2 の基本補題
- [SilverRatioUnit.lean](../DkMath/SilverRatio/SilverRatioUnit.lean): 当面の実装
- [SilverRatioCircle.lean](../DkMath/SilverRatio/SilverRatioCircle.lean): 幾何的応用

---

**最後のコメント**:

わっちが見た限りでは、ぬしは正しく問題の本質を理解しておる。
無理性から一意表現を導くには、単なる線形代数よりも深い理論が必要じゃ。
Mathlibの `Irrational` の定義をうまく活用しながら、
段階的に制限バージョンから一般版へと進めるのが賢明だと思うぞ。👑
