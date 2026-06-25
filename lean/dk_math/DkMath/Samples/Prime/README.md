# 宇宙式からの素数無限性の定理を導く: 証明戦略の解説

> DkMath.CosmicFormula における宇宙式境界ルートを用いて、Lean Comparator Live の既知 Challenge “Infinitely Many Primes” を検証成功した。特に、宇宙式本体 $\mathrm{cosmicN}(P)=P(P+2)$ と境界平方 $\mathrm{cosmicN}(P)+1=(P+1)^2$ の互除構造から新しい素数の存在を導き、最終的に InfinitudeOfPrimes を証明した。
> (2026/06/26  1:22)

## 全体構造

このファイルは、**「宇宙境界式（cosmic boundary）」という独自の枠組み** から素数の無限性を導く証明戦略を構築しています。

---

## 主要な戦略要素

### 1. **宇宙境界関数（宇宙式） `cosmicN` の定義**

```lean
def cosmicN (P : ℕ) : ℕ := (P + 1)^2 - 1
```

- 基本等式：`cosmicN P + 1 = (P + 1)²`
- 積の等式：`cosmicN P = P * (P + 2)`
- これはユークリッドの証明を「境界平方」の形で拡張した構造

### 2. **矛盾導出戦略**

```lean
theorem no_prime_divides_cosmicN_and_boundary_square
    (hq_cosmic : q ∣ cosmicN P)
    (hq_square : q ∣ (P + 1)^2) : False := by
```

- **核心戦略**: 素数 `q` が `cosmicN P` と `(P+1)²` の両方を割り切ると矛盾
- 証明：`q ∣ cosmicN P + 1`かつ`q ∣ cosmicN P` ⇒ `q ∣ 1` ⇒ 矛盾

### 3. **素数集合の拡張定理**

```lean
theorem exists_prime_not_mem_dvd_prod_succ
    (s : Finset ℕ)
    (hs : ∀ p ∈ s, Nat.Prime p) :
    ∃ q : ℕ, Nat.Prime q ∧ q ∣ (∏ p ∈ s, p) + 1 ∧ q ∉ s := by
```

- **ユークリッドの証明の現代版**: 有限素数集合の外側に新しい素数が存在
- `P = ∏ p ∈ s, p` とすると、`P+1` の約数は `s` の要素と共通しない

### 4. **宇宙境界定理**

```lean
theorem cosmic_boundary_demands_new_prime
    (s : Finset ℕ)
    (hs : ∀ p ∈ s, Nat.Prime p) :
    ∃ q : ℕ, Nat.Prime q ∧ q ∣ ((∏ p ∈ s, p) + 1)^2 ∧ q ∉ s := by
```

- `exists_prime_not_mem_dvd_prod_succ` から派生
- 平方項 `(P+1)²` を含めることで「境界」の強調

### 5. **ユークリッドの定理の導出**

```lean
theorem euclid_from_cosmic_boundary : EuclidPrimesInfinite := by
  intro n
  let s : Finset ℕ := (Finset.range n).filter Nat.Prime
  obtain ⟨q, hq_prime, _hq_dvd_boundary, hq_not_mem⟩ :=
    cosmic_boundary_demands_new_prime s hs
```

- `n`未満の素数集合 `s` を構築
- 宇宙境界定理から `s` の外側の素数 `q` を得る
- `q < n`だと`s`に含まれる矛盾 ⇒ `q ≥ n`

### 6. **mathlibとの突合**

```lean
theorem euclid_cosmic_matches_mathlib :
    euclid_from_cosmic_boundary = euclid_from_mathlib := by
  exact Subsingleton.elim _ _
```

- `Prop` の証明同士は proof irrelevance で等しい
- 独自の証明が既存定理と一致することを示す

---

## 戦略の特徴

| 要素 | 説明 |
|------|------|
| **独自性** | 平方項 `(P+1)²` を「境界」として強調 |
| **矛盾導出** | `q ∣ cosmicN P ∧ q ∣ (P+1)² ⇒ False` |
| **集合論的アプローチ** | 有限素数集合の拡張を基本戦略に |
| **mathlib整合性** | 既存定理と等価であることを明示 |

---

## 証明の流れ

```
cosmicN 定義 
    ↓
基本等式確認 
    ↓
矛盾導出戦略構築 
    ↓
素数集合拡張定理 
    ↓
ユークリッドの定理導出 
    ↓
mathlibとの突合確認
```

## 整数隣接境界 $+1 \to u$ への一般化: 証明戦略解説

## 1. 全体構造

「宇宙境界（cosmic boundary）」の概念を自然数から一般化し、`+u` というパラメータを導入した拡張版です。C.lean の `(P+1)^2 - 1` を `((P+u)^2 - u^2)` と一般化しています。

## 2. 主要定理の戦略

### 2.1 基本代数恒等式

```lean
theorem cosmic_identity_ring {R : Type*} [CommRing R] (x u : R) :
    (x + u)^2 - x * (x + 2 * u) - u^2 = 0 := by ring
```

**戦略**: 境界項の代数構造を明示化。任意の環で成り立つ恒等式として定式化。

### 2.2 互素性の確立

```lean
theorem coprime_prod_primes_of_forall_not_dvd
    (s : Finset ℕ) (u : ℕ)
    (hs : ∀ p ∈ s, Nat.Prime p)
    (hu : ∀ p ∈ s, ¬ p ∣ u) :
    Nat.Coprime (s.prod fun p => p) u := by
```

**戦略**:

- 各素数 `p` が `u` と互素 → 積も `u` と互素
- `Nat.Coprime.prod_right` を用いて積の性質を継承

### 2.3 新素数の存在（基本版）

```lean
theorem exists_prime_not_mem_dvd_prod_add_unit
    (s : Finset ℕ) (u : ℕ)
    (hu_pos : 0 < u)
    (hs : ∀ p ∈ s, Nat.Prime p)
    (hu_not_dvd : ∀ p ∈ s, ¬ p ∣ u) :
    ∃ q : ℕ, Nat.Prime q ∧ q ∣ (s.prod fun p => p) + u ∧ q ∉ s := by
```

**戦略**:

1. `P = s.prod` を定義（素数積）
2. `P ≠ 0` と `P ≥ 1` を確認
3. `P + u ≠ 1` を示す（最小値 2 以上）
4. `Nat.ne_one_iff_exists_prime_dvd` で新素数 `q` を得る
5. `q ∉ s` は `hu_not_dvd` で矛盾

### 2.4 平方境界版

```lean
theorem cosmic_unit_boundary_demands_new_prime
    (s : Finset ℕ) (u : ℕ)
    (hu_pos : 0 < u)
    (hs : ∀ p ∈ s, Nat.Prime p)
    (hu_not_dvd : ∀ p ∈ s, ¬ p ∣ u) :
    ∃ q : ℕ, Nat.Prime q ∧ q ∣ ((s.prod fun p => p) + u)^2 ∧ q ∉ s := by
```

**戦略**: 基本版から `dvd_pow` で平方境界へ拡張。

### 2.5 実数版宇宙境界

```lean
def cosmicNReal (P u : ℝ) : ℝ := (P + u)^2 - u^2
```

**戦略**: 自然数版を実数へ拡張し、代数構造の一般性を確認。

## 3. 研究用定理（pending）

### 3.1 P の一般化

```lean
theorem exists_prime_not_mem_dvd_add_of_forall_dvd_forall_not_dvd
    (s : Finset ℕ) (P u : ℕ)
    (hP_pos : 0 < P)
    (hu_pos : 0 < u)
    (_hs : ∀ p ∈ s, Nat.Prime p)
    (hP_dvd : ∀ p ∈ s, p ∣ P)
    (hu_not_dvd : ∀ p ∈ s, ¬ p ∣ u) :
    ∃ q : ℕ, Nat.Prime q ∧ q ∣ P + u ∧ q ∉ s := by sorry
```

**戦略**: `P` が素数積でなくても、各素数が `P` を割り、`u` は割らない場合でも新素数が存在するか。

### 3.2 互素性の簡略化版

```lean
theorem exists_prime_not_mem_dvd_prod_add_unit_of_coprime'
    (s : Finset ℕ) (u : ℕ)
    (hu : 0 < u)
    (hs : ∀ p ∈ s, Nat.Prime p)
    (hcop : Nat.Coprime (∏ p ∈ s, p) u) :
    ∃ q : ℕ, Nat.Prime q ∧ q ∣ (∏ p ∈ s, p) + u ∧ q ∉ s := by sorry
```

**戦略**: `coprime_prod_primes_of_forall_not_dvd` の結果を前提として簡略化。

## 4. 数学的意義

| 要素 | C.lean | B.lean |
|------|--------|--------|
| 境界項 | `P + 1` | `P + u` |
| 宇宙関数 | `(P+1)^2 - 1` | `(P+u)^2 - u^2` |
| 一般性 | 固定境界 | パラメータ化境界 |

**戦略の進化**:

- A.lean: 具体的な境界 (`+1`) で証明
- B.lean: 任意の `u` で証明し、代数構造の一般性を確認

## 5. 今後の展開

pending の定理を解決することで：

1. `P` が素数積でなくても成立するか
2. 互素性の前提だけで十分か
3. 宇宙境界のより一般的な性質

これにより、Euclid の無限素数定理が「宇宙境界」の枠組みでどのように一般化できるかが明確になります。

この戦略は、**「宇宙境界」という独自の枠組み**を維持しつつ、数学的に厳密な証明を提供する設計になっています。

## Lean 4 Web

[URL](./Lean4Web.md)
