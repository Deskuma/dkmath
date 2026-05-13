# Real / Log Route Plan

## 目的

この設計書は、N/Q 版で確立した finite ratio-style route を、実数値 weight と対数候補へ拡張するための実装計画である。

N/Q 版では、次の形が Lean 上で通っている。

```text
c(n, p) = A(p) / B(n)        with A B : ℕ -> ℚ
0 <= A(p)
0 < B(n)
Σ A(p(q)) <= B(n)
--------------------------------
sub-probability channel provider
weightedHitMass <= C
```

R 版では、この構造をまず `ℝ` に移し、その後で `A(p) = log p`, `B(n) = log n` を候補として接続する。

## 基本方針

実装は次の三層に分ける。

### Layer 1. Real ratio skeleton

まず `Real.log` を使わず、抽象的な実数値関数だけを扱う。

```lean
A B : ℕ -> ℝ
realRatioBasePrimeWeight A B n p = A p / B n
```

必要な仮定は N/Q 版と同型にする。

```text
∀ p, 0 <= A p
∀ n, 0 < B n
∀ n, Σ q in index(n), A(p(q)) <= B n
```

この層の目的は、`ℚ` 版の theorem shape を `ℝ` でも再現できるか確認することである。

### Layer 2. Real channel bridge

既存の channel / weight provider は現在 `ℚ` weight を中心に作られている。

R 版では、次のどちらを選ぶかを先に決める必要がある。

1. 既存 API を `ℚ` のまま保ち、実数 route は別 API として試作する。
2. weight carrier を型パラメータ化し、`ℚ` / `ℝ` の両方に対応する。

現時点の推奨は 1 である。

理由は、既存 N/Q 版はすでに多数の theorem-facing names を持ち、安定しているためである。いきなり型パラメータ化すると、finite hitting から weighted path family まで広範囲に影響する。まずは `Real` 用の薄い parallel skeleton を作り、定理の形を確認する方が安全である。

### Layer 3. Log candidate

real ratio skeleton が通った後で、次を候補として入れる。

```text
A(p) = Real.log p
B(n) = Real.log n
```

この層では、以下の補題が必要になる。

```text
p >= 1  -> 0 <= log p
n > 1   -> 0 < log n
q | n   -> log q <= log n
Π p(q) <= n  または  Σ log p(q) <= log n
```

特に budget

```text
Σ q in index(n), log p(q) <= log n
```

は自明ではない。prime-power labels が互いにどのように選ばれているか、また同じ base prime を重複して読むかを制御する必要がある。

## Phase ナンバリング仕様

R 版の実装 Phase は、この設計書から新しい番号体系で管理する。

```text
Phase-R001
Phase-R002
...
Phase-R999
```

以前の案にあった `Phase RH`, `Phase RI`, `Phase RJ`, `Phase RK`, `Phase RL` は廃止する。N/Q 版の `BH` から `RH` へ飛ぶと、作業単位と記録番号の対応が読みづらくなるためである。

以後、R 版実装とその設計更新は `R001` から順に番号を振る。レビュー番号は従来通り `review-060.md` 以降を参照するが、レビュー番号と Phase 番号は独立に扱う。

## 実装 Phase 案

### Phase-R001. Real weight vocabulary

目的:

- 実数値 weight の最小 vocabulary を作る。
- 既存 `ℚ` API を壊さず、R 版用の名前空間を分ける。

候補ファイル:

```text
DkMath/NumberTheory/PrimitiveSet/RealWeight.lean
```

候補定義:

```lean
def RealBasePrimeToyWeight (c : ℕ -> ℕ -> ℝ) : Prop :=
  ∀ n p, 0 <= c n p

def realRatioBasePrimeWeight (A B : ℕ -> ℝ) : ℕ -> ℕ -> ℝ :=
  fun n p => A p / B n
```

完了条件:

- `realRatioBasePrimeWeight` の非負性が、`0 <= A p` と `0 < B n` から出る。
- `Real.log` はまだ使わない。

### Phase-R002. Real finite budget lemma

目的:

- finite sum に対して、ratio-style budget から sub-probability 型の有限和不等式を得る。

候補 theorem shape:

```lean
theorem real_ratio_sum_le_one
    (hA : ∀ p, 0 <= A p)
    (hB : 0 < B n)
    (hbudget : (index.sum fun q => A (pOf q)) <= B n) :
    (index.sum fun q => A (pOf q) / B n) <= 1
```

完了条件:

- `Finset.sum_div` と `div_le_iff₀` 相当の `ℝ` 補題で閉じる。
- channel API へ接続する前に、純粋な有限和補題として安定させる。

### Phase-R003. Real channel prototype

目的:

- `ℚ` の `WeightProvider` と混ぜず、`ℝ` weight provider の薄い prototype を作る。

候補ファイル:

```text
DkMath/NumberTheory/PrimitiveSet/RealWeightedPath.lean
```

候補定義:

```lean
structure RealWeightProvider (ι : Type _) where
  index : Finset ι
  weight : ι -> ℝ
  weight_nonneg : ∀ i, i ∈ index -> 0 <= weight i
```

候補 predicate:

```lean
def RealWeightProvider.SubProbability (P : RealWeightProvider ι) : Prop :=
  P.index.sum P.weight <= 1
```

完了条件:

- N/Q 版の theorem shape と対応する最小 API ができる。
- 既存 theorem 群には手を入れない。

### Phase-R004. Log positivity

目的:

- `Real.log` を使うための正値性補題を局所化する。

候補 theorem:

```text
1 <= p -> 0 <= Real.log p
1 < n  -> 0 < Real.log n
```

注意:

- Lean では `Nat` から `ℝ` への coercion が絡む。
- `p = 1` では `log 1 = 0` なので numerator 非負性には使える。
- denominator は割るため `n > 1` が必要。

完了条件:

- `Real.log` の正値性を、後続の ratio theorem に渡せる形で theorem 名にする。

### Phase-R005. External log budget

目的:

- `Σ log p(q) <= log n` をまず外部仮定として受け取り、log-ratio finite sum bound に接続する。

実装済み:

- `RealLogBudget`
- `real_log_ratio_sum_le_one`

### Phase-R006. Log numerator nonnegativity on index

目的:

- `log p / log n` 型 weight を provider に載せる前段として、index 上の numerator 非負性を整理する。

実装済み:

- `RealLogNonnegOn`
- `real_log_nat_nonneg_on`

### Phase-R007. Log-ratio real provider

目的:

- `log (pOf q) / log n` 型の有限実数 weight を `RealWeightProvider` に載せる。
- 外部 `RealLogBudget` から provider の sub-probability を示す。

実装済み:

- `realLogRatioWeightProvider`
- `realLogRatioWeightProvider_subProbability`

### Phase-R008. Product route design for log budget

目的:

- `RealLogBudget I pOf n` を供給する方法を、いきなり prime-power route に戻らず product budget route として分解する。

候補アプローチ:

1. budget を外部仮定として受け取る。
2. selected base primes の積が `n` を割る、または `<= n` であることから導く。
3. prime-power label の重複制御を入れる。

現在の状態:

- 1 は Phase-R005 から Phase-R007 までで完了。
- 次は 2 を `RealLogBudget_of_product_le` 系の小補題群として設計する。
- 3 は product budget route が見えてから別 Phase で扱う。

理由:

- Erdos #1196 へ向かう本質は、log budget の構成にある。
- ここを channel API と同時に実装すると、責務が混ざる。

分解案:

1. 実数値の正の有限積に対して、`sum log = log prod` 型の補題を用意する。
2. `prod <= N` と `0 < prod`, `0 < N` から `log prod <= log N` を得る。
3. 1 と 2 を合成して、実数版の `sum log <= log N` を得る。
4. 自然数版 `pOf : ι -> ℕ`, `n : ℕ` へ戻し、`∀ q ∈ I, 1 ≤ pOf q` と product bound から `RealLogBudget I pOf n` を供給する。

初期実装では、4 へ急がず、1-3 を小さい real lemma として試す。

## リスク

### 1. 既存 API の型一般化が広すぎる

`ℚ` weight を `ℝ` に一般化したくなるが、これは影響範囲が大きい。最初は parallel prototype を推奨する。

### 2. `Real.log` の補題探索が重い

`Real.log`、自然数 coercion、正値性、単調性が絡むため、小さい補題を先に theorem 名で固定する。

### 3. budget が数学的本丸になる

`Σ log p(q) <= log n` は ratio route の単なる置換ではない。prime-power label の選び方、重複、divisibility の情報が必要になる。

## N/Q 版との対応表

| N/Q 版 | R 版候補 |
| --- | --- |
| `BasePrimeToyWeight` | `RealBasePrimeToyWeight` |
| `ratioBasePrimeWeight` | `realRatioBasePrimeWeight` |
| `RatioBaseWeightBudget` | `RealRatioBaseWeightBudget` |
| `baseWeightSubProbability_of_ratioBudget` | real finite budget lemma |
| `ratioBaseWeight_hitMass_le_const` | real weighted hit mass bound |
| `sampleTenRatioBaseWeight_route_summary` | real/log sample summary |

## 最初に実装するべきもの

最初の Lean 実装は、`Real.log` ではなく、次だけでよい。

```text
RealBasePrimeToyWeight
realRatioBasePrimeWeight
realRatioBasePrimeWeight_realBasePrimeToyWeight
real_ratio_sum_le_one
```

この段階で `ℝ` の除算と有限和だけを検証し、log 固有の問題は次 Phase に分離する。
