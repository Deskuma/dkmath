# Valuation Budget Route Plan

## 目的

この設計書は、R/log 版で重複なし route の次に必要になる、重複あり base-prime route の実装方針を整理する。

重複なし route では、selected base primes が pairwise distinct であることを仮定して、

```text
I ⊆ T.index n
1 < n
NatPairwiseDistinctOn I (W.basePrimeOf n I hI)
------------------------------------------------
log-ratio real provider is SubProbability
```

まで到達した。

重複あり route では、同じ base prime が複数回現れる場合でも、

```text
∏ q in I, W.basePrimeOf n I hI q ≤ n
```

を供給することが目標になる。

## 問題の形

各 selected label `q ∈ I` は witness provider により

```text
q = p(q) ^ k(q)
```

と読める。ここで `p(q) = W.basePrimeOf n I hI q` である。

重複なし route では、`p(q)` がすべて異なれば互いに素なので、各 `p(q) ∣ n` から積も `n` を割ることができた。

重複あり route では、同じ `p` が複数回現れるため、次の比較が必要になる。

```text
#{ q ∈ I | p(q) = p } ≤ exponent of p in n
```

この比較があれば、

```text
∏ q in I, p(q) ∣ n
```

に進める。そこから既存の R/log route により `SubProbability` へ到達できる。

## 候補 API

### Base-prime multiplicity

選択集合 `I` 上で、base value `p` が何回現れるかを `Finset.filter` で数える。

```lean
def NatBaseMultiplicityOn
    {ι : Type _}
    (I : Finset ι)
    (pOf : ι → ℕ)
    (p : ℕ) : ℕ :=
  (I.filter fun i => pOf i = p).card
```

この定義は、まず `RealLog.lean` または新規 `ValuationBudget.lean` に置く候補である。

### Factorization budget

`Nat.factorization` は `ℕ →₀ ℕ` として各素数の指数を返す。mathlib では、素数 `p` について

```lean
n.factorization p = padicValNat p n
```

という形で接続されている。

重複あり route の最初の predicate は次の形が自然である。

```lean
def NatBaseMultiplicityBudgetOn
    {ι : Type _}
    (I : Finset ι)
    (pOf : ι → ℕ)
    (n : ℕ) : Prop :=
  ∀ p, Nat.Prime p →
    NatBaseMultiplicityOn I pOf p ≤ n.factorization p
```

この route では `Nat.factorization` を主 API とし、必要なときだけ `padicValNat` と接続する。

## `factorization` route と `padicValNat` route

### `Nat.factorization` route

利点:

- 積の divisibility を示す目的に近い。
- `factorization_le_iff_dvd` や `prod_factorization_pow_eq_self` と相性が良い。
- 「全 prime の指数比較」から「product divides n」へ進めやすい。

懸念:

- `Finsupp` / finite support の補題に慣れる必要がある。
- `∏ pOf(q)` の factorization を、multiplicity count と一致させる補題が必要になる。

### `padicValNat` route

利点:

- DkMath 既存コードに `padicValNat` を使う実績が多い。
- 個別 prime の指数評価を直接書ける。
- `p` 固定の局所補題を書きやすい。

懸念:

- 最終的に product divisibility へ戻すには、全 prime の評価を束ねる必要がある。
- `Nat.factorization` が内部的に `padicValNat` を使っているため、最終段では factorization route に寄せた方が自然な可能性が高い。

## 推奨方針

最初は `Nat.factorization` route を主軸にする。

理由:

1. 目標は `∏ pOf(q) ∣ n` であり、これは factorization の点wise 比較と相性が良い。
2. `Nat.factorization` は `padicValNat` と接続済みなので、必要なら既存の p-adic 補題を後から差し込める。
3. 重複あり route の抽象補題を prime-power witness から独立に作れる。

## 実装 Phase 案

### Phase-R021. Valuation budget design

この文書を作成し、重複あり route の predicate と実装順を固定する。

### Phase-R022. Multiplicity vocabulary

実装済み:

```lean
def NatPrimeValuedOn
def NatBaseMultiplicityOn
def NatBaseMultiplicityBudgetOn
```

`DkMath/NumberTheory/PrimitiveSet/ValuationBudget.lean` に分離した。
あわせて、展開用の薄い補題として次を追加済み。

```lean
theorem natBaseMultiplicityOn_eq_card_filter
theorem natBaseMultiplicityBudgetOn_iff
```

### Phase-R023. Product factorization bridge

実装済み:

```lean
theorem factorization_prod_primeValued_eq_multiplicity_of_prime
theorem natProductDvdOn_of_multiplicityBudget
```

`pOf` が selected index 上で prime-valued である仮定を明示し、任意の prime `p` について

```text
(∏ i in I, pOf i).factorization p
=
NatBaseMultiplicityOn I pOf p
```

を示した。その後、`NatBaseMultiplicityBudgetOn I pOf n` から factorization の点wise 比較を作り、
`Nat.factorization_le_iff_dvd` で

```lean
NatProductDvdOn I pOf n
```

へ戻す。

### Phase-R024. Product bound and provider bridge

実装済み:

```lean
theorem realLogNonnegOn_of_natPrimeValuedOn
theorem natProductBoundOn_of_multiplicityBudget
theorem realLogProductBudget_of_multiplicityBudget
theorem realLogRatioWeightProvider_subProbability_of_multiplicityBudget
```

R017 と同様に、

```text
NatBaseMultiplicityBudgetOn
-> NatProductDvdOn
-> NatProductBoundOn
-> RealLogProductBudget
-> SubProbability
```

へ接続した。

この段階では `pOf : ι → ℕ` を抽象引数のまま扱う。
`pOf` が selected index 上で prime-valued であり、base multiplicity が
`n.factorization` に収まるなら、`log (pOf i) / log n` provider は
`SubProbability` になる。

### Phase-R025. Witness-provider bridge

`W.basePrimeOf` について、既存の

```lean
PrimePowerWitnessProvider.basePrimeOf_prime_on
PrimePowerWitnessProvider.basePrimeOf_dvd_source_on
```

を使い、multiplicity budget 仮定から witness-derived log-ratio provider の `SubProbability` へ進める。

## 注意点

- `n = 0` の扱いは避ける。R/log route ではすでに `1 < n` を要求しているため、必要な非零性はここから供給する。
- `pOf i = 1` は log nonnegativity では許されるが、valuation budget route では prime-valued 仮定を置くため対象外になる。
- 重複なし route は今後も残す。valuation route はそれを置き換えるのではなく、より一般の route として追加する。
- 最初から `W.label` の exponent `k(q)` を使い切ろうとしない。まずは base prime の出現回数を `n.factorization` で抑える抽象 route を閉じる。

## 到達目標

最終的には次の theorem-facing shape を目指す。

```lean
theorem basePrimeOf_logRatioSubProbability_of_multiplicityBudget
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (n : ℕ)
    (I : Finset ℕ)
    (hI : ∀ q, q ∈ I → q ∈ T.toDivisorTransitionKernel.index n)
    (hn : 1 < n)
    (hbudget :
      NatBaseMultiplicityBudgetOn I (W.basePrimeOf n I hI) n) :
    (realLogRatioWeightProvider I (W.basePrimeOf n I hI) n
      (W.basePrimeOf_realLogNonnegOn n I hI) hn).SubProbability
```

この theorem が閉じれば、重複あり finite log route の入口ができる。
