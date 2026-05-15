# CF-Erdos1196-260508 Overview

## 目的

この作業ディレクトリは、Erdos #1196 へ向かう Lean 実装のうち、有限・代数的な `ℕ` / `ℚ` 版の骨格をまとめる。

現時点の主眼は、解析的な極限評価ではない。まず有限集合、有限和、有限 channel provider を使って、primitive set が作る hitting mass が sub-probability channel の外へ出ない、という再利用可能な spine を固定する。

今回までに到達した N/Q 版の中心命題は次の形である。

```text
finite primitive / antichain structure
-> source-controlled chain family
-> finite transition kernel
-> sub-probability channel provider
-> weightedHitMass <= source bound
```

さらに prime-power divisor channel に対して、

```text
c(n, p) = A(p) / B(n)
0 <= A(p)
0 < B(n)
Σ A(p(q)) <= B(n)
-----------------------
weightedHitMass <= C
```

という ratio-style toy route が `ℚ` 上で実走済みである。

## 現在地

この作業では、次の層を順に積み上げた。

1. finite mass / hitting layer
   - 有限 hitting family の質量上界を作る。
   - source への injective assignment によって hit 側の総質量を source 側で抑える。

2. primitive set layer
   - `PrimitiveOn S` を有限 divisibility antichain として定義する。
   - 同じ divisibility chain 上で primitive set に複数回 hit できない、という非交差性の入口を作る。

3. source-controlled / weighted path layer
   - source を共有する chain family に有限 weight provider を適用する。
   - provider が sub-probability なら weighted hit mass は source mass bound を超えない。

4. finite transition kernel layer
   - index / next / weight を持つ有限 kernel を導入する。
   - kernel から provider を取り出し、weighted path family へ適用する導線を作る。

5. divisor / prime-power transition layer
   - `DivisorTransitionKernel` により、label `q` を使った `n -> n / q` の有限遷移を扱う。
   - prime-power label を持つ kernel を `PrimePowerDivisorTransitionKernel` として package 化する。

6. witness-provider base-prime weight layer
   - prime-power label `q = p^k` から base prime `p` を読む `PrimePowerWitnessProvider` を導入する。
   - label weight を base-prime weight `c(n, p)` から作る。

7. ratio-style toy route
   - `ratioBasePrimeWeight A B n p = A p / B n` を導入する。
   - 非負 numerator、正 denominator、有限 budget 条件から sub-probability を得る。
   - sample kernel で `weightedHitMass <= 1` まで確認する。

## Lean 上の主要な到達点

代表的な公開名は次である。

```lean
PrimitiveOn
SourceControlledChainFamily
WeightedPathFamily.weightedHitMass
WeightProvider.SubProbability
FiniteTransitionKernel
DivisorTransitionKernel
PrimePowerDivisorTransitionKernel
PrimePowerWitnessProvider
PrimePowerChannelProvider
ratioBasePrimeWeight
PrimePowerWitnessProvider.RatioBaseWeightBudget
PrimePowerWitnessProvider.ratioBaseWeight_hitMass_le_const
sampleTenRatioBaseWeight_route_summary
```

特に `sampleTenRatioBaseWeight_route_summary` は、現在の N/Q 版 ratio-style route の concrete summary である。

sample では、

```text
index(10) = {2, 5}
A(2) = 1
A(p != 2) = 0
B(n) = 1
```

として、

```text
A(2) + A(5) = 1 <= B(10)
```

を budget として閉じ、最終的に `weightedHitMass <= 1` まで Lean で通している。

## N/Q 版で意図的に扱っていないもの

この段階では、次はまだ扱わない。

- `Real.log`
- 実数値 weight
- `log p / log n`
- 無限 primitive set
- 漸近評価
- `1 + O(1 / log x)`
- von Mangoldt 関数そのものの解析的性質

理由は単純で、有限構造と解析構造を同時に入れると、問題が分解しにくくなるためである。N/Q 版は、後続の実数・対数版が載るための有限 channel API と theorem-facing names を固定する段階である。

## R 版へ進む方針

次段階では、`ℚ` 上の ratio-style toy route を `ℝ` 上へ持ち上げる。

ただし、いきなり `A(p) = log p`, `B(n) = log n` を Lean に入れるのではなく、まず次の三層を分ける。

```text
1. Real ratio layer
   A B : ℕ -> ℝ
   c(n, p) = A(p) / B(n)

2. Real budget layer
   0 <= A(p)
   0 < B(n)
   Σ A(p(q)) <= B(n)

3. log candidate layer
   A(p) = Real.log p
   B(n) = Real.log n
```

この切り分けにより、`ℝ` の除算・有限和・非負性と、`Real.log` 固有の補題を混ぜずに進められる。

R 版の実装計画は [RealLogRoutePlan.md](./RealLogRoutePlan.md) に分離する。

## R/log 版の現在地

R 版は `Phase-R001` から番号を振り直し、現在は重複あり finite log route まで Lean 上で通っている。

現在の推奨 summary theorem は次である。

```lean
PrimePowerWitnessProvider.basePrimeOf_logRatioSubProbability
```

これは次の条件だけから、

```text
I ⊆ T.index n
1 < n
```

次の real provider が `SubProbability` であることを示す。

```text
q ↦ Real.log (W.basePrimeOf n I hI q) / Real.log n
```

この route では、prime-power witness から `q = p(q)^k(q)` を読み、同じ base prime `p`
を持つ selected labels を exponent slot `1..n.factorization p` へ単射で入れる。
そのため、外部の multiplicity-budget 仮定なしで

```text
#{q ∈ I | p(q) = p} ≤ n.factorization p
```

が自動生成される。

比較用に、重複なし route の summary theorem も残している。

```lean
PrimePowerWitnessProvider.basePrimeOf_logRatioSubProbability_of_distinctBasePrimes
```

これは次の条件から、

```text
I ⊆ T.index n
1 < n
selected base primes are pairwise distinct
```

次の real provider が `SubProbability` であることを示す。

```text
q ↦ Real.log (W.basePrimeOf n I hI q) / Real.log n
```

内部では次の導線を使っている。

```text
pairwise distinct selected base primes
-> pairwise coprime selected base primes
-> selected base product divides n
-> selected base product <= n
-> Σ log(basePrime(q)) <= log n
-> Σ log(basePrime(q)) / log n <= 1
```

この route では、witness provider 由来の base prime について、選択集合上で次が theorem 名として固定されている。

```lean
PrimePowerWitnessProvider.basePrimeOf_prime_on
PrimePowerWitnessProvider.basePrimeOf_dvd_source_on
PrimePowerWitnessProvider.basePrimeOf_realLogNonnegOn
```

重複なし route の外部仮定として残るのは、選択された base prime の pairwise distinctness である。次段階の主題は、同じ base prime が複数回現れる場合の valuation budget / exponent consumption route である。

重複あり route は、R021-R027 で次の鎖として閉じた。

```text
q = p(q)^k(q)
same-base-prime labels inject into exponent slots
-> NatBaseMultiplicityBudgetOn I (W.basePrimeOf n I hI) n
-> ∏ q in I, W.basePrimeOf n I hI q ∣ n
-> ∏ q in I, W.basePrimeOf n I hI q ≤ n
-> Σ log(basePrime(q)) ≤ log n
-> Σ log(basePrime(q)) / log n ≤ 1
-> SubProbability
```

重複あり route の詳細設計は [ValuationBudgetRoutePlan.md](./ValuationBudgetRoutePlan.md) に分離する。

## 推奨される読み順

1. [ImplementsPlan.md](./ImplementsPlan.md)
   - 初期計画と finite hitting / primitive set spine の設計。
2. [History.md](./History.md)
   - 実際の作業履歴。Phase ごとの到達点と検証結果。
3. [README.md](./README.md)
   - 現在の N/Q 版まとめ。
4. [RealLogRoutePlan.md](./RealLogRoutePlan.md)
   - 次段階の R 版設計。
5. [ValuationBudgetRoutePlan.md](./ValuationBudgetRoutePlan.md)
   - 重複あり base-prime route と valuation budget の設計。

レビュー詳細は [review/](./review/) に保存されているが、通常の実装判断ではこの README と History を入口にする。
