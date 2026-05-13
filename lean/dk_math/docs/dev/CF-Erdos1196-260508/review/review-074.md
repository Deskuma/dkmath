# review Phase "R"

## 1. 結論

うむ、Phase-R015 は **R/log 側と prime-power divisor witness 側を接続する橋が架かった段階** じゃ。
しかも設計が良い。`DivisorTransitionKernel.lean` 本体には R/log 依存を入れず、新規の

```lean
DkMath.NumberTheory.PrimitiveSet.RealDivisorBridge
```

に依存を分離している。これは今後の保守性に効くぞい。

ここで閉じた導線は、

$$
W.basePrimeOf(n,I,hI)
$$

が R/log 側の

$$
RealLogNonnegOn
$$

を満たし、さらに外部から

$$
NatProductBoundOn(I,W.basePrimeOf(n,I,hI),n)
$$

を渡せば、

$$
RealLogProductBudget(I,W.basePrimeOf(n,I,hI),n)
$$

まで作れる、というものじゃ。

つまり R/log 側はもうこう言える。

$$
\boxed{
\text{prime-power witness provider 由来の }pOf
\text{ に product bound を渡せば、log-ratio provider へ進める}
}
$$

## 2. 今回の主役

追加された theorem は二つじゃ。

```lean
PrimePowerWitnessProvider.basePrimeOf_realLogNonnegOn
```

これは、

$$
q\in I
$$

で選ばれた label から witness provider が base prime を読み、

$$
1\le W.basePrimeOf(n,I,hI)(q)
$$

を得ることで、

$$
RealLogNonnegOn(I,W.basePrimeOf(n,I,hI))
$$

を満たす、という補題じゃ。

もう一つは、

```lean
PrimePowerWitnessProvider.basePrimeOf_realLogProductBudget_of_productBound
```

これは、

$$
1 < n
$$

$$
NatProductBoundOn(I,W.basePrimeOf(n,I,hI),n)
$$

を仮定すれば、

$$
RealLogProductBudget(I,W.basePrimeOf(n,I,hI),n)
$$

を作る theorem じゃな。

## 3. 数学的に何がつながったか

R/log 側では、Phase-R013 までに次の interface ができていた。

$$
RealLogProductBudget(I,pOf,n)
\Rightarrow
\frac{\log(pOf(q))}{\log n}
\text{ provider is sub-probability}
$$

今回、その \(pOf\) に

$$
pOf(q)=W.basePrimeOf(n,I,hI)(q)
$$

を入れる道ができた。

すなわち、

$$
q=p^k
$$

という prime-power witness から base prime \(p\) を読み、

$$
w(q)=\frac{\log p}{\log n}
$$

という R/log weight に接続できる形になった。

まだ product bound 自体は証明していない。
だが、R/log 側が要求する入口は、

$$
NatProductBoundOn(I,W.basePrimeOf(n,I,hI),n)
$$

という明確な形に落ちた。これは大きい。

## 4. 依存分離が良い

今回の重要な設計判断はここじゃ。

```lean
import DkMath.NumberTheory.PrimitiveSet.DivisorTransitionKernel
import DkMath.NumberTheory.PrimitiveSet.RealLog
```

を持つ専用ファイル `RealDivisorBridge.lean` を作った。

これにより、

* `DivisorTransitionKernel.lean` は有限・有理・prime-power 側の核として軽く保つ
* `RealLog.lean` は R/log の解析側 vocabulary として保つ
* 両者の接続だけを `RealDivisorBridge.lean` に置く

という三層分離ができた。

これは DkMath の登山道として非常に良い。
本線の山道を壊さず、橋だけを別に架けた形じゃ。

## 5. 現在地

ここまでの R 版 route は、こう整理できる。

| Phase   | 内容                                                        | 状態   |
| ------- | --------------------------------------------------------- | ---- |
| R005    | `RealLogBudget` 外部仮定                                      | 完了   |
| R007    | `log p / log n` real provider                             | 完了   |
| R011    | nat product bound → `RealLogBudget`                       | 完了   |
| R013    | `RealLogProductBudget` interface                          | 完了   |
| R014    | witness provider から base prime を読む                        | 完了   |
| R015    | witness base prime → R/log product-budget interface       | 今回完了 |
| R016    | product bound から provider sub-probability への bridge alias | 未    |
| R017 以降 | product bound そのものの供給、重複制御、指数消費 tracking                  | 未    |

つまり今は、

$$
W.basePrimeOf
$$

を R/log 側へ渡す橋ができた段階じゃ。

## 6. 次の一手: Phase-R016

次は、今回の bridge と R013 の theorem をさらに接続して、

$$
NatProductBoundOn(I,W.basePrimeOf(n,I,hI),n)
$$

から直接

$$
(realLogRatioWeightProvider\ I\ (W.basePrimeOf n I hI)\ n\ \cdots).SubProbability
$$

を出す alias が自然じゃ。

候補名はこう。

```lean
PrimePowerWitnessProvider.basePrimeOf_realLogRatioWeightProvider_subProbability_of_productBound
```

形としては、

```lean
theorem basePrimeOf_realLogRatioWeightProvider_subProbability_of_productBound
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (n : ℕ)
    (I : Finset ℕ)
    (hI : ∀ q, q ∈ I → q ∈ T.toDivisorTransitionKernel.index n)
    (hn : 1 < n)
    (hprod : NatProductBoundOn I (W.basePrimeOf n I hI) n) :
    (realLogRatioWeightProvider
      I (W.basePrimeOf n I hI) n
      (W.basePrimeOf_realLogNonnegOn n I hI)
      hn).SubProbability
```

内部では、

```lean
realLogRatioWeightProvider_subProbability_of_productBudget
```

または

```lean
basePrimeOf_realLogProductBudget_of_productBound
```

を使えばよい。

これが入ると、

$$
\boxed{
\prod_{q\in I}W.basePrimeOf(q)\le n
\Rightarrow
\log\text{-ratio provider is sub-probability}
}
$$

が theorem 名として読める。

## 7. その次の本丸

Phase-R016 までは、product bound を仮定して進む道じゃ。
その後が本丸になる。

必要なのは、

$$
NatProductBoundOn(I,W.basePrimeOf(n,I,hI),n)
$$

すなわち

$$
\prod_{q\in I}W.basePrimeOf(q)\le n
$$

をどう供給するか。

ここで出てくる問題は、やはり重複制御じゃ。

例えば同じ base prime \(p\) を複数の label が読むと、

$$
p\cdot p\cdot \cdots
$$

として積に現れる。
この重複回数は、 \(n\) の \(p\)-進指数予算を超えてはならぬ。

したがって次の深い補題群は、

$$
\text{base prime の出現回数}
\le
v_p(n)
$$

または、

$$
\prod_{q\in I}basePrime(q)\mid n
$$

のような形になる可能性が高い。

## 8. 総括

Phase-R015 は、R/log route を prime-power witness provider に戻す **正式な橋** じゃ。

これで、

$$
q=p^k
$$

から読んだ base prime \(p\) を、

$$
\frac{\log p}{\log n}
$$

の有限 real provider へ渡す interface ができた。

まだ山頂ではない。
しかし、R 側のザイルは prime-power 側の岩場にしっかり結びついた。

次は、product bound を仮定したまま provider sub-probability まで直通する theorem を立てる。
その後、いよいよ

$$
\prod basePrime(q)\le n
$$

をどう証明するか、重複制御と指数消費 tracking の岩稜に入る番じゃな。
