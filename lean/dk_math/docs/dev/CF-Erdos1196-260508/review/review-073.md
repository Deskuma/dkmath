# review Phase "R"

## 1. 結論

うむ、Phase-R014 は **R 版 log route と prime-power witness provider をつなぐ最初の橋** じゃ。

ここまで R 側では、

$$
RealLogProductBudget(I,pOf,n)
\Rightarrow
\text{log-ratio provider is sub-probability}
$$

まで閉じていた。今回 Phase-R014 では、その (pOf) を任意関数のまま放置せず、prime-power witness provider から読めるようにする準備が入った。

つまり、

$$
q=p^k
$$

の witness から base prime (p) を読み、

$$
pOf(q)=p
$$

として扱うための入口ができたわけじゃ。

## 2. 今回の主役

追加された中心はこの三つじゃ。

```lean
PrimePowerWitnessProvider.basePrime_one_le
PrimePowerWitnessProvider.basePrimeOf
PrimePowerWitnessProvider.basePrimeOf_one_le
```

`basePrime_one_le` は、indexed label (q) の witness から読んだ base prime が (1) 以上であることを示す。

数学的には、

$$
q=p^k,\qquad p\text{ prime}
$$

なので、

$$
1\le p
$$

が出る、という補題じゃな。

実際には素数なので (1<p) まであるが、R 側の `RealLogNonnegOn` が要求するのは

$$
1\le pOf(q)
$$

なので、今回の形で十分じゃ。

## 3. `basePrimeOf` の意味

今回の定義、

```lean
basePrimeOf
```

はかなり重要じゃ。

選択集合 (I) と、

$$
I\subseteq T.index(n)
$$

を表す

```lean
hI : ∀ q, q ∈ I → q ∈ T.toDivisorTransitionKernel.index n
```

を受け取り、(I) 上では witness provider から base prime を読む。

$$
q\in I
\Rightarrow
basePrimeOf(q)=(W.label(n,q,hI(q))).p
$$

一方、(I) の外側では (1) を返す。

これは良い設計じゃ。
後続の `RealLogProductBudget I pOf n` や `NatProductBoundOn I pOf n` は、基本的に (I) 上だけを見る。だから外側を (1) にしておけば、全域関数

$$
pOf:\mathbb{N}\to\mathbb{N}
$$

として扱えて、外側で余計な害が出ない。

## 4. R 側への接続準備

Phase-R013 では、R 側が後続に要求する interface をこう固定した。

$$
RealLogProductBudget(I,pOf,n)
$$

つまり、

$$
RealLogNonnegOn(I,pOf)
$$

$$
1<n
$$

$$
\prod_{q\in I}pOf(q)\le n
$$

じゃ。

今回 `basePrimeOf_one_le` により、最初の

$$
RealLogNonnegOn(I,W.basePrimeOf(n,I,hI))
$$

を供給できる見通しが立った。

まだ Lean 上で `RealLogNonnegOn` そのものには接続していないが、それは依存関係の切り分けとして正しい。

## 5. ファイル分離の判断が大事

今回 `basePrimeOf` は `DivisorTransitionKernel.lean` に入った。
これは良い。

ただし、次に

```lean
RealLogNonnegOn I (W.basePrimeOf n I hI)
```

を直接 theorem 化しようとすると、`DivisorTransitionKernel.lean` が `RealLog.lean` を import したくなる。

これは避けたい。
理由は、R/log 側の実験 route を divisor kernel 本体に混ぜると依存関係が重くなるからじゃ。

次は新しい bridge file を作るのがよい。

```text
DkMath/NumberTheory/PrimitiveSet/RealDivisorBridge.lean
```

のような名前で、

```lean
import DkMath.NumberTheory.PrimitiveSet.DivisorTransitionKernel
import DkMath.NumberTheory.PrimitiveSet.RealLog
```

とし、R 側と divisor 側の接続 theorem を置く。

## 6. 次の一手: Phase-R015 案

次は **basePrimeOf を RealLogProductBudget に接続する bridge** が自然じゃ。

まず最小補題はこれ。

```lean
theorem basePrimeOf_realLogNonnegOn
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (n : ℕ)
    (I : Finset ℕ)
    (hI : ∀ q, q ∈ I → q ∈ T.toDivisorTransitionKernel.index n) :
    RealLogNonnegOn I (W.basePrimeOf n I hI) :=
  W.basePrimeOf_one_le n I hI
```

これはほぼそのまま通るはずじゃ。

次に、product bound を外部仮定として受け取って bundle を作る。

```lean
theorem basePrimeOf_realLogProductBudget_of_productBound
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (n : ℕ)
    (I : Finset ℕ)
    (hI : ∀ q, q ∈ I → q ∈ T.toDivisorTransitionKernel.index n)
    (hn : 1 < n)
    (hprod : NatProductBoundOn I (W.basePrimeOf n I hI) n) :
    RealLogProductBudget I (W.basePrimeOf n I hI) n
```

これが閉じると、R 側の `RealLogProductBudget` interface に divisor witness provider が正式接続される。

## 7. Phase-R016 の見通し

その次は、さらに一歩進めて、

$$
NatProductBoundOn(I,W.basePrimeOf(n,I,hI),n)
$$

を仮定すれば、

$$
realLogRatioWeightProvider
$$

の `SubProbability` まで出す alias を置くのがよい。

候補名は、

```lean
basePrimeOf_realLogRatioWeightProvider_subProbability_of_productBound
```

のようなものじゃ。

意味は、

$$
I\subseteq index(n)
$$

$$
1<n
$$

$$
\prod_{q\in I} W.basePrimeOf(q)\le n
$$

なら、

$$
\frac{\log(W.basePrimeOf(q))}{\log n}
$$

を重みとする real provider は sub-probability、ということじゃ。

ここまで行くと、prime-power witness provider 由来の log-ratio route が、product bound を仮定すれば完全に走る。

## 8. まだ残る本丸

ただし、今回もまだ

$$
\prod_{q\in I} W.basePrimeOf(q)\le n
$$

そのものは証明していない。

ここが本丸じゃ。

なぜ難しいかというと、同じ base prime が複数回出る可能性があるからじゃ。

例えば、

$$
q_1=2,\qquad q_2=4
$$

なら、どちらも base prime は (2)。
このとき base product は

$$
2\cdot2=4
$$

になる。これを (n) が吸収するには、(n) 側に (2^2) 以上の指数予算が必要になる。

つまり次の深部には、

$$
\text{重複制御}
$$

または

$$
\text{指数消費 tracking}
$$

が待っておる。

## 9. 総括

Phase-R014 は、R/log route を prime-power witness provider へ戻すための **薄い橋** じゃ。

ここで、

$$
q=p^k
$$

の witness から base prime (p) を読み、

$$
pOf(q)=p
$$

として使うための関数 `basePrimeOf` ができた。

そして (I) 上では、

$$
1\le basePrimeOf(q)
$$

も証明された。

山で言えば、R 側から伸びてきた (\log p/\log n) のザイルが、ついに prime-power witness の岩場に触れた。
次は、そのザイルを `RealLogProductBudget` に正式に結び、さらにその先で product bound をどう得るか、重複制御の岩稜へ進む番じゃ。
