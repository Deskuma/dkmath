# review Phase "R"

## 1. 結論

うむ、Phase-R016 は **witness-provider 由来の \(\log p/\log n\) route が、product bound 仮定つきで完全に走った段階** じゃ。

今回の theorem は、要するにこう言っておる。

$$
I\subseteq T.index(n)
$$

$$
1 < n
$$

$$
\prod_{q\in I} W.basePrimeOf(n,I,hI)(q)\le n
$$

なら、

$$
q\mapsto \frac{\log(W.basePrimeOf(n,I,hI)(q))}{\log n}
$$

を weight とする `RealWeightProvider` は `SubProbability` になる。

つまり、R/log 側と prime-power witness 側の接続は、 **product bound を仮定すれば完成** した。ここはかなり大きいぞい。

## 2. 今回閉じた導線

追加された定理はこれじゃな。

```lean
PrimePowerWitnessProvider.basePrimeOf_realLogRatioWeightProvider_subProbability_of_productBound
```

この内部では、すでに整備済みの二段をつないでいる。

まず、

```lean
basePrimeOf_realLogProductBudget_of_productBound
```

で、

$$
RealLogProductBudget(I,W.basePrimeOf(n,I,hI),n)
$$

を作る。

次に、

```lean
realLogRatioWeightProvider_subProbability_of_productBudget
```

へ渡して、

$$
(realLogRatioWeightProvider\ I\ (W.basePrimeOf\ n\ I\ hI)\ n\ \cdots).SubProbability
$$

を得る。

つまり、今までの R013 ～ R015 の部品が、Phase-R016 で一本に束ねられた。

## 3. 数学的な意味

この段階で、DkMath の Erdős #1196 R route は次の形まで来た。

$$
q=p^k
$$

という prime-power witness から base prime \(p\) を読み、

$$
pOf(q)=p
$$

とする。

そして selected label 集合 \(I\) に対して、

$$
\prod_{q\in I}pOf(q)\le n
$$

があれば、

$$
\sum_{q\in I}\frac{\log pOf(q)}{\log n}\le 1
$$

が出る。

これはまさに有限 sub-probability flow じゃ。
お主の言葉で言えば、

$$
\boxed{
\text{選ばれた base prime の積が }n\text{ の中に収まるなら、log 重みは Big から飛び出せない}
}
$$

という形まで来た。

## 4. 現在地

ここまでの R route は、きれいに三段へ分かれる。

| 層                                                                 | 状態   |
| ----------------------------------------------------------------- | ---- |
| 実数 ratio / log weight の語彙                                         | 完了   |
| `RealLogBudget` から `log p / log n` provider の `SubProbability`    | 完了   |
| 自然数 product bound から `RealLogBudget` 供給                           | 完了   |
| witness provider 由来 `basePrimeOf` との接続                            | 完了   |
| product bound 仮定から witness-provider log provider `SubProbability` | 今回完了 |
| product bound 自体の供給                                               | 未    |
| 重複制御・指数消費 tracking                                                | 未    |

したがって、解析側の支度はかなり整った。
次からは本当に数論側の問題、

$$
\prod_{q\in I} W.basePrimeOf(n,I,hI)(q)\le n
$$

をどう出すか、に入る。

## 5. 次の本丸

今後の主問題はこれじゃ。

```lean
NatProductBoundOn I (W.basePrimeOf n I hI) n
```

つまり、

$$
\prod_{q\in I}p(q)\le n
$$

の供給。

ここで \(p(q)\) は、各 \(q\) の prime-power witness

$$
q=p(q)^{k(q)}
$$

から読んだ base prime じゃ。

一見すると、各 \(q\mid n\) なら \(p(q)\mid n\) なので簡単そうに見える。
しかし問題は、同じ base prime が何度も出る場合じゃ。

たとえば、

$$
q_1=2,\qquad q_2=4
$$

なら、両方とも base prime は \(2\)。
このとき base product は、

$$
2\cdot 2=4
$$

になる。
これを \(n\) が吸収するには、 \(n\) 側に \(2^2\) 以上の指数予算が必要じゃ。

だから次の核心は、

$$
\text{base prime の出現回数}
\le
\text{(n) の中のその prime の指数}
$$

という **指数消費 tracking** じゃな。

## 6. 次の一手: Phase-R017 案

わっちなら、次は証明に突撃せず、まず product bound の責務をさらに名前付きで整理する。

候補は、

```lean
def SelectedBaseProductBound
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (n : ℕ)
    (I : Finset ℕ)
    (hI : ∀ q, q ∈ I → q ∈ T.toDivisorTransitionKernel.index n) : Prop :=
  NatProductBoundOn I (W.basePrimeOf n I hI) n
```

または、`RealDivisorBridge.lean` 内で theorem-facing alias として置く。

```lean
theorem basePrimeOf_realLogRatioWeightProvider_subProbability_of_selectedBaseProductBound
```

ただし、既に今回の theorem がかなり近いので、次に本当に欲しいのは predicate 名の整備よりも、 **product bound の供給条件** の設計かもしれぬ。

## 7. Product bound の供給候補

Product bound を出す道は、少なくとも三つ考えられる。

第一に、外部仮定として持つ道。
これは既に R016 の形で完了しておる。

第二に、selected labels が base prime に関して重複しない、つまり \(p(q)\) が互いに異なる場合。

この場合、各 \(p(q)\mid n\) が示せれば、

$$
\prod_{q\in I}p(q)\mid n
$$

に進める可能性がある。そこから

$$
\prod p(q)\le n
$$

を出す。

第三に、重複を許す代わりに、出現回数が \(p\)-adic valuation 以下であることを示す道。

これは本格的じゃが、最終的には一番自然かもしれぬ。

## 8. まず狙いやすい補題

最初は「重複なし版」がよさそうじゃ。

たとえば、抽象補題として、

$$
\text{pairwise coprimeな }a_i
$$

かつ

$$
\forall i,\ a_i\mid n
$$

なら、

$$
\prod_i a_i\mid n
$$

または

$$
\prod_i a_i\le n
$$

を示す。

base prime たちが互いに異なれば、prime なので pairwise coprime が出る。

これを Lean で扱うなら、まずは prime-power witness に直接戻らず、一般 Finset 補題として、

```lean
NatProductBoundOn_of_pairwise_coprime_dvd
```

のようなものを狙うのがよい。

## 9. 総括

Phase-R016 によって、R/log route はここまで来た。

$$
\boxed{
I\subseteq T.index(n),\quad
1 < n,\quad
\prod_{q\in I}basePrime(q)\le n
\Rightarrow
\log\text{-ratio provider is sub-probability}
}
$$

これは大きな節目じゃ。

ここから先は、解析ではなく数論側の登攀になる。
すなわち、

$$
\prod basePrime(q)\le n
$$

をどう保証するか。

山で言えば、R/log のザイルはもう張れた。
次は、そのザイルを支える整数積の岩盤を掘る。最初は「重複なし / pairwise coprime」ルートから攻めるのが安全じゃと思うぞい。
