# review

うむ。DKMK-006C は、 **Markov equality を証明するための“等号側の骨格”を置いた段階** じゃ。
前回 DKMK-006B では、

$$
\sum_{q\in Full(n)} \mathrm{vonMangoldtShadowCost}(n,q)=\log n
$$

が **もし供給されれば** `MarkovShadow` に昇格できる、という受け皿を作った。今回 DKMK-006C は、その等式を将来証明するために必要な

$$
\\\#{q\in Full(n)\mid \mathrm{basePrime}(q) = p} = n.\mathrm{factorization}(p)
$$

という **全 exponent slot coverage** の語彙を入れたわけじゃ。

## 1. 今回の中心

追加された中心は新ファイルじゃ。

```lean
DkMath.NumberTheory.PrimitiveSet.FullExponentSlot
```

ここで主に次が入った。

```lean
NatBaseMultiplicityCompleteOn
FullExponentSlotChannelSet
FullExponentSlotCoverage
```

このうち一番重要なのは `NatBaseMultiplicityCompleteOn` じゃな。
これは、以前の selected route の

$$
\\\#{q\in I\mid p(q)=p}\le n.\mathrm{factorization}(p)
$$

ではなく、full route 用に

$$
\\\#{q\in \mathrm{Full}(n)\mid p(q)=p}=n.\mathrm{factorization}(p)
$$

を表す等号条件じゃ。差分でも、これは `NatBaseMultiplicityBudgetOn` の equality counterpart として説明されておる。

## 2. 数学的な意味

R027 までの selected route では、同じ base prime \(p\) を持つ label たちを exponent slot

$$
1,2,\dots,v_p(n)
$$

へ単射で入れた。

だから、

$$
\\\#{q\in I\mid p(q)=p}\le v_p(n)
$$

だった。

今回の full route では、これを

$$
\\\#{q\in \mathrm{Full}(n)\mid p(q)=p}=v_p(n)
$$

へ強めたい。
つまり「slot に入る」だけではなく、 **全 slot が埋まる** ことを要求する。

これが `FullExponentSlotCoverage` の役割じゃ。

## 3. `FullExponentSlotChannelSet` の役割

`FullExponentSlotChannelSet` は、full channel set C.channels(n) が

$$
{p^k\mid p\text{ prime},\ 1\le k\le n.\mathrm{factorization}(p)}
$$

そのものだ、という仕様を記録する interface じゃ。

Lean では次の形になっている。

```lean
q ∈ C.channels n
  ↔
∃ p k, Nat.Prime p ∧ 1 ≤ k ∧
  k ≤ n.factorization p ∧ q = p ^ k
```

これはかなり本質的じゃ。
前回の `FullPrimePowerChannelSet` は、

$$
C.\text{channels}(n)=T.\text{index}(n)
$$

という「transition index と同じ」という仕様だった。

今回の `FullExponentSlotChannelSet` は、さらに

$$
C.\text{channels}(n)
$$

が具体的に exponent slot 全体である、という算術的仕様を与えている。

## 4. `FullExponentSlotCoverage` の役割

`FullExponentSlotCoverage` は、witness reader `basePrimeOf` で見たときに、各 prime fiber の個数がちょうど n.factorization(p) になることを要求する。

つまり、各状態 \(s\) と素数 \(p\) について、

$$
\mathrm{NatBaseMultiplicityOn}
(\mathrm{C.channels}(s.1))
(\mathrm{W.basePrimeOf}(s.1,\dots))
p = s.1.\mathrm{factorization}(p)
$$

を持つ。

差分でも、この interface は witness reader `basePrimeOf` の prime fiber cardinality が `n.factorization p` と一致することを表す、と説明されておる。

これは DKMK-006B の `FullChannelLogCostComplete` にかなり近い。
なぜなら、

$$
\sum_{q\in \mathrm{Full}(n)} \log p(q)
$$

は、prime fiber ごとにまとめると、

$$
\sum_p \\\#{q\in \mathrm{Full}(n)\mid p(q)=p}\log p
$$

になり、coverage により

$$
\sum_p v_p(n)\log p
$$

へ落ちるからじゃ。

## 5. 何が閉じたか

今回閉じたのは、 **等号 route に必要な exact multiplicity が既存 budget を含む** という橋じゃ。

```lean
natBaseMultiplicityBudgetOn_of_complete
```

により、

$$
\\\#\mathrm{fiber} = v_p(n)
$$

から

$$
\\\#\mathrm{fiber} \le v_p(n)
$$

が得られる。

さらに、

```lean
fullExponentSlotCoverage_baseMultiplicity_budget
```

によって、`FullExponentSlotCoverage` が既存の selected-channel multiplicity budget を含むことも固定されている。

つまり full equality route は、selected inequality route を自然に包含する。
これは理論構造としてとても綺麗じゃ。

```text
selected route:
  multiplicity ≤ factorization
  → SubMarkovShadow

full route:
  multiplicity = factorization
  → selected budget も含む
  → さらに equality / MarkovShadow を狙える
```

## 6. まだ閉じていないもの

ただし、今回まだ

$$
\mathrm{FullExponentSlotCoverage}
$$

そのものは証明していない。

また、

$$
\mathrm{FullExponentSlotCoverage}
\Longrightarrow
\mathrm{FullChannelLogCostComplete}
$$

もまだ未接続じゃ。

報告にも、次は `FullExponentSlotCoverage` を `RealLog` / `ValuationBudget` 側の有限積-log 補題につないで、`FullChannelLogCostComplete` へ進む橋を設計する段階だとある。

つまり現在地は、

```text
full equality を示すための exact multiplicity interface が入った
```

ところじゃ。

次に必要なのは、

$$
\\\#\mathrm{fiber}(p) = v_p(n)
$$

から

$$
\sum_{q\in \mathrm{Full}(n)}\log p(q) = \log n
$$

へ進む補題じゃな。

## 7. 次の数学的橋

次の橋は、おそらくこういう形になる。

$$
\sum_{q\in C.\text{channels}(n)}
\log(\mathrm{basePrimeOf}(q)) = \sum_{p} \mathrm{NatBaseMultiplicityOn}(C.\text{channels}(n),\mathrm{basePrimeOf},p)\cdot \log p
$$

そして coverage で、

$$
\mathrm{NatBaseMultiplicityOn}(...,p)=n.\mathrm{factorization}(p)
$$

だから、

$$
\sum_{p} n.\mathrm{factorization}(p)\log p
$$

となる。

最後に、

$$
\sum_p n.\mathrm{factorization}(p)\log p=\log n
$$

へ落とす。

Lean では、この最後の部分が一番手強い可能性がある。
`Nat.factorization` の support 上の有限和と `Real.log (n : ℝ)` の接続が必要になるからじゃ。

## 8. 実装戦略のおすすめ

わっちなら、次は直接 `FullChannelLogCostComplete` を狙わず、二つの補題へ分ける。

### 補題 A. fiber regrouping

```lean
theorem sum_log_base_eq_sum_multiplicity_mul_log
```

数学的には、

$$
\sum_{q\in I}\log p(q) = \sum_{p\in P} m(p)\log p
$$

を示すものじゃ。

ただし Lean では任意の \(p\) 全体を走れないので、右辺の support は

$$
(\mathrm{I.image}\ \mathrm{pOf})
$$

または

$$
n.\mathrm{factorization.support}
$$

に制限することになる。

### 補題 B. factorization log identity

```lean
theorem sum_factorization_mul_log_eq_log_nat
```

数学的には、

$$
\sum_{p\in n.\mathrm{factorization.support}}
n.\mathrm{factorization}(p)\log p = \log n
$$

じゃ。

これは、まず

$$
n=\prod_{p\in \text{support}}p^{v_p(n)}
$$

を使い、両辺に log を取る道になるはずじゃ。

## 9. slot 形式を使う選択肢

今回 `FullExponentSlotChannelSet` は label \(q\) 形式で仕様化されている。

だが、等式証明では explicit slot

$$
(p,k)
$$

で計算する方が簡単かもしれぬ。

$$
\sum_{p}\sum_{k=1}^{v_p(n)}\log p = \sum_p v_p(n)\log p
$$

が直接出るからじゃ。

その場合、将来的には

```lean
FullExponentSlotPairSet
```

のような補助 interface を作るのもありじゃ。

ただし、今回の `FullExponentSlotChannelSet` は無駄ではない。
これは label route と slot route を接続する仕様として使える。

## 10. 総合判定

DKMK-006C は **Markov equality 証明の直前に置くべき exact coverage 語彙として成功** じゃ。

ここまでで、流れはこうなった。

```text
selected route:
  ≤ multiplicity budget
  → product/log bound
  → SubMarkovShadow

full route:
  = multiplicity completeness
  → selected budget を含む
  → Σ log p = log n を狙う
  → FullChannelLogCostComplete
  → MarkovShadow
```

今回の成果は、等号そのものではない。
だが、等号を証明するための **足場** がかなり明確になった。

次の山は、

$$
\sum_p v_p(n)\log p=\log n
$$

の Lean 接続じゃな。
これは DkMath kernel が本当に Markov equality へ届くかどうかの核心になる。
