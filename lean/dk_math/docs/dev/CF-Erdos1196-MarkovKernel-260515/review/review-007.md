# review

うむ。DKMK-006B は、 **Markov equality route の受け皿を作った段階** じゃ。
まだ

$$
\sum_{q\in Full(n)} \mathrm{vonMangoldtShadowCost}(n,q)=\log n
$$

そのものは証明しておらぬ。じゃが、 **この等式が得られたなら Markov shadow へ昇格できる** という接続は no-sorry で閉じた。これは設計上かなり大事な分岐点じゃ。

## 1. 今回、何が追加されたか

中心は二つじゃ。

```lean
DkMath.NumberTheory.PrimitiveSet.MarkovShadow
DkMath.NumberTheory.PrimitiveSet.FullChannelEquality
```

`MarkovShadow` は、前回の `SubMarkovShadow` に

$$
\mathrm{totalWeightAt}(s)=1
$$

を追加した equality 側の語彙じゃ。

構造としては、

```lean
structure MarkovShadow (σ ι : Type _) where
  toSubMarkovShadow : SubMarkovShadow σ ι
  totalWeightAt_eq_one :
    ∀ s, toSubMarkovShadow.totalWeightAt s = 1
```

となっておる。
つまり、状態ごとの finite real provider が、単に

$$
\sum_i w_i\le 1
$$

ではなく、

$$
\sum_i w_i=1
$$

を満たすものとして扱える。

## 2. `MarkovShadow.ofCapacityKernel` の意味

今回の良い点は、

```lean
MarkovShadow.ofCapacityKernel
```

が入ったことじゃ。

これは、positive-capacity な `CapacityKernel` に対して、

$$
\mathrm{outgoingCost}(s)=\mathrm{capacity}(s)
$$

が全状態で成り立つなら、正規化後の provider が Markov shadow になる、という一般補題じゃ。

数学的には単純で、

$$
\sum_i \mathrm{cost}(s,i)=\mathrm{capacity}(s)
$$

かつ

$$
\mathrm{capacity}(s) > 0
$$

なら、

$$
\sum_i \frac{\mathrm{cost}(s,i)}{\mathrm{capacity}(s)} = 1
$$

となる。

DKMK-001 から続いてきた構造で言えば、

$$
\text{CapacityKernel}
\to
\text{SubMarkovShadow}
\to
\text{MarkovShadow}
$$

の最後の矢印が、今回入ったわけじゃ。

## 3. `FullChannelLogCostComplete` の意味

もう一つの中心がこれじゃ。

```lean
structure FullChannelLogCostComplete
    (W : PrimePowerWitnessProvider T)
    (C : FullPrimePowerChannelSet T) : Prop where
  outgoing_eq :
    ∀ s : LogCapacityState,
      (C.channels s.1).sum
        (fun q =>
          W.vonMangoldtShadowCost s.1 (C.channels s.1) (C.subset_index s.1) q)
      =
      Real.log (s.1 : ℝ)
```

これは、full channel set 上で

$$
\sum_{q\in C.\text{channels}(n)}
\mathrm{vonMangoldtShadowCost}(n,q) = \log n
$$

が成り立つことを仮定 interface として切り出している。

ここで重要なのは、 **この等式を今回は証明していない** ことじゃ。
証明していない代わりに、「この等式が供給された場合に何が起きるか」をすべて no-sorry で閉じた。

これはよい分離じゃ。

## 4. 何が閉じたか

今回閉じた鎖はこうじゃ。

まず、`FullChannelLogCostComplete W C` があるとする。

つまり、

$$
\sum_{q\in C.\text{channels}(n)}
\mathrm{vonMangoldtShadowCost}(n,q) = \log n
$$

が全 \(n > 1\) で成り立つ。

すると、

```lean
fullGlobalLogCapacityKernel_outgoingCost_eq_capacity
```

により、

$$
(\mathrm{W.fullGlobalLogCapacityKernel}\ C).\mathrm{outgoingCost}(s) =
(\mathrm{W.fullGlobalLogCapacityKernel}\ C).\mathrm{capacity}(s)
$$

が出る。

さらに、

```lean
fullGlobalLogCapacityKernel_normalizedOutgoing_eq_one
```

により、

$$
(\mathrm{W.fullGlobalLogCapacityKernel}\ C).\mathrm{normalizedOutgoing}(s) = 1
$$

が出る。

最後に、

```lean
fullGlobalLogCapacityMarkovShadow
```

で、

$$
\text{full log-capacity route}
$$

が `MarkovShadow` に昇格する。

つまり、full equality が一度手に入れば、Markov route への接続はもう完成しておる。

## 5. 数学的な位置づけ

ここまでの構図は非常に綺麗じゃ。

selected route では、

$$
I(n)\subseteq Full(n)
$$

なので、

$$
\sum_{q\in I(n)}
\frac{\mathrm{cost}(n,q)}{\log n}
\le 1
$$

となり、`SubMarkovShadow` になる。

full route では、

$$
I(n)=Full(n)
$$

かつ

$$
\sum_{q\in Full(n)}\mathrm{cost}(n,q)=\log n
$$

があれば、

$$
\sum_{q\in Full(n)}
\frac{\mathrm{cost}(n,q)}{\log n}
=1
$$

となり、`MarkovShadow` になる。

今回 DKMK-006B で、この二つの違いが Lean の語彙として明確になった。

## 6. 本線との対応

既存の Erdős #1196 Markov route では、

$$
\sum_{q\mid n}\Lambda(q)=\log n
$$

が核じゃった。

DkMath route では、これを直接 \(\Lambda\) で置かず、

$$
\mathrm{vonMangoldtShadowCost}(q) = \log p(q)
$$

として扱っている。

したがって DkMath 版の本線 equality は、

$$
\sum_{q\in Full(n)}
\mathrm{vonMangoldtShadowCost}(n,q) = \log n
$$

じゃ。

今回の `FullChannelLogCostComplete` は、この等式を **Markov 化の必要条件として明示したもの** じゃな。

つまり、DkMath kernel branch はついに、既存 route の

$$
\Lambda(q)/\log n
$$

の Markov kernel と同じ高さまで、構造的には登ってきた。
残るのは、この equality をどう証明するかじゃ。

## 7. 今回の設計が良い理由

今回の設計がよいのは、未証明の重い部分を無理に押し込んでいない点じゃ。

本当に難しいのは、

$$
C.\text{channels}(n)
$$

が全 exponent slot をちょうど一回ずつ含み、

$$
\sum_{q\in C.\text{channels}(n)}\log p(q)=\log n
$$

になることを示す部分じゃ。

そこを今回 `FullChannelLogCostComplete` として interface 化した。

これは、今後二つのルートを許す。

一つは、既存の `T.index n` が本当に full prime-power divisor set であることを証明して、`FullChannelLogCostComplete` を実装する道。

もう一つは、別に canonical full channel enumeration を構成し、その enumeration について `FullChannelLogCostComplete` を示す道。

どちらにも進める。
この自由度は大きい。

## 8. 次に必要なもの

次は報告にもある通り、

$$
T.\text{index}(n)
$$

が全 exponent slot を埋めることを表す構造仮定の設計じゃ。

数学的には、必要なのは次のような主張じゃ。

各 \(n > 1\) について、

$$
C.\text{channels}(n) = {p^k\mid p\text{ prime},\ 1\le k\le n.\mathrm{factorization}(p)}
$$

である。

このとき、

$$
\sum_{q\in C.\text{channels}(n)}
\mathrm{vonMangoldtShadowCost}(n,q) = \sum_p
\sum_{k=1}^{v_p(n)}
\log p
$$

となる。

内側の和は、

$$
\sum_{k=1}^{v_p(n)}\log p = v_p(n)\log p
$$

だから、

$$
\sum_p v_p(n)\log p=\log n
$$

に落ちる。

つまり DKMK-006C 以降の核心は、

$$
\text{full channel enumeration}
$$

と

$$
\log n=\sum_p v_p(n)\log p
$$

を結ぶことじゃ。

## 9. 次段の設計案

わっちなら、次はまだ直接証明へ行かず、もう一段 interface を切る。

たとえば、

```lean
structure FullExponentSlotChannelSet
    (T : PrimePowerDivisorTransitionKernel)
    (C : FullPrimePowerChannelSet T) : Prop where
  mem_iff :
    ∀ n q,
      q ∈ C.channels n ↔
        ∃ p k, Nat.Prime p ∧ 1 ≤ k ∧
          k ≤ n.factorization p ∧ q = p ^ k
```

あるいは、`T.index n` の定義と衝突するなら、`T` に依存しない canonical full slot set を別途作る。

```lean
def fullExponentSlotChannels (n : ℕ) : Finset ℕ := ...
```

ただし、Finset で

$$
{p^k\mid p\mid n,\ 1\le k\le v_p(n)}
$$

を作るには、有限な prime support が必要になる。
ここは `n.factorization.support` を使うのが自然じゃろう。

目標は、

$$
\sum_{q\in fullExponentSlotChannels(n)}
\log(basePrime(q)) = \log n
$$

じゃ。

## 10. 注意点

ここで気をつけたいのは、重複じゃ。

異なる \((p,k)\) から同じ \(q\) が出ることは基本的にない。
なぜなら prime power 表現は一意だからじゃ。

だが Lean では、

$$
p^k=r^\ell \Rightarrow p=r,\ k=\ell
$$

のような補題が必要になる可能性がある。

ただし、Finset を pair \((p,k)\) 上で作り、cost を \(\log p\) として和を取るなら、\(q=p^k\) の一意性を避けられる場合がある。

つまり、次の二案がある。

### 案 A. label \(q\) の Finset で行く

既存 `PrimePowerWitnessProvider` と接続しやすい。
しかし prime-power 表現の一意性が必要になる。

### 案 B. slot \((p,k)\) の Finset で行く

等式

$$
\sum_{p}\sum_{k=1}^{v_p(n)}\log p =
\log n
$$

は証明しやすい。
しかし既存 `q`-label route と接続する bridge が必要になる。

わっちは案 B を先に推す。
なぜなら equality の証明には slot 表現の方が圧倒的に自然だからじゃ。

## 11. 総合判定

DKMK-006B は **Markov equality route の受け皿完成** じゃ。

これで、DkMath kernel branch は三段階を持った。

```text
CapacityKernel:
  Σ cost ≤ capacity

SubMarkovShadow:
  normalized Σ weight ≤ 1

MarkovShadow:
  normalized Σ weight = 1
```

そして full channel route については、

```text
FullPrimePowerChannelSet:
  full channel を選ぶ

FullChannelLogCostComplete:
  full channel の cost が capacity を使い切る

fullGlobalLogCapacityMarkovShadow:
  equality があれば MarkovShadow へ昇格
```

という形が整った。

まだ未踏なのは、

$$
FullChannelLogCostComplete
$$

そのものの証明じゃ。

だが、ここまでの登山はかなり良い。
いよいよ「DkMath kernel は Markov kernel の影である」という標語が、Lean の構造として形になってきた。

次の獲物は明確じゃ。

$$
\text{全 exponent slot の列挙}
\Rightarrow
\sum \log p=\log n
$$

ここを取れば、DkMath 独自ルートは本線の Markov equality に接続する。
