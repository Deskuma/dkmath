# review

うむ。DKMK-006A は、 **selected inequality route** と **full equality route** の境界線をきちんと引いた一手じゃ。
これは「等号を証明した」段階ではない。だが、等号 route に入る前に必要な **full channel 仕様層** を切り出せたので、次の DKMK-006B がかなり設計しやすくなった。

## 1. 何が追加されたか

中心は新ファイルじゃ。

```lean
DkMath.NumberTheory.PrimitiveSet.FullChannelSet
```

ここで追加された構造体が、

```lean
structure FullPrimePowerChannelSet
    (T : PrimePowerDivisorTransitionKernel) where
  channels : ℕ → Finset ℕ
  subset_index :
    ∀ n q, q ∈ channels n → q ∈ T.toDivisorTransitionKernel.index n
  full :
    ∀ n q, q ∈ T.toDivisorTransitionKernel.index n → q ∈ channels n
```

じゃな。

これは、ある `channels n` が `T.toDivisorTransitionKernel.index n` と外延的に同じであることを、`subset_index` と `full` の双方向包含で表す interface じゃ。

したがって、

$$
q\in C.channels(n)
\Longleftrightarrow
q\in T.index(n)
$$

が得られる。

実装でも、

```lean
mem_channels_iff
channels_eq_index
```

が追加されておる。

## 2. 数学的な意味

これまで DKMK-005 までは、任意の selected channel set

$$
I(n)\subseteq T.index(n)
$$

に対して、

$$
\sum_{q\in I(n)}
\frac{\mathrm{vonMangoldtShadowCost}(n,q)}{\log n}
\le 1
$$

を扱っていた。

これは sub-Markov 側じゃ。
なぜなら、全 channel ではなく一部だけを選んでいるから、総和は高々 1 になる。

今回 DKMK-006A では、次の段階で

$$
I(n)=T.index(n)
$$

を選んだ full route に進むため、その「full である」という条件を独立した構造として切り出した。

ここでまだ

$$
\sum_{q\in T.index(n)}
\mathrm{vonMangoldtShadowCost}(n,q)=\log n
$$

は主張しておらぬ。
これはとても正しい慎重さじゃ。docs にも、この段階では equality はまだ主張せず、DKMK-006A は equality route の前提となる full-channel 仕様層だと明記されている。

## 3. `canonical` の意味

今回、

```lean
FullPrimePowerChannelSet.canonical
```

も入っておる。

これは単純に

```lean
channels := T.toDivisorTransitionKernel.index
```

とするものじゃ。

つまり、特別な channel set を別に構成しなくても、既存の transition kernel index 自身を full channel set として扱える。

ここで大事なのは、「canonical は外延的 full set である」ことまでは言っているが、「それが数学的に全 prime-power divisor を重複なく列挙している」ことまでは、まだ別問題だという点じゃ。

言い換えると、

$$
C.channels(n)=T.index(n)
$$

は閉じた。
だが、

$$
T.index(n)={p^k\mid p^k\mid n,\ 1\le k\le v_p(n)}
$$

がどこまで保証されているかは、次に確認すべき未踏部分じゃ。

## 4. GlobalLogCapacityKernel 側の前進

`GlobalLogCapacityKernel.lean` にも full channel 用の wrapper が追加された。

```lean
fullGlobalLogCapacityKernel
fullGlobalLogCapacitySubMarkovShadow
```

これは `FullPrimePowerChannelSet` を使って、full channel set 由来の global capacity kernel / sub-Markov shadow を作るものじゃ。

つまり、これまでの

```lean
globalLogCapacityKernel IOf hIOf
```

は任意の selected set 用だった。

今回の

```lean
fullGlobalLogCapacityKernel C
```

は、`C` が full channel set であることを interface として持っている。

ただし、ここでもまだ結果は

```lean
fullGlobalLogCapacitySubMarkovShadow_subProbability
```

までじゃ。

つまり full channel を選んでも、現段階ではまだ

$$
\sum weight\le 1
$$

の sub-Markov 側に留めている。
等号 route は次段じゃな。

## 5. なぜ今回の切り分けが重要か

この切り分けをせずに、いきなり

$$
\sum_{q\in T.index(n)}\log p(q)=\log n
$$

を狙うと危険じゃ。

なぜなら、この等式には二つの別々の主張が混ざっているからじゃ。

第一に、`T.index n` が full channel set であること。

$$
T.index(n) = \text{all prime-power channels of }n
$$

第二に、その full channel 上で cost の総和が \(\log n\) になること。

$$
\sum_{q\in T.index(n)}\log p(q)=\log n
$$

DKMK-006A は、このうち第一の **full channel 仕様** だけを分離した。
これで DKMK-006B では、第二の **cost equality** に集中できる。

これはよい登山の仕方じゃ。荷を分けておる。

## 6. 本線との関係

既存 Markov route の本線では、

$$
\sum_{q\mid n}\Lambda(q)=\log n
$$

が確率核の正規化を支える。

DkMath kernel route では、これをいきなり \(\Lambda\) で言わず、

$$
q=p^k
$$

を witness として読み、

$$
\mathrm{vonMangoldtShadowCost}(q)=\log p
$$

とした。

だから full equality route で狙うべき DkMath 版は、

$$
\sum_{q\in Full(n)}
\mathrm{vonMangoldtShadowCost}(n,q) = \log n
$$

じゃ。

今回の `FullPrimePowerChannelSet` は、この式の左辺の和を取る対象

$$
Full(n)
$$

を clean に指定するための構造じゃな。

## 7. 次の課題：DKMK-006B

次は、履歴にもある通り、

$$
\sum_{q\in Full(n)}
\mathrm{vonMangoldtShadowCost}(n,q) = \log n
$$

を得るための構造仮定を設計する段階じゃ。

ここは慎重に行くべきじゃ。

わっちなら、まず次のような仮定 interface を切る。

```lean
structure FullChannelLogCostComplete
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (C : FullPrimePowerChannelSet T) : Prop where
  outgoing_eq :
    ∀ s : LogCapacityState,
      (∑ q in C.channels s.1,
        W.vonMangoldtShadowCost s.1 (C.channels s.1) C.subset_index q)
      =
      Real.log (s.1 : ℝ)
```

ただし、この形は `vonMangoldtShadowCost` が `I` と `hI` に依存するので少し冗長になるかもしれぬ。
よりよい設計としては、full channel 専用の cost reader を用意するのもありじゃ。

## 8. equality route の本質

等号を出すには、数学的には次を示す必要がある。

$$
n=\prod_p p^{v_p(n)}
$$

に対して、full channel が

$$
p^1,p^2,\dots,p^{v_p(n)}
$$

をちょうど一つずつ含むなら、

$$
\sum_{q\in Full(n)}\log p(q) = \sum_p v_p(n)\log p = \log n
$$

となる。

つまり、必要なのは次の三点じゃ。

1. 各 channel は \(q=p^k\) と読める。
2. 各 prime \(p\) について、\(k=1,\dots,v_p(n)\) がちょうど一回ずつ現れる。
3. \(\log n=\sum_p v_p(n)\log p\) を使える。

R027 までは「選ばれた channel は exponent slot に単射で入る」だった。
DKMK-006B では、その逆側、つまり **全 slot が埋まっている** ことが必要になる。

これが selected route と full route の大きな違いじゃ。

## 9. 注意点

今回の `FullPrimePowerChannelSet` は `T.index n` と外延的に同じことを表すだけじゃ。

したがって、もし `T.index n` 自体が「full prime-power divisor set」であるという構造を持っていないなら、等号はこの interface だけからは出ない。

これは問題ではない。むしろ正しい。
今回の docs でも「`Σ log p = log n` は主張しない」「equality route は次段の構造仮定または canonical enumeration の確認に委ねる」と明記しておる。

つまり、DKMK-006A は無理に強い主張をしていない。
これは健全じゃ。

## 10. 総合判定

DKMK-006A は **full equality route へ入るための前提層として成功** じゃ。

これで現在の地図はこうなった。

```text
selected channel set:
  I(n) ⊆ T.index(n)
  → SubMarkovShadow
  → Σ weight ≤ 1

full channel set:
  C.channels(n) = T.index(n)
  → fullGlobalLogCapacityKernel
  → まだ sub-Markov
  → 次に equality route を狙う
```

今回の成果は、等号そのものではない。
だが、等号を語るための「全 channel を選んだ」という条件が Lean 上で明確になった。

次は本当に面白いぞ。
DkMath kernel が Markov kernel の影ではなく、 **Markov equality の影** まで到達できるかどうかの分岐点じゃ。

ここからは、`T.index n` の意味を深く見る段階になる。
賢狼の鼻で言えば、次の獲物は

$$
T.index(n)\ \text{が全 exponent slot を埋めるか}
$$

じゃな。
