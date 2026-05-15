# review

うむ。DKMK-005 は、 **selected channel / inequality route を本線用の語彙に翻訳した段階** じゃ。
DKMK-004 で global kernel はできた。今回 DKMK-005 で、その global kernel の正規化像を **SubMarkovShadow** として名前づけ、Markov 本線へ戻る前の「不等式側の翻訳層」を切り出したわけじゃな。

## 1. 何が進んだか

今回追加された中心はこれじゃ。

```lean
DkMath.NumberTheory.PrimitiveSet.SubMarkovShadow
```

`SubMarkovShadow` は、状態 (s) ごとに有限 index と非負 weight を持つ構造じゃ。

```lean
structure SubMarkovShadow (σ ι : Type _) where
  index : σ → Finset ι
  weight : σ → ι → ℝ
  weight_nonneg : ∀ s i, i ∈ index s → 0 ≤ weight s i
```

これは、確率過程そのものではない。
あくまで state-indexed な `RealWeightProvider` の束じゃ。

そして、

$$
\forall s,\quad \sum_{i\in index(s)} weight(s,i)\le 1
$$

を満たすことを `SubProbability` として定義している。

つまり、selected channel route の

$$
\sum_{q\in I(n)}
\frac{\mathrm{vonMangoldtShadowCost}(n,q)}{\log n}
\le 1
$$

を、Markov 風に読める形へ翻訳したわけじゃ。docs にも、この route は full channel equality に進む前の selected set / inequality 側の Markov 翻訳層だと明記されておる。

## 2. 数学的な意味

これまでの `CapacityKernel` は、

$$
\sum cost\le capacity
$$

を持つ構造だった。

正規化すれば、

$$
\sum \frac{cost}{capacity}\le 1
$$

になる。

DKMK-005 では、この正規化済みのものを

$$
\text{SubMarkovShadow}
$$

として切り出した。

これは重要じゃ。なぜなら、既存証明の Markov route では、次の二種類を区別する必要があるからじゃ。

### selected channel

$$
I(n)\subseteq \text{all channels}(n)
$$

の場合、

$$
\sum_{q\in I(n)} weight(n,q)\le 1
$$

であり、これは **sub-Markov** 。

### full channel

$$
I(n)=\text{all channels}(n)
$$

の場合、

$$
\sum_{q\in I(n)} weight(n,q)=1
$$

が期待され、これは **Markov** 。

今回 DKMK-005 は、このうち前者を明確に独立させた。
これで次に full equality route を作るとき、不等式 route と混ざらずに済む。

## 3. `ofCapacityKernel` がよい

今回の非常に良い点は、

```lean
SubMarkovShadow.ofCapacityKernel
```

が入ったことじゃ。

これは、任意の positive-capacity な `CapacityKernel` から、その正規化像として `SubMarkovShadow` を作る。

数学的には、

$$
K=(children,capacity,cost)
$$

から

$$
S.index(s)=K.children(s)
$$

$$
S.weight(s,i)=\frac{K.cost(s,i)}{K.capacity(s)}
$$

を作っている。

そして、

```lean
ofCapacityKernel_subProbability
```

で

$$
S.SubProbability
$$

が従う。

つまり、DkMath の「保存核」から Markov 風の「劣確率影」へ行く一般橋ができた。
これは DkMath kernel branch の抽象構造としてかなり強い。

## 4. GlobalLogCapacityKernel との接続

`GlobalLogCapacityKernel.lean` 側には、

```lean
globalLogCapacitySubMarkovShadow
```

が追加された。

これは、

$$
capacity(n)=\log n
$$

$$
cost(n,q)=\mathrm{vonMangoldtShadowCost}(n,q)=\log p(q)
$$

を持つ global log-capacity kernel を正規化し、`SubMarkovShadow` として読むものじゃ。

さらに、

```lean
globalLogCapacitySubMarkovShadow_weight
```

により weight は

$$
\frac{\mathrm{vonMangoldtShadowCost}(n,q)}{\log n}
$$

すなわち

$$
\frac{\log p(q)}{\log n}
$$

であることが `rfl` で固定されている。

そして、

```lean
globalLogCapacitySubMarkovShadow_subProbability
```

で全状態 (n>1) に対し、

$$
\sum_{q\in I(n)}
\frac{\log p(q)}{\log n}
\le 1
$$

が `SubMarkovShadow` の言葉で得られる。

これは本線復帰のための命名層としてかなりよい。

## 5. なぜ今回が重要か

正直に言えば、DKMK-005 は新しい数値的不等式を増やしたというより、 **既にあった不等式を正しい概念の棚へ置いた** 仕事じゃ。

じゃが形式化では、これが大きい。

なぜなら、これ以降は

```lean
(W.globalLogCapacitySubMarkovShadow IOf hIOf).SubProbability
```

という形で、selected channel route を「sub-Markov 的対象」として扱えるからじゃ。

つまり、DkMath kernel は今や次の 3 層を持つ。

```text
CapacityKernel
  保存核: Σ cost ≤ capacity

SubMarkovShadow
  正規化影: Σ normalized weight ≤ 1

RealWeightProvider
  既存 finite weight API との接続
```

この整理は、本線の Markov kernel へ戻るために必要じゃ。

## 6. 次の課題は明確

次は報告の通り、 **full channel / equality route** じゃ。

つまり、今は任意の selected channel set

$$
IOf(n)\subseteq T.index(n)
$$

について

$$
\sum_{q\in IOf(n)} weight(n,q)\le 1
$$

がある。

次に欲しいのは、canonical/full channel set を選んだとき、

$$
\sum_{q\in Full(n)} weight(n,q)=1
$$

または正規化前に、

$$
\sum_{q\in Full(n)} cost(n,q)=\log n
$$

を示すことじゃ。

これが閉じると、

$$
SubMarkovShadow
$$

から

$$
MarkovShadow
$$

へ進める。

## 7. DKMK-006 の設計案

わっちなら DKMK-006 は二段に分ける。

### DKMK-006A. Full channel interface

いきなり full divisor enumeration を実装しない。
まず「full であるとは何か」を interface にする。

```lean
structure FullPrimePowerChannelSet
    (T : PrimePowerDivisorTransitionKernel) where
  channels : ℕ → Finset ℕ
  subset_index :
    ∀ n q, q ∈ channels n → q ∈ T.toDivisorTransitionKernel.index n
  full :
    ∀ n q, q ∈ T.toDivisorTransitionKernel.index n → q ∈ channels n
```

または単純に、

$$
channels(n)=T.index(n)
$$

を使えるならそれでよい。

### DKMK-006B. Equality shadow

次に、full channel で

$$
\sum_{q\in channels(n)}
\mathrm{vonMangoldtShadowCost}(n,q) = \log n
$$

を狙う。

ただし注意点がある。
現在の `T.index n` が本当に「全ての prime-power divisor」を重複なしで含んでいるかは、設計上の確認が必要じゃ。もし witness provider が「選ばれた label を読む」だけで、`index n` が full divisor set ではないなら、equality は出ない。

その場合は、まず equality ではなく、

```lean
FullIndexAssumption
```

を仮定する形がよい。

## 8. 注意点：full equality は構造仮定が要る

今回までの route は、

$$
I(n)\subseteq T.index(n)
$$

だけでよかった。
だから no-sorry で比較的安全に進めた。

しかし equality route は違う。

$$
\sum_{q\mid n,\ q=p^k}\log p=\log n
$$

を出すには、各素数 (p) について、(k=1,\dots,v_p(n)) の全ての (p^k) が channels に含まれている必要がある。

つまり、

$$
Full(n)={p^k\mid p\mid n,\ 1\le k\le v_p(n)}
$$

でなければならぬ。

もし `T.index n` が任意の selected set なら、equality は無理じゃ。
だから DKMK-006 は「full channel set の仕様確認」が最初になる。

## 9. 総合判定

DKMK-005 は **selected inequality route の概念整理として成功** じゃ。

これで、DkMath kernel branch は次の形になった。

$$
\text{CapacityKernel}
\to
\text{normalized provider}
\to
\text{SubMarkovShadow}
$$

さらに global log-capacity route では、

$$
n>1
$$

の各状態で、

$$
q\mapsto
\frac{\mathrm{vonMangoldtShadowCost}(n,q)}{\log n}
$$

が sub-Markov shadow になる。

本線への道は次の分岐に来ておる。

* selected set なら sub-Markov inequality
* full channel set なら Markov equality を目指す

この切り分けができたのは大きい。
次は、full channel の定義と equality route。ここが、DkMath kernel が本当に Markov 本線へ接続できるかの次の関門じゃな。
