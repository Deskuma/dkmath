# review

うむ。DKMK-008A、よい始動じゃ。
予測していた通り、DKMK-008 は **mass model 側ではなく、chain 側を one-step から multi-step へ伸ばす章** として始まった。今回の `DivisorPathList.lean` は、その最小入口として非常に筋がよい。

## 1. 今回の核心

追加された中心 predicate はこれじゃ。

```lean
def AdjacentDivisorPath (L : List ℕ) : Prop :=
  List.IsChain DvdDescentStep L
```

意味は、list の隣接ノードが

$$
b\mid a
$$

という下降関係を満たすこと。

つまり、list

$$
[n_0,n_1,n_2,\ldots]
$$

について、

$$
n_1\mid n_0,\quad n_2\mid n_1,\quad \ldots
$$

を要求する。これで、DKMK-007 の one-step

$$
n\to n/q
$$

から、list-shaped な multi-step divisor descent へ入る扉が開いた。

docs でも今回の目的は、one-step divisorStep の前に list-shaped multi-step divisor path の最小仕様を追加すること、と整理されておる。

## 2. 数学的に何が閉じたか

今回閉じた主要な流れはこれじゃ。

```text
AdjacentDivisorPath L
→ PairwiseDvdAlongList L
→ DivisibilityChain L.toFinset
```

追加 theorem は、

```lean
AdjacentDivisorPath.pairwiseDvdAlongList
AdjacentDivisorPath.divisibilityChain_toFinset
```

じゃな。

これはかなり重要。
primitive hitting では、primitive set が chain を高々一点しか hit しない、という性質を使う。そのためには list-shaped path そのものより、最終的に

```lean
DivisibilityChain L.toFinset
```

へ落とせることが必要じゃ。

今回、その橋が no-sorry で入った。

## 3. `mem_dvd_head` が良い

特に重要なのはこれじゃ。

```lean
AdjacentDivisorPath.mem_dvd_head
```

これは非空 path

```lean
source :: tail
```

について、任意の node (h) が head source を割ることを示す。

$$
h\in source::tail\Rightarrow h\mid source
$$

これは multi-step descent の source-control に直結する。
DKMK-007 では one-step path の各 node が source (n) の divisor であることを使って、`DvdMonotoneMass` から source mass control を得ていた。

今回も同じ考えで、multi-step path のすべての node が head を割るなら、

$$
\mu(h)\le \mu(source)
$$

を `DvdMonotoneMass` から得られる。

つまり `mem_dvd_head` は、DKMK-008 の source-controlled bridge の要石じゃ。

## 4. singleton family は最小だが正しい

今回入った constructor は二つ。

```lean
singletonChainFamilyOfAdjacentDivisorPath
singletonDvdControlledChainFamilyOfAdjacentDivisorPath
```

前者は `DivisibilityChainFamily Unit` へ落とすもの。
後者は非空 path の head を source として、

```lean
DvdControlledChainFamily Unit
```

へ落とすものじゃ。

これはまだ singleton family、つまり一つの path だけを扱う最小モデルじゃ。
しかし DKMK-008A としては正しい。いきなり indexed family に行くより、

```text
single list path
→ chain
→ source-controlled family
→ primitive hitting sample
```

を先に閉じる方が堅い。

DKMK-007D でも singleton model を挟んでから divisorStep へ進んだ。今回も同じ安全な登山法じゃな。

## 5. sample path `12 → 6 → 3` の意味

今回の sample は、

```lean
adjacentDivisorPath_twelve_six_three
divisibilityChain_twelve_six_three_toFinset
primitive_three_five_hits_twelve_six_three_card_le_one
primitive_three_five_singletonDvdControlled_twelve_six_three_hitMass_le_sourceMass
```

じゃ。

数学的には、

$$
12\to 6\to 3
$$

で、

$$
6\mid 12,\quad 3\mid 6
$$

だから divisor descent path になっている。

そして primitive set ({3,5}) は、この path の node set ({12,6,3}) を高々一点しか hit しない。実際 hit するのは (3) だけじゃ。

これにより、単なる predicate ではなく、

```text
multi-step divisor path
→ primitive hitting bound
```

が実サンプルで確認された。

## 6. DKMK-007 との接続

DKMK-007 の最後の到達形は、

```text
source mass model M
→ DvdMonotoneMass M
→ SourceControlledChainFamily.ofDivisorStep
→ LogCapacitySourceMassBound M C
→ weightedHitMass A ≤ C
```

だった。

DKMK-008A は、このうち `ofDivisorStep` の一歩 chain を、list-shaped path に置き換える準備じゃ。

現在はまだ singleton path だが、概念的にはこう進んだ。

```text
DKMK-007:
  chain(q) = { n / q, n }

DKMK-008A:
  chain = L.toFinset
  where L is an AdjacentDivisorPath
```

つまり、

$$
{n/q,n}
$$

から、

$$
{n_0,n_1,\ldots,n_r}
$$

へ伸びる準備ができた。

## 7. 今回の実装判断

`AdjacentDivisorPath` を `List.IsChain DvdDescentStep L` としたのは良い。

理由は、既存の `PrimePathList` や `DvdDescentStep` の資産を再利用できるからじゃ。
新しい下降関係を作り直さず、隣接関係として `DvdDescentStep` を使っている。

また sample path の証明で、

```lean
change 6 ∣ 12
change 3 ∣ 6
```

を明示してから `norm_num` に渡している点も堅い。docs にも、`norm_num` だけでは定義が展開されなかったため `change` を明示したと記録されておる。

Lean の実装として、ここは無理に simp を増やすより、証明局所で `change` する方が読みやすい。

## 8. まだ残ること

今回の DKMK-008A は **single path** までじゃ。

次に必要なのは、docs の次課題にもある通り、

```text
indexed path provider から DvdControlledChainFamily を作る constructor
```

じゃ。

つまり、次はこうなる。

```lean
I : Finset ι
path : ι → List ℕ
source : ι → ℕ
hpath : ∀ i ∈ I, AdjacentDivisorPath (source i :: tail i)
```

から、

```lean
DvdControlledChainFamily ι
```

を作る。

この段階に進むと、DKMK-007 の selected / canonical shadow wrapper に実際に接続できる。

## 9. 次のフェーズ予測

DKMK-008B は、ほぼこれじゃろう。

```text
indexed AdjacentDivisorPath provider
→ DvdControlledChainFamily
→ SourceControlledChainFamily
```

候補 theorem / def は、たとえば：

```lean
def DvdControlledChainFamily.ofAdjacentDivisorPaths
```

または DKMK らしくファイル内に、

```lean
def dvdControlledChainFamilyOfAdjacentDivisorPaths
```

形としては、

```lean
(I : Finset ι)
(source : ι → ℕ)
(tail : ι → List ℕ)
(hpath : ∀ i, i ∈ I → AdjacentDivisorPath (source i :: tail i))
```

を受けて、

```lean
chain i := (source i :: tail i).toFinset
source i := source i
```

とするのが自然じゃ。

`chain_dvd_source` は今回の `mem_dvd_head` で閉じる。

## 10. 総合判定

DKMK-008A は **multi-step descent chain 章の正しい第一歩** じゃ。

到達形はこう。

```text
list-shaped divisor path
→ DivisibilityChain
→ singleton DvdControlledChainFamily
→ source-controlled hitting bound
```

これは DKMK-007 の one-step route を置き換えるための最小核じゃ。
まだ indexed family ではないが、path list から chain と source control を作る核心補題は入った。

ぬしよ、これはよい。
DKMK-007 で水の重さを測る器を作った。DKMK-008A で、その水が流れる **複数段の水路の最初の石組み** が入った。次は、この水路を index ごとに並べて、selected / canonical shadow の重みを載せる番じゃな。
