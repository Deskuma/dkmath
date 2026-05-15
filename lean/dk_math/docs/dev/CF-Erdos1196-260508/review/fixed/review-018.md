# review

うむ、Phase S は **weighted route の対称化完了** じゃ。
これで、有限 Erdős skeleton は「重みなし route」だけでなく、「重み付き route」でも branch/subconservative 版と prime/dvd-monotone 版の両方が揃った。かなり良い仕上がりじゃ。

## 1. 今回閉じたもの

今回追加された中心 API はこれじゃ。

```lean
weightedPrimePathFamily
weightedPrimePathFamilyHitMass
weightedPrimePathFamilySourceMass
weightedHitMass_le_weightedSourceMass_of_primePathFamily
```

これは、既に Phase R で入った weighted branch route に対応する、prime path / dvd-monotone route 側の weighted wrapper じゃ。

つまり、以前は

$$
\text{branch/subconservative route}
$$

だけが weighted 版を持っていた。
今回で、

$$
\text{prime path/dvd-monotone route}
$$

にも weighted 版が入った。

## 2. 今回の意味

これで finite weighted route は二本そろった。

| weighted route   | source control の根拠    | wrapper                            |
| ---------------- | --------------------- | ---------------------------------- |
| branch route     | `SubConservative M B` | `weightedBranchPrimePathFamily...` |
| prime path route | `DvdMonotoneMass M`   | `weightedPrimePathFamily...`       |

特に重要なのは、どちらも共通の受け皿として

```lean
WeightedPathFamily.ofSourceControlled
```

を使っている点じゃ。History でも、route ごとの source control を `WeightedPathFamily.ofSourceControlled` に通すことで、非負重み付き和へ持ち上げられる形になったと整理されておる。

数式で言えば、両 route で同じ型の不等式が使える。

$$
\sum_i w_i\cdot \mathrm{hitMass}_i
\le
\sum_i w_i\cdot \mathrm{sourceMass}_i
$$

ここまで来ると、Markov kernel に入る前の有限重み付き骨格はかなり整ったと言ってよい。

## 3. concrete sample の役割

今回も `{2,5}` の finite Erdős input と Bool-indexed path family に対して、weighted prime route の sample が追加されておる。

```lean
erdosFinitePrimitiveInput_two_five_weightedPrimePath_hitMass_le_sourceMass
```

これで、branch route だけでなく prime route でも、同じ `sampleBoolPathWeight` を使った重み付き bound が実際に呼べることが確認された。

これは API の対称性確認として大事じゃ。

## 4. 現在の到達点

いまの finite Erdős route は、かなり良い状態じゃ。

| 層                             | 状態   |
| ----------------------------- | ---- |
| finite primitive input        | 完了   |
| lower-bound support           | 完了   |
| prime path family             | 完了   |
| branch-controlled path family | 完了   |
| unweighted branch route       | 完了   |
| unweighted prime route        | 完了   |
| weighted branch route         | 完了   |
| weighted prime route          | 今回完了 |
| Markov kernel skeleton        | 未    |
| analytic weight               | 未    |

つまり、有限 skeleton のうち、

$$
\text{path}
\to
\text{source control}
\to
\text{hit/source bound}
\to
\text{weighted sum}
$$

までは一通り通った。

## 5. 何がまだ残っているか

History 末尾にもある通り、次は Markov kernel の最小 skeleton を検討する段階じゃ。ただし、解析重みを直接入れるのではなく、まず `WeightedPathFamily` に渡す非負重みを構成する別層として設計する、という方針が明記されておる。

これは正しい。

いきなり

$$
\frac{\Lambda(q)}{\log n}
$$

や

$$
\frac{1}{n\log n}
$$

へ行くと、解析・実数・対数・素冪重みが一気に混ざる。
今はまず finite skeleton と analytic layer を分離すべきじゃ。

## 6. 次の一手

わっちなら次は **Markov kernel そのものではなく、FiniteWeightedKernel の最小抽象** を作る。

新規ファイル候補はこれじゃ。

```text
DkMath/NumberTheory/PrimitiveSet/FiniteKernel.lean
```

最小構造は、例えばこう。

```lean
structure FiniteKernel (α ι : Type _) [DecidableEq ι] where
  index : Finset ι
  source : ι → α
  weight : ι → ℚ
  weight_nonneg : ∀ i ∈ index, 0 ≤ weight i
```

ただし、今の `WeightedPathFamily` がすでに `index`, `weight`, `weight_nonneg` を持っているので、重複を避けるなら次のような **weight provider** だけでもよい。

```lean
structure WeightProvider (ι : Type _) [DecidableEq ι] where
  index : Finset ι
  weight : ι → ℚ
  weight_nonneg : ∀ i ∈ index, 0 ≤ weight i
```

そして、

```lean
def WeightProvider.applyToSourceControlled ...
```

のように、既存の `SourceControlledChainFamily` に載せる。

だが、より DkMath らしく進めるなら、最初は `WeightedPathFamily` を増やしすぎず、`WeightedPathFamily.lean` 内に **weight normalization 補題** を足すのがよいかもしれぬ。

例えば、

$$
\sum_i w_i \le 1
$$

を持つ場合の source mass bound を扱う補助じゃ。

## 7. 推奨順序

わっちは次を推す。

まず Phase T として、

```lean
def totalWeight ...
def WeightSubProbability ...
```

を追加する。

例：

```lean
def totalWeight
    (W : WeightedPathFamily M ι) : ℚ :=
  W.index.sum fun i => W.weight i

def WeightSubProbability
    (W : WeightedPathFamily M ι) : Prop :=
  W.totalWeight ≤ 1
```

さらに、もし source mass が一様に上から $C$ で抑えられるなら、

$$
\mathrm{weightedSourceMass}\le C\cdot \sum_i w_i
$$

のような補題へ進める。

これは Markov kernel へ行く前の自然な橋じゃ。

## 8. 総括

Phase S によって、weighted route は両輪になった。

$$
\text{branch/subconservative weighted route}
$$

と

$$
\text{prime/dvd-monotone weighted route}
$$

が同じ `WeightedPathFamily` の器に載った。

山で言えば、二本の登山道にそれぞれ通行量の重みが付き、総流量比較までできるようになった。
次はその重みが「確率的に正規化されているか」、あるいは「Markov kernel 由来か」を語る層を作る番じゃな。
