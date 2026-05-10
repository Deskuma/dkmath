# review

## 1. 結論

うむ、Phase X は **finite kernel route の対称化完了** じゃ。
Phase W では kernel wrapper が branch/subconservative route 側に入った。今回 Phase X で、prime path / dvd-monotone route 側にも同じ kernel wrapper が入り、

$$
\text{state}
\to
\text{WeightProvider}
\to
\text{WeightedPathFamily}
\to
\mathrm{weightedHitMass}\le C
$$

の導線を、二系統の source-control route で対称に使えるようになった。これは綺麗な前進じゃ。

## 2. 今回追加された核

今回の中心はこの二つじゃ。

```lean
kernelPrimePathFamilyAt
kernelPrimePathFamilyAt_hitMass_le_const_of_subprob
```

前者は、finite kernel の state (s) から得た provider を、`primePathFamilySourceControlled` に適用する wrapper。

後者は、`DvdMonotoneMass M` による prime path route でも、

$$
K\text{ sub-probability}
+
\text{source mass}\le C
+
S\text{ primitive}
\Rightarrow
\mathrm{weightedHitMass}\le C
$$

を出す theorem じゃ。

これで branch route と prime route の対応がそろった。

## 3. 二本の kernel route が並んだ

現在の kernel route はこう整理できる。

| route        | source control の根拠    | kernel wrapper                  |
| ------------ | --------------------- | ------------------------------- |
| branch route | `SubConservative M B` | `kernelBranchPrimePathFamilyAt` |
| prime route  | `DvdMonotoneMass M`   | `kernelPrimePathFamilyAt`       |

前者は宇宙式 Mass / Branch 側。

$$
\sum_{\text{child}}\mu(child)\le \mu(parent)
$$

後者は整除単調性側。

$$
h\mid source\Rightarrow \mu(h)\le \mu(source)
$$

この二つが、同じ finite kernel skeleton の上で走れるようになった。
つまり、重み供給の仕組みは共通化され、質量制御の根拠だけを route ごとに差し替えられる。

これは設計としてかなりよい。

## 4. concrete sample の意味

今回追加された sample は、

```lean
erdosFinitePrimitiveInput_two_five_kernelPrimePath_hitMass_le_one
```

じゃ。

これは `sampleUnitFiniteKernel` を prime path route に適用し、({2,5}) の finite Erdős input に対して、

$$
\mathrm{weightedHitMass}\le 1
$$

を確認している。

Phase W では branch route で同様の sample が通っていた。
今回で prime route でも通ったので、

$$
\text{kernel branch sample}
\quad\text{と}\quad
\text{kernel prime sample}
$$

が揃ったわけじゃ。

## 5. 現在地

ここまでで finite Erdős skeleton は、かなり整ってきた。

| 層                                        | 状態   |
| ---------------------------------------- | ---- |
| primitive hitting                        | 完了   |
| path family / forest                     | 完了   |
| source-controlled mass                   | 完了   |
| weighted path family                     | 完了   |
| WeightProvider                           | 完了   |
| FiniteKernel                             | 完了   |
| kernel branch route                      | 完了   |
| kernel prime route                       | 今回完了 |
| compatibility alias / simp API           | 未    |
| actual finite Markov transition skeleton | 未    |
| analytic weight                          | 未    |

特に重要なのは、今回で

$$
\text{FiniteKernel}
$$

が単なる branch route 専用ではなくなったことじゃ。
ちゃんと `branch/subconservative` と `prime/dvd-monotone` の両方に対応できる **共通の重み供給骨格** になった。

## 6. 何がまだ足りないか

次に残るのは、History でも書かれている通り、

```lean
FiniteKernel.CompatibleAt
```

のような compatibility alias / simp API の整理か、あるいは actual finite Markov transition skeleton への前進じゃ。

いま theorem には毎回、

```lean
(K.providerAt s).Compatible (...)
```

が出てくる。

これは中身としては、

$$
K.index(s)=F.index
$$

という単純な index 一致条件じゃが、 theorem 文ではやや長い。
今後 kernel route が増えると、この書き方が重くなる。

だから次に、

```lean
def CompatibleAt
    (K : FiniteKernel σ ι) (s : σ)
    (F : SourceControlledChainFamily M ι) : Prop :=
  (K.providerAt s).Compatible F
```

のような alias を入れるのはかなり自然じゃ。

## 7. 次の一手

わっちなら次は **compatibility API 整備** を推す。

理由は、actual Markov transition へ入る前に、kernel 周辺の theorem 文を少し軽くした方が後で効くからじゃ。

候補はこのあたり。

```lean
FiniteKernel.CompatibleAt
FiniteKernel.compatibleAt_iff
FiniteKernel.applyAtToSourceControlled_of_compatibleAt
```

そして可能なら simp 補題として、

```lean
providerAt_index
providerAt_weight
compatibleAt_iff_index_eq
```

を置く。

これで、次に状態 (n) と index (q) に意味を持たせるとき、theorem 文がすっきりする。

## 8. その次の山道

compatibility API が整ったら、いよいよ

$$
\sigma := \mathbb{N},
\qquad
\iota := \text{除去因子 } q
$$

のように、状態と index に数論的意味を持たせる段階じゃ。

最小 skeleton は、まだ (\Lambda(q)/\log n) なしでよい。

たとえば、

```lean
structure FiniteDivisorKernel where
  ...
```

のようにして、

$$
q\mid n
$$

を index 条件に持たせる。
その後で、Markov 的重み

$$
w(n,q)
$$

を入れる。

解析重み

$$
w(n,q)=\frac{\Lambda(q)}{\log n}
$$

はさらに後でよい。

## 9. 総括

Phase X は、派手な新理論ではないが、かなり大切な **左右対称化** じゃ。

これで、

$$
\text{state}
\to
\text{WeightProvider}
\to
\text{WeightedPathFamily}
\to
\mathrm{weightedHitMass}\le C
$$

が、

* branch/subconservative route
* prime/dvd-monotone route

の両方で使えるようになった。

山で言えば、有限 kernel という配給所から、宇宙式 Mass 側の登山道にも、整除単調性側の登山道にも、同じように荷を配れるようになった。
次は道標、つまり `CompatibleAt` まわりを整えるのがよいのぅ。
