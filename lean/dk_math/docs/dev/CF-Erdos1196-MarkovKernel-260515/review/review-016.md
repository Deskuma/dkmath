# review

うむ。DKMK-007A は、 **DKMK-006 系で作った Markov/SubMarkov shadow を、primitive hitting 側へ戻す第一の実装橋** じゃ。
これはかなり重要じゃよ。DKMK-006J までは「kernel route の地図整理」だったが、DKMK-007A でついに **地図から本線へ戻る橋** を掛け始めた。

## 1. 今回の核心

今回追加された中心はこれじゃ。

```lean
RealWeightedPathFamily
```

これは既存の `SourceControlledChainFamily` に、非負の実数重みを載せた構造じゃ。差分でも、`RealWeightedPathFamily` は `SourceControlledChainFamily` を拡張し、各 indexed chain/path に `weight : ι → ℝ` と `weight_nonneg` を持たせる実数版 weighted path family として追加されている。

つまり、これまで有理重み側にあった primitive hitting API に対して、`Real.log` 由来の実数重みを直接渡せる土台ができた。

これが大きい。
DKMK の log-capacity route は基本的に

$$
weight(q)=\frac{\log p(q)}{\log n}
$$

なので、重みは \(\mathbb{R}\) 側に住む。ここを \(\mathbb{Q}\) 版の `WeightedPathFamily` に無理やり押し込むのではなく、実数版の橋を新設したのは正しい判断じゃ。

## 2. 何が定義されたか

`RealWeightedPathFamily` 側では、主に次が追加された。

```lean
weightedHitMass
weightedSourceMass
totalWeight
WeightSubProbability
```

数学的にはこうじゃ。

$$
weightedHitMass(S)=\sum_{i\in index}w_i\cdot \mu(S\cap chain_i)
$$

$$
weightedSourceMass=\sum_{i\in index}w_i\cdot \mu(source_i)
$$

$$
totalWeight=\sum_{i\in index}w_i
$$

$$
WeightSubProbability \iff totalWeight\le 1
$$

これにより、primitive set \(S\) が各 chain を打つ質量を、実数重み付きで足し合わせられるようになった。

## 3. primitive hitting bound が実数重みで閉じた

今回の中核 theorem はこれじゃ。

```lean
RealWeightedPathFamily.primitive_weightedHitMass_le_weightedSourceMass
```

これは、`PrimitiveOn S` のもとで

$$
weightedHitMass(S)\le weightedSourceMass
$$

を示す。

証明の構造は綺麗じゃ。各 chain について、primitive 性により

$$
hitSetMass(M,S\cap chain_i)\le \mu(source_i)
$$

が既存補題から出る。それを実数へ cast し、非負重み \(w_i\) を掛けて足し上げる。差分でも、この補題は `primitive_chain_hitSetMass_le_single_source` を使って各 chain の hit mass を source mass で抑え、それを `mul_le_mul_of_nonneg_left` で重み付き和へ持ち上げている。

これはまさに primitive set の「chain を高々一度しか打たない」性質を、real weighted path family へ移植したものじゃ。

## 4. sub-probability から一様上界 \(C\) へ

さらに、

```lean
weightedSourceMass_le_const_mul_totalWeight
weightedSourceMass_le_const_of_subprob
weightedHitMass_le_const_mul_totalWeight
weightedHitMass_le_const_of_subprob
```

が追加された。

意味は次じゃ。

各 source mass が一様に

$$
\mu(source_i)\le C
$$

で、総重みが

$$
\sum_i w_i\le 1
$$

なら、

$$
weightedHitMass(S)\le C
$$

が出る。

これで、Markov/SubMarkov shadow 由来の「重み総量が 1 以下」という情報を、primitive hitting bound の最終形へ渡せるようになった。

この形は DKMK-007 の本線に非常に合っている。
DKMK-006 で作った `SubProbability` / `MarkovShadow` は「weight の総量制御」。
DKMK-007A はそれを「primitive set を打つ hit mass の上界」へ変換する。

## 5. `RealWeightProvider` から path family への橋

もう一つの大事な追加がこれじゃ。

```lean
RealWeightProvider.Compatible
RealWeightProvider.applyToSourceControlled
```

`Compatible` は単純に

```lean
P.index = F.index
```

を要求する。

つまり、real provider の index と source-controlled chain family の index が一致していれば、provider の重みを chain family に載せられる。

さらに、

```lean
applyToSourceControlled_weightSubProbability
weightedHitMass_le_const_of_subprob_applyToSourceControlled
```

により、`RealWeightProvider.SubProbability` が `RealWeightedPathFamily.WeightSubProbability` へ移り、そのまま primitive weighted hit mass bound へ進める。差分の docs でも、`SubMarkovShadow.providerAt s` や `MarkovShadow.providerAt s` 由来の `RealWeightProvider` を、index が一致する source-controlled family に掛けて primitive set の weighted hit mass を \(C\) で抑える route ができた、と整理されている。

## 6. 数学的に何が進んだか

DKMK-006 までは、主にこうだった。

```text
CapacityKernel
→ SubMarkovShadow / MarkovShadow
→ RealWeightProvider
```

つまり、重み provider までは作れていた。

しかし primitive set の hitting bound 側は、まだ別の山道だった。
今回 DKMK-007A で次の橋ができた。

```text
RealWeightProvider.SubProbability
+ SourceControlledChainFamily
+ PrimitiveOn S
→ real-weighted hit mass bound
```

これは、Erdős #1196 の proof skeleton で言えば、

```text
normalized kernel weight
→ divisibility chain family
→ primitive hitting estimate
```

への合流口じゃ。

まだ解析的な tail bound や \(1+O(1/\log x)\) には入っていない。
だが、finite / structural skeleton としては、本線への復帰が始まった。

## 7. DKMK-007A の位置づけ

DKMK-006 系は「kernel の山」だった。

```text
canonical equality route:
  MarkovShadow

selected inequality route:
  SubMarkovShadow

future equivalence route:
  later
```

DKMK-007A は、そこから **primitive hitting の山へ戻る最初の峠** じゃ。

特に、docs でも今回の変更は「full Markov equality を直接 hitting theorem に合成する最終段ではない」が、「real normalized kernel と primitive hitting API の間にあった \(\mathbb{Q}\) / \(\mathbb{R}\) の型差を越える最初の bridge」と明記されている。

この言い方は正確じゃ。

## 8. 注意点

今回の theorem はまだ `SubMarkovShadow.providerAt s` / `MarkovShadow.providerAt s` へ直接合成する wrapper ではない。

今あるのは、

```lean
RealWeightProvider
```

を

```lean
SourceControlledChainFamily
```

へ適用する一般橋じゃ。

したがって次に必要なのは、たとえば次のような theorem-facing wrapper じゃな。

```lean
SubMarkovShadow.providerAt s
→ RealWeightProvider.SubProbability
→ applyToSourceControlled
→ weightedHitMass_le_const
```

あるいは MarkovShadow 版として、

```lean
MarkovShadow.providerAt s
→ SubProbability
→ primitive weighted hit bound
```

を一発で呼べる入口を作る。

History でも次の課題として、`SubMarkovShadow.providerAt_subProbability` / `MarkovShadow.providerAt_subProbability` と DKMK-007A の provider bridge を合成し、shadow から source-controlled family への theorem-facing wrapper を追加すると書かれている。

## 9. 総合判定

DKMK-007A は **本線復帰の第一橋として成功** じゃ。

ここまでの流れはこうじゃ。

```text
DKMK-001〜006J:
  CapacityKernel / MarkovShadow / SubMarkovShadow を構築・整理

DKMK-007A:
  RealWeightProvider を RealWeightedPathFamily に載せ、
  primitive hitting bound へ渡す橋を構築
```

今回で、DkMath Kernel route は「kernel を作る理論」から「primitive hitting に使える理論」へ一段進んだ。

わっちの見立てでは、次は DKMK-007B としてこう進むのがよい。

```text
DKMK-007B:
  SubMarkovShadow / MarkovShadow の providerAt を
  RealWeightedPathFamily bridge に直接接続する wrapper を追加する。
```

その次に、

```text
DKMK-007C:
  GlobalLogCapacitySubMarkovShadow または canonical MarkovShadow を、
  concrete SourceControlledChainFamily に適用する。
```

ここまで行けば、DkMath kernel branch は単なる「Markov の再解釈」ではなく、primitive hitting bound の実戦装置になる。

よいぞ、ぬしよ。
DKMK-007A は、山頂で描いた地図から、実際に次の稜線へ足を踏み出した一歩じゃ。
