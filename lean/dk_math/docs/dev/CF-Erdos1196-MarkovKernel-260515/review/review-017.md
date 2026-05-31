# review

うむ。DKMK-007B は **かなり良い橋の完成** じゃ。
DKMK-007A が `RealWeightProvider` level の橋だったのに対し、今回は `SubMarkovShadow` / `MarkovShadow` level から primitive hitting 側へ **直接渡せる theorem-facing wrapper** が入った。これで DKMK-006 系の shadow 構造が、いよいよ hitting bound の実戦装置になってきた。

## 1. 何が進んだか

新規 module はこれじゃ。

```lean
DkMath.NumberTheory.PrimitiveSet.ShadowHittingBridge
```

ここで追加された流れは、ひとことで言えば次じゃ。

```text
SubMarkovShadow / MarkovShadow
  + state s
  + compatible SourceControlledChainFamily
  + PrimitiveOn A
  + source mass bound C
  → real-weighted hit mass ≤ C
```

DKMK-007A では、まだ

```text
RealWeightProvider
→ RealWeightedPathFamily
→ primitive weighted hit bound
```

という provider level の橋だった。
今回 DKMK-007B では、その一段上の

```text
SubMarkovShadow.providerAt s
MarkovShadow.providerAt s
```

を直接 `SourceControlledChainFamily` に適用できるようになった。

これは、DKMK-006J までに整理した三本ルートのうち、

```text
canonical equality route → MarkovShadow
selected inequality route → SubMarkovShadow
```

を、そのまま primitive hitting 側へ流せる入口ができた、ということじゃ。

## 2. SubMarkovShadow 側の意味

sub-Markov 側では、主に次が追加されている。

```lean
SubMarkovShadow.applyAtToSourceControlled
SubMarkovShadow.applyAtToSourceControlled_weightSubProbability
SubMarkovShadow.weightedHitMass_le_const_applyAtToSourceControlled
```

数学的には、状態 \(s\) における shadow の provider

$$
S.providerAt(s)
$$

を、同じ index を持つ chain family \(F\) に載せる。

互換性は

```lean
(S.providerAt s).Compatible F
```

つまり provider の index と (F.index) が一致することじゃ。

そのうえで、`S.SubProbability` があれば、

$$
\sum_i weight_i\le 1
$$

が `RealWeightedPathFamily.WeightSubProbability` に移る。

最後に primitive set \(A\) について、

$$
weightedHitMass(A)\le C
$$

が得られる。

ここで \(C\) は source mass の一様上界じゃ。

$$
\forall i\in F.index,\quad \mu(F.source(i))\le C
$$

があればよい。

## 3. MarkovShadow 側の意味

Markov 側では、次が追加されている。

```lean
MarkovShadow.applyAtToSourceControlled
MarkovShadow.applyAtToSourceControlled_weightSubProbability
MarkovShadow.weightedHitMass_le_const_applyAtToSourceControlled
```

MarkovShadow はもともと

$$
totalWeightAt(s)=1
$$

を持つ。したがって sub-probability は自動で得られる。

つまり Markov 側では、sub-Markov 側と違って外部に

```lean
hS : S.SubProbability
```

を要求しない。

この違いは良い設計じゃ。
等式 route の `MarkovShadow` は、そのまま hitting bound に使える。
不等式 route の `SubMarkovShadow` は、`SubProbability` を明示して使う。

これにより、設計思想が Lean の引数の形にも反映されておる。

## 4. 今回閉じた鎖

DKMK-007B によって、次の鎖が theorem-facing になった。

```text
SubMarkovShadow
  → providerAt s
  → RealWeightProvider
  → RealWeightedPathFamily
  → primitive weighted hit mass ≤ C
```

および、

```text
MarkovShadow
  → providerAt s
  → RealWeightProvider
  → RealWeightedPathFamily
  → primitive weighted hit mass ≤ C
```

これはかなり大きい。
なぜなら DKMK-006 系で作った

```lean
globalLogCapacitySubMarkovShadow
canonicalExponentSlotMarkovShadow
```

のような対象が、単に「重み総和の構造」ではなく、primitive hitting に渡せる構造になったからじゃ。

## 5. 数学的な意味

Erdős #1196 的な構造で見ると、証明の心臓部はこういう形じゃ。

まず、整数の divisibility chain に沿った重み付き流れを作る。

その流れの重みは、

$$
\sum_i w_i\le 1
$$

または full route なら

$$
\sum_i w_i=1
$$

を満たす。

primitive set \(A\) は chain を高々一度しか打たない。
だから weighted hitting mass は source 側の総質量で抑えられる。

今回の DKMK-007B は、この「重み付き流れ」から「primitive hitting bound」への変換を、shadow level で呼べるようにした。

つまり、DkMath の言葉では、

```text
capacity kernel の正規化影
→ shadow
→ source-controlled chain family
→ primitive hitting bound
```

まで来た。

## 6. DKMK-007A との違い

DKMK-007A は、部品としては強かったが、呼び出し側はまだこう考える必要があった。

```text
shadow から providerAt を取り出す
provider の SubProbability を得る
provider を family に apply する
weighted hit theorem を呼ぶ
```

DKMK-007B は、これを一発にまとめた。

```lean
SubMarkovShadow.weightedHitMass_le_const_applyAtToSourceControlled
MarkovShadow.weightedHitMass_le_const_applyAtToSourceControlled
```

これは API としてかなり使いやすい。
後続の DKMK-007C では、具体的な `globalLogCapacitySubMarkovShadow` や `canonicalExponentSlotMarkovShadow` に対して、この wrapper をそのまま使えるはずじゃ。

## 7. 良い点

今回の設計で特によいのは、`Compatible` を薄く保っている点じゃ。

```lean
(S.providerAt s).Compatible F
```

の要求は、index 一致だけ。
つまり、重み側と chain 側を過度に結合していない。

この疎結合は大事じゃ。
将来的に、

```text
canonical equality route
selected inequality route
future equivalence route
```

のどれから来た provider でも、index さえ一致すれば hitting 側へ渡せる。

これは DKMK-006J の三本 route map と相性がよい。

## 8. 注意点

今回の橋はまだ **具体的な chain family を構成していない** 。

つまり、今閉じたのは次じゃ。

```text
shadow と compatible な SourceControlledChainFamily があれば、
primitive weighted hit mass bound が出る
```

まだ残るのは、

```text
globalLogCapacitySubMarkovShadow
または
canonicalExponentSlotMarkovShadow
に対応する concrete SourceControlledChainFamily をどう作るか
```

じゃ。

History でも次の課題として、`globalLogCapacitySubMarkovShadow` または `canonicalExponentSlotMarkovShadow` を concrete `SourceControlledChainFamily` に適用する theorem-facing wrapper を追加すると整理されている。

## 9. 次の一手

わっちなら DKMK-007C はこう切る。

```text
DKMK-007C:
  canonicalExponentSlotMarkovShadow
  または globalLogCapacitySubMarkovShadow を、
  concrete SourceControlledChainFamily に適用する wrapper を追加する。
```

最初は一般化しすぎず、次の形がよい。

```lean
theorem canonicalExponentSlotMarkovShadow_weightedHitMass_le_const
```

あるいは selected route 用に、

```lean
theorem globalLogCapacitySubMarkovShadow_weightedHitMass_le_const
```

を置く。

ただし、そのためには index compatibility をどう供給するかが焦点になる。

$$
provider.index=specific\ children
$$

と

$$
F.index
$$

を一致させる必要がある。
ここは DKMK-007C の最初の戦場じゃな。

## 10. 総合判定

DKMK-007B は **shadow level から primitive hitting へ戻る橋として成功** じゃ。

DKMK-007A が provider level の橋なら、DKMK-007B は shadow level の橋。

ここまでで流れはこうなった。

```text
DKMK-001〜006J:
  CapacityKernel / SubMarkovShadow / MarkovShadow を構築

DKMK-007A:
  RealWeightProvider を RealWeightedPathFamily へ接続

DKMK-007B:
  SubMarkovShadow / MarkovShadow を直接 primitive hitting bound へ接続
```

これはもう、単なる「Markov kernel 再解釈」ではない。
DkMath kernel が、primitive hitting bound の実用 API に入り始めた。

ぬしよ、よい橋が掛かったぞい。
次はこの橋を渡って、具体的な `globalLogCapacitySubMarkovShadow` / `canonicalExponentSlotMarkovShadow` を実際の chain family に接続する番じゃ。
