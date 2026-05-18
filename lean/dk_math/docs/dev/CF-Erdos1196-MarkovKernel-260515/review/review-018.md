# review

うむ。DKMK-007C は **かなり重要な本線復帰フェーズ** じゃ。
DKMK-007A で `RealWeightProvider` から `RealWeightedPathFamily` へ橋を掛け、DKMK-007B で `SubMarkovShadow` / `MarkovShadow` から primitive hitting へ直接渡せる wrapper を作った。今回 DKMK-007C では、その wrapper を **具体的な log-capacity shadow** に接続した。つまり、抽象 bridge が、いよいよ DkMath kernel の実体へ刺さったわけじゃ。

## 1. 今回の核心

新規 module はこれじゃ。

```lean
DkMath.NumberTheory.PrimitiveSet.LogCapacityHittingBridge
```

追加された route は 2 系統ある。

```text
selected log-capacity SubMarkovShadow
  + F.index = IOf s.1
  → primitive real-weighted hit mass ≤ C
```

```text
canonical exponent-slot MarkovShadow
  + F.index = canonicalExponentSlotLabels s.1
  → primitive real-weighted hit mass ≤ C
```

これにより、DKMK-006 系で作った

```lean
globalLogCapacitySubMarkovShadow
canonicalExponentSlotMarkovShadow
```

が、primitive hitting bound へ theorem-facing に接続された。

## 2. selected route の意味

selected route 側では、次が追加された。

```lean
PrimePowerWitnessProvider.globalLogCapacitySubMarkovShadow_providerAt_compatible
PrimePowerWitnessProvider.globalLogCapacitySubMarkovShadow_applyAtToSourceControlled
PrimePowerWitnessProvider.globalLogCapacitySubMarkovShadow_weightedHitMass_le_const
```

ここでの互換条件は、

```lean
IOf s.1 = F.index
```

じゃ。

つまり、状態 (s) の自然数成分 (s.1) に対して、selected channel set (IOf(s.1)) と source-controlled chain family (F) の index が一致すれば、`globalLogCapacitySubMarkovShadow` の provider を (F) に載せられる。

その結果、primitive set (A) について、

$$
weightedHitMass(A)\le C
$$

が出る。

この (C) は、各 source mass の一様上界じゃ。

$$
\forall q\in F.index,\quad \mu(F.source(q))\le C
$$

selected route はもともと full equality ではなく、

$$
\sum weight\le 1
$$

の route じゃから、`SubMarkovShadow` として扱うのが自然じゃ。今回、その自然な route が hitting 側へ届いた。

## 3. canonical route の意味

canonical route 側では、次が追加された。

```lean
canonicalExponentSlotMarkovShadow_providerAt_compatible
canonicalExponentSlotMarkovShadow_applyAtToSourceControlled
canonicalExponentSlotMarkovShadow_weightedHitMass_le_const
```

こちらの互換条件は、

```lean
canonicalExponentSlotLabels s.1 = F.index
```

じゃ。

つまり、canonical exponent-slot labels を index とする source-controlled chain family があれば、canonical Markov shadow をそのまま (F) に適用できる。

canonical route は DKMK-006F/G で Markov equality まで到達していた道じゃ。
したがって、ここでは `SubProbability` を別途仮定せず、`MarkovShadow` 側から自動的に hitting bound へ進む。

この違いは美しい。

```text
selected route:
  SubMarkovShadow
  external hS.SubProbability / built theorem
  inequality route

canonical route:
  MarkovShadow
  total weight = 1
  equality route
```

Lean の theorem shape に、数学の分岐がそのまま現れておる。

## 4. DKMK-007A/B/C の鎖

ここまでの DKMK-007 系は、かなり綺麗につながった。

```text
DKMK-007A:
  RealWeightProvider
  → RealWeightedPathFamily
  → primitive weighted hit bound
```

```text
DKMK-007B:
  SubMarkovShadow / MarkovShadow
  → RealWeightedPathFamily
  → primitive weighted hit bound
```

```text
DKMK-007C:
  globalLogCapacitySubMarkovShadow / canonicalExponentSlotMarkovShadow
  → RealWeightedPathFamily
  → primitive weighted hit bound
```

つまり、抽象 provider から始まった橋が、今回で具体的な log-capacity shadow まで届いた。

これは本線復帰として大きいぞい。

## 5. 数学的に何が進んだか

Erdős #1196 型の骨格では、欲しい構図はこうじゃ。

```text
log-capacity kernel weight
→ divisibility chain family
→ primitive hitting bound
```

DKMK-006 までは、主に左側を作っていた。

```text
CapacityKernel
→ normalized provider
→ SubMarkovShadow / MarkovShadow
```

DKMK-007A/B で中央の bridge を作った。

```text
RealWeightProvider / shadow
→ SourceControlledChainFamily
→ weighted hitting
```

今回 DKMK-007C で、左側と中央が具体的につながった。

```text
log-capacity shadow
→ SourceControlledChainFamily
→ primitive hitting
```

したがって、今後必要なのは右側の concrete 化、つまり (F) の構成じゃ。

## 6. 今回の設計判断の良い点

今回、compatibility を theorem 内で無理に構成せず、外部引数にしているのがよい。

selected route では、

```lean
hindex : IOf s.1 = F.index
```

canonical route では、

```lean
hindex : canonicalExponentSlotLabels s.1 = F.index
```

を仮定する。

これは柔軟じゃ。
なぜなら、`SourceControlledChainFamily` の具体構成は今後いくつか候補が出る可能性があるからじゃ。

* selected (IOf) に合わせる family
* canonical exponent-slot labels に合わせる family
* 将来の equivalence bridge を通した family
* local toy / sanity check 用 family

これらを最初から一つに固定しない。
`F.index` が合えば hitting bridge に乗れる、という形にしてある。

これは DKMK-006J の三本 route map と相性がよい。

## 7. 何がまだ残っているか

今回の docs でも次課題として明記されている通り、まだ (F) 自体の concrete constructor は外部入力じゃ。

つまり、現在の到達点はこう。

```text
log-capacity shadow と compatible な F があれば、
primitive weighted hit mass ≤ C が出る
```

残るのはこう。

```text
その compatible な SourceControlledChainFamily F を、
selected / canonical route から自然に作る
```

ここが DKMK-007D の本命になる。

## 8. 次の一手

わっちなら DKMK-007D は、まず constructor を小さく切る。

候補はこうじゃ。

```lean
SourceControlledChainFamily.ofIndex
```

または、より DkMath らしく、

```lean
SourceControlledChainFamily.ofDivisorChains
```

最初は chain の中身を欲張らず、index と source を揃える thin constructor がよい。

目標は次の 2 つ。

```lean
F.index = IOf s.1
```

```lean
F.index = canonicalExponentSlotLabels s.1
```

を自然に `rfl` または薄い simp で供給できる形にすることじゃ。

特に canonical route では、

```text
canonicalExponentSlotLabels s.1
```

を index にした `SourceControlledChainFamily` を作れれば、今回の

```lean
canonicalExponentSlotMarkovShadow_weightedHitMass_le_const
```

にそのまま渡せる。

## 9. 総合判定

DKMK-007C は **log-capacity shadow と primitive hitting bound の具体接続に成功** じゃ。

ここまでの流れはこうなった。

```text
DKMK-001〜006J:
  DkMath capacity kernel / shadow / canonical route を構築

DKMK-007A:
  RealWeightProvider を real weighted path family へ接続

DKMK-007B:
  SubMarkovShadow / MarkovShadow を hitting bridge へ接続

DKMK-007C:
  globalLogCapacitySubMarkovShadow / canonicalExponentSlotMarkovShadow を hitting wrapper へ接続
```

これはもう、抽象地図ではない。
DkMath kernel が primitive hitting API に実際に食い込み始めておる。

次の山は明確じゃ。

```text
DKMK-007D:
  SourceControlledChainFamily の concrete constructor を整備し、
  index compatibility を自然供給する。
```

ぬしよ、これは良い進み方じゃ。
山頂で作った `MarkovShadow` が、ついに primitive set の hitting 谷へ水路を伸ばし始めた。次はその水路に、具体的な chain family という石組みを入れる番じゃな。
