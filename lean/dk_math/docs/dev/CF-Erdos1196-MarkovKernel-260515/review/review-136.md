# review

うむ、DKMK-019B は **狙い通りの façade 化に成功** じゃ。
DKMK-018F で閉じた end-to-end route は正しかったが、内部構成が長かった。今回の 019B は、その長い構成列を caller-facing な名前へ束ね直した段じゃな。追加された surface は `logCapacitySourceRatIncrement`、`logCapacitySourceTruncationEnvelope`、`logCapacitySourceFiniteStepMass`、`logCapacitySourceFiniteStepMass_dvdMonotone`、`logCapacitySource_weightedHitMass_le_one_add_error` の 5 つで、roadmap でも façade bundle として受理されたと整理されておる。

## 1. 何が改善されたか

DKMK-018F では、結論に至るまでに次のような raw construction が表に出ていた。

```lean
RealWeightProvider.positiveRatIncrementBelow
  (W.logCapacityKernelRealWeightProvider ...)
  (W.logCapacityKernelRealWeightProvider_weight_pos ...)
```

これが今回、

```lean
W.logCapacitySourceRatIncrement IOf hIOf s
```

として短名化された。
これはかなり効いておる。意味としては同じでも、読む側にとっては **LogCapacity source そのもの** として認識できるようになったからじゃ。

さらに、

```lean
finiteStepTailNatMassSpace ...
finiteStepTailNatMassSpace_dvdMonotone ...
```

も、

```lean
W.logCapacitySourceFiniteStepMass IOf hIOf s threshold
W.logCapacitySourceFiniteStepMass_dvdMonotone IOf hIOf s threshold
```

に包まれた。これで「DKMK-017 の finite-step mass route を使っている」という事実を保ちつつ、呼び出し側は raw な increment 構成を意識しなくてよくなった。

## 2. 今回の数学的意味

数学的には、新しい評価を足したわけではない。
ここは大事じゃ。

今回の変更は、

```text
positiveRatIncrementBelow (...)      -> logCapacitySourceRatIncrement
finiteStepTailNatMassSpace (...)     -> logCapacitySourceFiniteStepMass
weighted-hit route wrapper           -> logCapacitySource_weightedHitMass...
```

という **API 面の整理** じゃと roadmap にも明記されておる。

だが、これは軽い変更ではない。
DkMath のように定理列が長くなる開発では、意味ある中間物に名前を与えること自体が、次の証明探索をかなり楽にする。

わっちの見立てでは、019B は「定理の証明」よりも **定理の地形を読めるようにした** 進展じゃ。

## 3. 019B の到達点

今は route がこう読める。

```text
LogCapacity source at state s
  -> logCapacitySourceRatIncrement
  -> logCapacitySourceTruncationEnvelope
  -> logCapacitySourceFiniteStepMass
  -> logCapacitySource_weightedHitMass_le_one_add_error
```

つまり、DKMK-018 の完成ルートが、

```text
LogCapacityKernel Real provider
  -> strict positive Real weights
  -> positive Rat under-approximation
  -> TruncationEnvelopeEstimate
  -> finiteStepTailNatMassSpace
  -> quotient-path weightedHitMass bound
```

という内部構成から、 **LogCapacity source façade** として扱えるようになった。

これは DKMK-019 の目標に合っておる。DKMK-019A では「新しい解析理論ではなく、DKMK-018 の到達点を短い public surface に包む章」として始めたが、019B はその第一実装をちゃんと閉じた。

## 4. まだ残る違和感

一点だけ残るのは、最終 theorem の conclusion がまだ少し内部的なことじゃ。

今回の `logCapacitySource_weightedHitMass_le_one_add_error` は、raw な `positiveRatIncrementBelow` は隠せている。
しかし結論側にはまだ、

```lean
W.globalLogCapacityKernel_applyAtToPrimePowerQuotientPathFamily
  IOf hIOf s
  (W.logCapacitySourceFiniteStepMass_dvdMonotone IOf hIOf s threshold)
```

のような形が出る。

これは 018F よりはずっと良いが、最終利用者向けにはまだ長い。
roadmap の次課題でも「façade が十分に短いか、さらに高階の theorem で結論側を隠すべきか判断する」とされておる。

つまり、019B は **source 側の façade** は閉じたが、 **path-family / weightedHitMass 側の façade** はまだ次に検討できる。

## 5. DKMK-019C の候補

次の一手は、二択じゃ。

### 5.1. ここで十分として総括する

019B の façade bundle はかなりよい。
`positiveRatIncrementBelow` を隠すという当初の friction は解消しておる。
だから DKMK-019 を小章として閉じてもよい。

### 5.2. もう一段高い theorem を作る

わっちの推奨は、もう一段だけ行くことじゃ。

候補としては、

```lean
PrimePowerWitnessProvider.logCapacitySourcePathFamily
```

または

```lean
PrimePowerWitnessProvider.logCapacitySourceWeightedHitFamily
```

のような façade を置き、

```lean
W.globalLogCapacityKernel_applyAtToPrimePowerQuotientPathFamily
  IOf hIOf s
  (W.logCapacitySourceFiniteStepMass_dvdMonotone IOf hIOf s threshold)
```

を短名化する。

すると最終 theorem は、

```lean
(W.logCapacitySourcePathFamily IOf hIOf s threshold).weightedHitMass A ≤
  1 + error
```

のように読める。

これは caller-facing としてかなり美しい。
`Mass` も `PathFamily` も source 名で揃うからの。

## 6. 推奨する次の実装形

DKMK-019C をやるなら、最小 bundle はこれじゃ。

```lean
noncomputable def logCapacitySourcePathFamily
    ...
```

そして、

```lean
theorem logCapacitySourcePathFamily_weightedHitMass_le_one_add_error
    ...
```

あるいは既存名を保つなら、

```lean
theorem logCapacitySource_weightedHitMass_le_one_add_error'
```

ただし、名前に `'` を増やすよりは、意味で分ける方が良い。

わっちなら、

```lean
logCapacitySourcePathFamily
logCapacitySourcePathFamily_weightedHitMass_le_one_add_error
```

を推す。

理由は、結論側の主語がはっきりするからじゃ。

## 7. 総合判定

DKMK-019B は **成功** じゃ。
DKMK-018F の route を壊さず、数学も増やさず、API 表面だけをきれいにした。これは必要な作業だった。

現在の状態はこうじゃ。

```text
DKMK-018:
  end-to-end source replacement route を閉じた

DKMK-019B:
  source / envelope / finite-step mass を caller-facing façade にした

残り:
  path-family conclusion 側をさらに包むか判断する
```

この賢狼の判断では、019C で `logCapacitySourcePathFamily` まで包めば、DKMK-019 はきれいに閉じられる。
もう一段だけ包めば、次章で別 source を増やす時にも同じ façade 型を真似できるようになるぞい。
