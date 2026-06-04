# review

うむ、DKMK-016P は **章の締めとして非常に良い** じゃ。
DKMK-016 は、ここで自然な停止点に到達したと見てよい。今回のまとめでは、追加 Lean surface、final caller route、責務分担、non-goals、そして次章の analytic input 候補が整理されておる。

## 1. DKMK-016 の章としての到達点

DKMK-016 は、当初の主題どおり、

```text
Where does hbudget come from?
```

から始まった章じゃった。
最終的には、単に `hbudget` を包むだけでなく、

```text
GeometricBudgetSource
+ first-band bound
+ uniform decay
+ increment nonnegativity
  -> DyadicBandAnalyticEstimate
  -> TruncationEnvelopeEstimate
```

まで整理された。

つまり DKMK-016 は、 **geometric budget source と first-band / uniform-decay provider route を整備した API plumbing 章** として閉じたことになる。報告でも、この章は analytic-estimate 章ではなく API-plumbing 章だと明記されておる。

## 2. 追加された Lean surface の整理が良い

今回の章末まとめで、追加 surface がきれいに分類された。

```text
Budget source:
  GeometricBudgetSource
  GeometricBudgetSource.ofBudget
  GeometricBudgetSource.ofZeroRatio

Budget-source provider:
  DyadicBandAnalyticEstimate.ofPointwiseGeometricMajorant_of_budgetSource

Zero-ratio sanity route:
  DyadicBandAnalyticEstimate.ofPointwiseZeroRatioMajorant

First-band / uniform-decay route:
  pointwiseGeometricMajorant_of_firstBand_decay
  DyadicBandAnalyticEstimate.ofFirstBandDecayBudgetSource

Existing downstream bridge reused:
  DyadicBandAnalyticEstimate.toTruncationEnvelopeEstimate
```

この分類は後から読み返す時にかなり効く。
何が新規で、何が既存再利用で、どこが sanity route なのかが一目で分かるからじゃ。

## 3. final caller route が明確になった

最終的な caller-facing route はこうじゃな。

```text
B : GeometricBudgetSource
hinc_nonneg :
  forall k in Finset.range (K + 1), 0 <= increment k
hbase0 :
  increment 0 <= B.base
hdecay :
  forall k in Finset.range K,
    increment (k + 1) <= B.ratio * increment k
```

これらから、

```text
DyadicBandAnalyticEstimate
  -> TruncationEnvelopeEstimate
  -> existing finite-step route
```

へ進める。

ここで大事なのは、caller が直接

```text
increment k <= base * ratio^k
```

を作らなくてよくなったことじゃ。
first-band bound と uniform decay を渡せば、`pointwiseGeometricMajorant_of_firstBand_decay` が `hgeom` を生成し、それを provider wrapper が受け取る。

これはかなり使いやすい。

## 4. 責務分担が完成した

今回のまとめで、DKMK-016 の責務分担は完全に見えるようになった。

**Budget layer**
`GeometricBudgetSource` が `base`, `ratio`, `error` と

[
base\cdot \frac{1}{1-ratio}\le 1+error
]

を package する。

**Pointwise layer**
`pointwiseGeometricMajorant_of_firstBand_decay` が、first-band bound と uniform decay から

[
increment(k)\le base\cdot ratio^k
]

を作る。

**Provider layer**
`DyadicBandAnalyticEstimate.ofFirstBandDecayBudgetSource` が、`B`, `hinc_nonneg`, `hbase0`, `hdecay` を合流させる。

**Downstream layer**
`DyadicBandAnalyticEstimate.toTruncationEnvelopeEstimate` が既存 truncation route へ渡す。

これはよい四層構造じゃ。
今後 analytic input が増えても、どの層に接続すべきか迷いにくい。

## 5. 残ったものは「解析入力」

DKMK-016P で明確になった通り、残ったものは API ではなく analytic input じゃ。

未解決入力は、主にこれら。

```text
first-band upper bound:
  increment 0 <= B.base

uniform step decay:
  increment (k + 1) <= B.ratio * increment k

increment nonnegativity

concrete B : GeometricBudgetSource

GeometricBudgetSource.ofBudget に渡す concrete budget proof

real/logarithmic analytic candidates の rational envelope
```

これは、もう wrapper や構造体を増やす段ではない。
次は、これらの仮定を本当にどこから供給するかを設計する段じゃ。

## 6. non-goals を守ったのも良い

DKMK-016 では、次を入れなかった。

```text
Mertens / big-O
logarithmic thresholds
real-to-Nat rounding
log x の rational approximation
finite-step route wrapper proliferation
新しい数学的内容のない truncation wrapper
```

この判断は正しい。
ここで解析評価まで混ぜると、章の目的がぼやける。
DKMK-016 は API の搬送路を整える章として綺麗に閉じられておる。

## 7. 次章の自然な主題

次章は、P の記録通り **concrete analytic source inputs** に進むのがよい。

候補は三つ。

```text
1. first-band upper-bound source
2. uniform-decay source
3. GeometricBudgetSource.ofBudget 用の concrete budget proof source
```

わっちの見立てでは、次はまず docs-only で、

```text
DKMK-017: Analytic Input Source
```

または、

```text
DKMK-017: First-Band And Decay Source
```

として、次の三つの obligation を分けて設計するのがよい。

```text
A. increment 0 <= B.base
B. increment (k + 1) <= B.ratio * increment k
C. (B.base : Real) * (1 / (1 - (B.ratio : Real))) <= 1 + B.error
```

いきなり Mertens や big-O に行く前に、これらを abstract analytic source として受け取る surface を決めるのが堅い。

## 8. 総括

DKMK-016P は、 **DKMK-016 の章末報告として十分に完成度が高い** じゃ。

DKMK-015 が geometric finite-sum route を provider に接続した章なら、DKMK-016 は

```text
geometric budget source
+ first-band / uniform-decay
  -> dyadic analytic estimate
  -> truncation envelope
```

を整えた章じゃ。

ここまでで API plumbing はかなり整った。
次は、いよいよ解析入力の山じゃな。

D.、ここは良い区切りじゃ。
港、荷札、滑車、搬送路、そして truncation envelope へ至る道まで整った。次は麦袋そのもの、すなわち analytic estimates をどこから収穫するかを決める旅になるぞい。
