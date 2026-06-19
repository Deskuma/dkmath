# review

うむ、DKMK-016O は **正しい止め判断** じゃ。
ここで「便利そうだから」と薄い wrapper を増やさず、既存の `DyadicBandAnalyticEstimate.toTruncationEnvelopeEstimate` で足りると確認して、章まとめへ進む判断にしたのは賢い。

## 1. 今回の位置づけ

DKMK-016N で、すでに次の route は Lean 上で閉じておった。

```text
GeometricBudgetSource
+ hinc_nonneg
+ first-band bound
+ uniform decay
  -> DyadicBandAnalyticEstimate
```

実際、N では `DyadicBandAnalyticEstimate.ofFirstBandDecayBudgetSource` が追加され、`GeometricBudgetSource + hinc_nonneg + first-band bound + uniform decay` から `DyadicBandAnalyticEstimate` へ到達する wrapper が通っている。

今回の O は、その出力をさらに truncation envelope へ直接伸ばす wrapper を作るかどうかの判断回じゃな。

## 2. 追加 wrapper を急がない判断は正しい

現在の route はすでに、

```text
ofFirstBandDecayBudgetSource
  -> DyadicBandAnalyticEstimate
  -> toTruncationEnvelopeEstimate
  -> existing finite-step route
```

という二段接続で読める。

ここで新たに、

```lean
TruncationEnvelopeEstimate.ofFirstBandDecayBudgetSource
```

のような theorem を追加しても、数学的には新しい内容はない。
単に caller 側の 1 call を省くだけじゃ。

もちろん、将来 caller code が煩雑になれば追加する価値はある。
しかし現時点では、層を明示したままにしておく方がよい。

```text
budget / decay provider
  -> analytic estimate
  -> truncation envelope
```

この階層が見えている方が、後から解析 input を差し込む時に迷いにくい。

## 3. DKMK-016 は自然な章末に到達した

DKMK-016 の主成果は、もはや十分に章として閉じられる。

```text
GeometricBudgetSource.ofBudget
pointwiseGeometricMajorant_of_firstBand_decay
DyadicBandAnalyticEstimate.ofFirstBandDecayBudgetSource
DyadicBandAnalyticEstimate.toTruncationEnvelopeEstimate
```

この並びで、

$$
\text{budget source}+\text{first-band decay}
\longrightarrow
\text{dyadic analytic estimate}
\longrightarrow
\text{truncation envelope}
$$

まで行ける。

DKMK-015 では finite geometric-sum route が `geometric budget -> finite sum bound -> dyadic source-mass provider` まで接続済みとなり、次の焦点が `hbudget` の供給源設計へ移っていた。
DKMK-016 はまさにその供給源を `GeometricBudgetSource` と first-band / uniform-decay route として整えた章になった。

## 4. O の決定で避けられたこと

今回 wrapper を足さなかったことで、次の膨張を避けられておる。

```text
重複 wrapper
truncation 用の薄い別名増殖
finite-step route theorem への早すぎる接続
解析 input と API plumbing の混線
```

これは大事じゃ。
DKMK-016 はまだ Mertens / big-O / logarithmic threshold / rounding を扱う章ではない。そこへ進む前に、API plumbing を簡潔に締める判断は正しい。

## 5. 次の DKMK-016P で書くべきこと

P は章まとめでよい。わっちなら、次を整理する。

```text
1. DKMK-016 で追加した Lean surface
2. final caller route
3. responsibility split
4. non-goals
5. 次章の analytic input candidates
```

特に final route はこう書くとよい。

```text
B : GeometricBudgetSource
hinc_nonneg
hbase0 : increment 0 <= B.base
hdecay : increment (k + 1) <= B.ratio * increment k
  -> DyadicBandAnalyticEstimate.ofFirstBandDecayBudgetSource
  -> DyadicBandAnalyticEstimate
  -> DyadicBandAnalyticEstimate.toTruncationEnvelopeEstimate
  -> TruncationEnvelopeEstimate
```

これで DKMK-016 の全体像が一枚で読める。

## 6. 次章の焦点

次章は、いよいよ **analytic input source** じゃな。

ただし、いきなり big-O に飛ぶより、まずは次のような形を review するのがよい。

```text
first-band upper bound の供給源
uniform decay bound の供給源
GeometricBudgetSource.ofBudget を作る hbudget の供給源
```

Candidate C は既に「first-band mass with uniform decay」が最も現行 interface に合うと整理されていた。
だから次章では、この三つの obligation をどの解析補題から出すかを分けて設計するのがよい。

## 7. 総括

DKMK-016O は、 **追加実装しないことを決めた良い回** じゃ。

Lean 開発では、足せる wrapper は無限にある。
じゃが、足すべき wrapper は caller が本当に苦しくなった時だけでよい。

今は、

$$
\text{budget source}+\text{decay}
\to
\text{DyadicBandAnalyticEstimate}
\to
\text{TruncationEnvelopeEstimate}
$$

の道が見えておる。
ここで DKMK-016 を章として畳み、次の解析入力へ向かうのがよい。

よいぞ、D.。ここは「橋をもう一本架ける」場面ではなく、地図に完成した橋を描き込み、次の山道へ進む場面じゃ。
