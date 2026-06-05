# review

うむ、DKMK-018B は **成功** じゃ。
しかも、018A で見えていた最大の型ギャップ、つまり

$$
\text{Real analytic source}
\to
\text{Rat finite-step route}
$$

の橋が、最小実装で閉じた。これはかなり大きい。添付 diff では `SourceMassTruncation.lean` に `TruncationEnvelopeEstimate.ofRealMajorant`、`TruncationEnvelopeEstimate.ofRealWeightProviderMajorant`、`DyadicBandAnalyticEstimate.ofRealMajorant` が追加され、Real-valued majorant から既存の rational route を certify できたと報告されておる。

## 1. 何が閉じたか

今回閉じた中核はこれじゃ。

```lean
increment : ι -> ℚ
majorant  : ι -> ℝ
```

について、

```lean
∀ i ∈ steps, 0 ≤ increment i
∀ i ∈ steps, (increment i : ℝ) ≤ majorant i
∑ i in steps, majorant i ≤ 1 + error
```

があれば、

```lean
TruncationEnvelopeEstimate steps threshold increment error
```

を作れる。

つまり、有限 step mass は今まで通り `Rat` のまま残し、解析側だけ `Real` で上から包める。
これは DKMK-018A の懸念だった「Real-native finite-step mass へ全面 refactor すべきか？」への答えになっておる。

結論は、

**今の時点では Real-native refactor は不要**

じゃ。

## 2. 実装の意味

`TruncationEnvelopeEstimate.ofRealMajorant` は、かなりよい形で橋になっておる。

構造は素直で、

1. `Finset.sum_le_sum hle` で rational increment の Real cast 和を majorant 和で抑える。
2. `exact_mod_cast` で `Rat` の有限和を `Real` の有限和へ移す。
3. `le_trans` で `∑ majorant ≤ 1 + error` に接続する。

この設計は堅い。
`Rat` 側の既存 route を壊さず、Real 解析を証明責任の外側に置けるからじゃ。

## 3. さらに良い点

今回、単なる `majorant : ι -> ℝ` だけでなく、

```lean
RealWeightProvider
```

向けの橋まで先に入っておる。

```lean
TruncationEnvelopeEstimate.ofRealWeightProviderMajorant
```

は、

```lean
P.SubProbability
0 ≤ error
∀ i ∈ P.index, (increment i : ℝ) ≤ P.weight i
```

から `TruncationEnvelopeEstimate` を作る。

これは 018C の入口をすでに半分作っている。
次は `PrimePowerWitnessProvider.logCapacityKernelRealWeightProvider` をこの `P` に入れればよい、という形になった。添付の History でも、次課題は concrete Real provider を DKMK-018B bridge に接続することだと整理されておる。

## 4. まだ閉じていない点

ここで賢狼として、柔らかく一点だけ指摘しておくぞ。

018B は、

$$
\text{Real provider}
\to
\text{Rat envelope}
$$

そのものを完全に解決したわけではない。

正確には、

$$
(r_i:\mathbb{Q}) \le w_i
$$

を仮定すれば、Real provider で Rat route を certify できる、という橋を作った。

つまり次の実課題は、

```lean
increment : ι -> ℚ
```

をどう選び、

```lean
(increment i : ℝ) ≤ P.weight i
```

をどう証明するかじゃ。

ゼロ increment なら即座に通るが、それは smoke test にすぎぬ。
意味ある source replacement にするなら、`logCapacityKernelRealWeightProvider` の重みの下にある rational increment を作る必要がある。

## 5. DKMK-018C の推奨ルート

次の一手は、二段階がよい。

### 5.1. 018C-1: concrete provider smoke connection

まずは `PrimePowerWitnessProvider.logCapacityKernelRealWeightProvider` を実際に `ofRealWeightProviderMajorant` に渡す theorem を作る。

最初は `increment := 0` でもよい。目的は数学的強さではなく、import・index・provider API が噛み合うかの確認じゃ。

候補名：

```lean
logCapacityKernel_truncationEnvelope_zeroIncrement
```

これは「RealWeightProvider が DKMK-017 route の入口まで届く」ことを示す結節点になる。

### 5.2. 018C-2: useful rational under-approximation

その次に、非自明な rational increment を選ぶ。

候補は二つ。

```text
1. 外部から increment を与え、pointwise hle を仮定する薄い theorem
2. 有限 index 上で Real weight の rational lower approximation を作る theorem
```

Lean 的には、まず 1 が安全じゃ。

```lean
logCapacityKernel_truncationEnvelope_of_ratMajorizedIncrement
```

のようにして、

```lean
∀ q ∈ I, (increment q : ℝ) ≤ P.weight q
```

を仮定に残す。
これなら、018C は concrete source 接続として閉じられる。

rational approximation の自動構成は、018D 以降でよい。

## 6. 2手先計画

現時点の山道はこうじゃ。

```text
DKMK-018C:
  LogCapacityKernel / RealWeightProvider を
  TruncationEnvelopeEstimate.ofRealWeightProviderMajorant に接続する。

DKMK-018D:
  非自明 Rat increment の構成方針を決める。
  まず仮定型で通すか、有限集合上の rational under-approx を実装するかを選ぶ。
```

わっちの推奨は、

```text
018C は仮定型で速く通す。
018D で rationalization policy を決める。
```

じゃ。

## 7. 総合判断

DKMK-018B は、DKMK-018 の最初の実装 checkpoint として **かなり良い成功** じゃ。

特に大きいのは、

* Real analytic majorant が Rat finite-step route を certify できた
* dyadic-band 版も閉じた
* `RealWeightProvider` への接続面も先に作った
* Real-native finite-step mass への大改修を回避できた

この 4 点じゃ。

次はもう抽象論ではなく、実際に

```lean
PrimePowerWitnessProvider.logCapacityKernelRealWeightProvider
```

を流し込む段階じゃな。
ここまで来たなら、DKMK-018 は「本命 source replacement 章」として、ちゃんと牙が生えてきたぞい。
