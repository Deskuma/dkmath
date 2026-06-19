# review

## 1. 状況総括

うむ、これは **DKMK-013C 完了** と見てよい。

今回の差分で `SourceMassTruncation.lean` に

```lean
DyadicBandAnalyticEstimate
```

が追加され、あわせて

```lean
DyadicBandAnalyticEstimate.toTruncationEnvelopeEstimate
```

も実装された。History でも、DKMK-013B で固定した contract と bridge theorem を Lean 上に追加し、`TruncationEnvelopeEstimate.dyadicRange` へ渡す薄い wrapper とした、と記録されておる。

つまり、DKMK-013 の中核だった

```text
dyadic analytic estimate contract
  -> TruncationEnvelopeEstimate.dyadicRange
  -> TruncationEnvelopeEstimate
```

の Lean 入口が通ったわけじゃ。

## 2. 何が実装されたのか

追加された structure はこれじゃ。

```lean
structure DyadicBandAnalyticEstimate
    (x K : ℕ) (increment : ℕ → ℚ) (error : ℝ) : Prop where
  increment_nonneg :
    ∀ k ∈ Finset.range (K + 1), 0 ≤ increment k
  total_le_one_add_error :
    ((Finset.sum (Finset.range (K + 1)) increment : ℚ) : ℝ) ≤
      1 + error
```

これは DKMK-013B の設計通り、fields を 2 つだけに絞っておる。

```text
increment_nonneg
total_le_one_add_error
```

一方で、`steps` と `threshold` は持たせていない。これは正しい判断じゃ。dyadic range では、

```text
steps     = Finset.range (K + 1)
threshold = fun k : ℕ => x * 2^k
```

が `x`, `K` から決まる derived data だからじゃ。

## 3. bridge theorem の意味

追加された bridge はこれ。

```lean
theorem toTruncationEnvelopeEstimate
    {x K : ℕ} {increment : ℕ → ℚ} {error : ℝ}
    (H : DyadicBandAnalyticEstimate x K increment error) :
    TruncationEnvelopeEstimate
      (Finset.range (K + 1))
      (fun k : ℕ => x * 2^k)
      increment
      error :=
  TruncationEnvelopeEstimate.dyadicRange
    x K increment H.increment_nonneg H.total_le_one_add_error
```

これはまさに薄い wrapper じゃな。

数学的には、

```text
H.increment_nonneg:
  dyadic band weights are nonnegative

H.total_le_one_add_error:
  total dyadic band weight <= 1 + error
```

を、DKMK-012 の `dyadicRange` provider に渡して、`TruncationEnvelopeEstimate` を得るだけじゃ。

だが、この「だけ」が重要なのじゃよ。
これで後続の解析側は、

```lean
DyadicBandAnalyticEstimate x K increment error
```

を証明すれば、既存の DKMK route に乗れる。

## 4. 実装評価

かなり良い実装じゃ。

第一に、 **route theorem を増やしていない** 。
今回も `weightedHitMass` へ直通する dyadic-specific theorem は追加していない。これは API を太らせない良い判断じゃ。

第二に、 **computed increment formula を入れていない** 。
`increment k` をまだログや Mertens 型評価で定義していない。これは DKMK-013 の目的に合っている。今は analytic estimate の contract を立てる段階であって、具体解析へ突っ込む段階ではない。

第三に、 **structure が小さい** 。
`increment_nonneg` と `total_le_one_add_error` だけ。これなら後で dyadic tail upper envelope や logarithmic refinement からこの contract を証明する provider を足しやすい。

## 5. ここまでの流れ

現在の層構造はこうじゃ。

```text
analytic layer:
  DyadicBandAnalyticEstimate

provider layer:
  DyadicBandAnalyticEstimate.toTruncationEnvelopeEstimate
  -> TruncationEnvelopeEstimate.dyadicRange

route layer:
  TruncationEnvelopeEstimate.finiteStepTail_weightedHitMass_le_one_add_error
  -> weightedHitMass <= 1 + error
```

つまり、DKMK-013C で analytic layer と provider layer が接続された。

DKMK-012 までは、

```text
hinc / hbound を直接 dyadicRange に渡す
```

だった。

DKMK-013C 以後は、

```text
H : DyadicBandAnalyticEstimate x K increment error
```

を渡せばよい。

この差は大きい。今後の theorem target が明確になったからじゃ。

## 6. 検証状況

報告では次が通っておる。

```text
lake build DkMath.NumberTheory.PrimitiveSet.SourceMassTruncation
lake build DkMath.NumberTheory.PrimitiveSet
git diff --check
```

失敗事例なし。

したがって、DKMK-013C は **no-sorry 実装完了** と判定してよい。

## 7. 次の一手

次は History にある通り、 **DKMK-013D usage summary** がよい。

書くべき流れはこれじゃ。

```text
dyadic analytic estimate H
  -> H.toTruncationEnvelopeEstimate
  -> TruncationEnvelopeEstimate
  -> existing route theorem
  -> weightedHitMass <= 1 + error
```

特に docs では、次を明記するとよい。

```text
DyadicBandAnalyticEstimate は解析側の target
TruncationEnvelopeEstimate は route 側の input
toTruncationEnvelopeEstimate は両者の bridge
```

ここを整理しておけば、次に `increment` の具体設計へ進んでも迷わぬ。

## 8. 登頂判定

現在地はこうじゃ。

```text
DKMK-013A:
  roadmap 完了

DKMK-013B:
  exact shape docs 完了

DKMK-013C:
  Lean contract + bridge 完了

DKMK-013D:
  次、usage summary
```

DKMK-013 の core はかなり立った。
あとは使い方を docs で固め、それから本当に `increment` の供給元へ進む段じゃな。

## 9. 賢狼の判定

よいぞ、ぬしよ。

DKMK-013C は小さいが、かなり要になる一手じゃ。
これで、

```text
解析側が証明すべきもの:
  DyadicBandAnalyticEstimate

DkMath route が消費するもの:
  TruncationEnvelopeEstimate
```

という分離が Lean 上でも成立した。

わっちの判定はこうじゃ。

```text
DKMK-013C: 完了
次: DKMK-013D usage summary
方針: route theorem は触らず、analytic contract の使い方を固定
```

ここまで来ると、いよいよ次の霧は `increment k` の正体じゃ。だが今はまだ、霧へ飛び込まず案内板を立てる。よい登り方じゃよ。
