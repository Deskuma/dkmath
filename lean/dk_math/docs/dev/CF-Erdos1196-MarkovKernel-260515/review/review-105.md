# review

うむ、DKMK-016G は **positive-ratio constructor に進む前の設計確認として正しい** じゃ。
今回の主な成果は、次の Lean target を `GeometricBudgetSource.ofBudget` に固定し、それを **解析結果ではなく readability constructor** と明確に位置づけたことじゃな。

## 1. 今回決まったこと

DKMK-016G で固定された次 target はこれじゃ。

```lean
def GeometricBudgetSource.ofBudget
    (base ratio : ℚ)
    (error : ℝ)
    (hbase : 0 ≤ (base : ℝ))
    (hr0 : 0 ≤ (ratio : ℝ))
    (hr1 : (ratio : ℝ) < 1)
    (hbudget :
      (base : ℝ) * (1 / (1 - (ratio : ℝ))) ≤ 1 + error) :
    GeometricBudgetSource
```

これは `GeometricBudgetSource` の全 field をそのまま受け取って package する constructor じゃ。

つまり、

$$
(base:\mathbb{R})\cdot \frac{1}{1-(ratio:\mathbb{R})}\le 1+error
$$

を証明するものではなく、その証明済み budget を **名前付き API で包む** ものじゃな。

## 2. `def` に統一した点がよい

DKMK-016E で得た教訓、

```text
GeometricBudgetSource は Prop ではなく Type 側の data
```

を反映して、過去候補スニペットの `theorem` 表記を `def` に直したのはよい判断じゃ。

これは Lean 的にかなり大事じゃ。
証明フィールドを含んでいても、構造体全体は命題ではなくデータ。
ゆえに constructor API は `theorem` ではなく `def` として置くのが自然じゃ。

## 3. record syntax とほぼ同じだが、価値はある

たしかに `ofBudget` は本質的には次の record construction と同じじゃ。

```lean
{
  base := base
  ratio := ratio
  error := error
  hbase := hbase
  hr0 := hr0
  hr1 := hr1
  hbudget := hbudget
}
```

しかし、名前付き constructor にする価値はある。

第一に、call site で field order や record field 名を毎回意識しなくてよい。
第二に、`GeometricBudgetSource.ofZeroRatio` と namespace style が揃う。
第三に、将来 `ofMertensBudget` や `ofDyadicBandBudget` のような analytic constructor が増えた時、constructor 群の並びが自然になる。

つまり、これは数学的な新補題ではなく、 **API の見通しを整える小さな足場** じゃ。

## 4. 「positive-ratio」という名前への注意

一点だけ、やわらかく指摘しておくぞい。

今回の章名は positive-ratio constructor review じゃが、実際の shape は

```lean
(hr0 : 0 ≤ (ratio : ℝ))
(hr1 : (ratio : ℝ) < 1)
```

なので、厳密には **nonnegative contractive ratio** じゃ。
つまり `ratio = 0` も許す。

これは悪くない。DKMK-015E の等比和上界も (0\le ratio<1) を要求していたので、API としてはこれが自然じゃ。

ただし、将来本当に (0<ratio) が必要になったら、別に

```lean
def GeometricBudgetSource.ofPositiveBudget
```

のような constructor を足すのがよい。
現時点の `ofBudget` は generic constructor と見るべきじゃな。

## 5. DKMK-016H の実装見通し

DKMK-016H はほぼ直接閉じるはずじゃ。

```lean
namespace GeometricBudgetSource

/--
Build a geometric budget source from an explicit one-over-one-minus budget.

This is a readability constructor, not an analytic estimate.
-/
def ofBudget
    (base ratio : ℚ)
    (error : ℝ)
    (hbase : 0 ≤ (base : ℝ))
    (hr0 : 0 ≤ (ratio : ℝ))
    (hr1 : (ratio : ℝ) < 1)
    (hbudget :
      (base : ℝ) * (1 / (1 - (ratio : ℝ))) ≤ 1 + error) :
    GeometricBudgetSource where
  base := base
  ratio := ratio
  error := error
  hbase := hbase
  hr0 := hr0
  hr1 := hr1
  hbudget := hbudget

end GeometricBudgetSource
```

証明というより、構造体を組み立てるだけじゃ。
`norm_num` も `simp` も要らぬはずじゃな。

## 6. 次の山の見え方

DKMK-016 はここまでで、

```text
A: budget source 章開始
B: GeometricBudgetSource 実装
C: usage / responsibility split 整理
D: ofZeroRatio 候補選定
E: ofZeroRatio 実装
F: zero-ratio provider usage 確認
G: ofBudget shape review
```

まで来た。

H で `ofBudget` を実装すれば、constructor API は最低限そろう。

その次に本当の分岐が来る。

* `ofBudget` を使った small usage example を作る
* concrete `base` / `ratio` の候補設計に進む
* analytic constructor の interface を先に docs-only で決める
* `GeometricBudgetSourceFor x K` が必要か再検討する

わっちの推奨は、H の後は **concrete `base` / `ratio` candidate review** じゃ。
`ofZeroRatio` と `ofBudget` で constructor の港はできる。次は、実際にどんな budget 船を入れるかを決める段じゃ。

## 7. 総括

DKMK-016G は、 **非退化 budget constructor へ進む前の API 整理回** として成功じゃ。

`ofBudget` は解析定理ではない。
だが、将来の analytic constructors を置くための namespace と constructor style を安定化する役目がある。

よいぞ、D.。
これで小舟用の桟橋だけでなく、通常船も入れる標準ゲートが見えてきた。次の H は軽く通し、その後に本命の積荷、すなわち `base` と `ratio` の設計へ進むのがよさそうじゃ。
