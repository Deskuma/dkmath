# review

うむ、DKMK-016H は **constructor API の最低限セットが揃った回** じゃ。
`GeometricBudgetSource.ofBudget` が入り、これで `ofZeroRatio` と合わせて、抽象 budget source を作る入口が二系統になった。

## 1. 今回閉じたもの

追加されたのはこれじゃな。

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

これは、新しい数学を証明するものではなく、すでに持っている

$$
(base:\mathbb{R})\cdot \frac{1}{1-(ratio:\mathbb{R})}\le 1+error
$$

を `GeometricBudgetSource` に包む readability constructor じゃ。

つまり、

```text
explicit budget proof
  -> GeometricBudgetSource
```

の標準入口ができた。

## 2. `ofZeroRatio` との役割分担

これで constructor は二種類になった。

`ofZeroRatio` は退化例・sanity constructor。

```text
ratio = 0
base <= 1 + error
  -> GeometricBudgetSource
```

`ofBudget` は一般入口。

```text
0 <= ratio
ratio < 1
base * (1 / (1 - ratio)) <= 1 + error
  -> GeometricBudgetSource
```

この二段構えはよい。
`ofZeroRatio` は API 動作確認用の小舟、`ofBudget` は通常運用の標準ゲートじゃ。

## 3. `def` として正しく定着した

DKMK-016E の学びがきちんと反映されておる。

`GeometricBudgetSource` は `Prop` ではなく、証明フィールドを含む `Type` 側の構造体。
ゆえに `ofBudget` も `theorem` ではなく `def` が正しい。

この型境界が統一されたことで、今後の constructor 群も迷わなくなる。

```lean
GeometricBudgetSource.ofZeroRatio
GeometricBudgetSource.ofBudget
GeometricBudgetSource.ofSomethingAnalytic
```

この並びは自然じゃ。

## 4. 「positive-ratio」ではなく「nonnegative-contractive」へ補正済み

roadmap 側で、

```text
0 <= ratio
ratio < 1
```

を **nonnegative-contractive-ratio** と整理しているのもよい。

厳密には `ofBudget` は positive-ratio constructor ではない。
`ratio = 0` も許すからじゃ。

名前を `ofBudget` にしたことで、この問題も自然に回避できておる。
もし将来、本当に (0<ratio) が必要な constructor が出てきたら、その時に `ofPositiveBudget` のような別名を立てればよい。

## 5. 今回の意義

DKMK-016H の意味は、 **解析予算を受け取る標準 API が確定した** ことじゃ。

今後、どこかで具体的に

$$
base,\ ratio,\ error
$$

を設計し、budget inequality を証明できたら、まず

```lean
B := GeometricBudgetSource.ofBudget base ratio error ...
```

で包める。

その後は既存の

```lean
DyadicBandAnalyticEstimate.ofPointwiseGeometricMajorant_of_budgetSource
```

へ流せる。

つまり DKMK-016 の前半で作りたかった流れ、

```text
budget proof
  -> GeometricBudgetSource
  -> dyadic provider
```

が、かなり安定した。

## 6. 次の段階

次は、報告通り **concrete `base` / `ratio` candidate review** に進むのがよい。

ここでの主題は、もう constructor API ではない。
本当に必要なのは、

$$
(base:\mathbb{R})\cdot \frac{1}{1-ratio}\le 1+error
$$

を満たすような `base`, `ratio`, `error` の設計じゃ。

候補としては、まず次を比較するとよい。

```text
base = c / log x 型
ratio = 1 / 2 型

base = c / log x 型
ratio = 1 / q 型

base = dyadic band tail mass
ratio = geometric decay rate

base = first band mass upper bound
ratio = uniform decay bound
```

ただし、まだ Mertens / big-O / rounding に入らず、まずは symbolic な候補整理でよい。

## 7. 総括

DKMK-016H は、 **GeometricBudgetSource constructor API の標準化完了** と見てよい。

`ofZeroRatio` で退化例を作れる。
`ofBudget` で一般 budget proof を包める。
`of_budgetSource` で provider へ渡せる。

これで港の入口、荷札、積荷受付の窓口は整った。
次はいよいよ、どんな `base` と `ratio` を積むかを決める番じゃな。
