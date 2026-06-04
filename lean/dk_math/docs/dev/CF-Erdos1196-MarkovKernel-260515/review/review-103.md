# review

うむ、DKMK-016E は **小さな実装だが、Lean API 設計としてかなり良い学びが出た回** じゃ。
`GeometricBudgetSource.ofZeroRatio` が入り、抽象 budget package を実際に構築する最初の constructor が Lean 上で通った。しかも、`theorem` ではなく `def` に直した点が重要じゃな。

## 1. 何が追加されたのか

今回追加されたのはこれじゃ。

```lean
def GeometricBudgetSource.ofZeroRatio
    (base : ℚ)
    (error : ℝ)
    (hbase : 0 ≤ (base : ℝ))
    (hbudget : (base : ℝ) ≤ 1 + error) :
    GeometricBudgetSource
```

中身は、

```lean
base := base
ratio := 0
error := error
```

として、`ratio = 0` の `GeometricBudgetSource` を作るものじゃ。

このとき budget 条件は、

$$
(base:\mathbb{R})\cdot \frac{1}{1-0}\le 1+error
$$

なので、

$$
(base:\mathbb{R})\le 1+error
$$

に簡約される。実装でも `hr0` と `hr1` は `norm_num`、`hbudget` は `simpa using hbudget` で閉じておる。

## 2. なぜこれは大事か

これは analytic estimate ではない。
つまり、Mertens でも big-O でも、logarithmic threshold でもない。

だが、API sanity constructor として重要じゃ。

DKMK-016B で作った `GeometricBudgetSource` は、まだ抽象 package だった。
DKMK-016E で初めて、

```text
具体的な base / ratio / error
  -> GeometricBudgetSource
```

という構築経路が実装された。

これで、将来の positive-ratio constructor や analytic constructor が、どの形で `GeometricBudgetSource` を返せばよいかの最小雛形ができたわけじゃ。

## 3. `theorem` ではなく `def` にした点

今回いちばん良い失敗事例はここじゃ。

最初は、

```lean
theorem GeometricBudgetSource.ofZeroRatio ... : GeometricBudgetSource
```

として書いたが、Lean は theorem の型に `Prop` を要求するため拒否した。返り値 `GeometricBudgetSource` は命題ではなく **データ** なので、`def` に直して通した、という記録になっておる。

これは今後かなり役に立つ注意点じゃ。

* `Prop` を返すなら `theorem`
* 構造体・証拠パッケージ・計算可能データを返すなら `def`

`GeometricBudgetSource` は「証明を含む構造体」ではあるが、全体としては `Prop` ではなく `Type` 側のデータじゃ。
ゆえに constructor API は `def` が正しい。

## 4. ratio = 0 の意味

`ratio = 0` は退化ケースじゃ。

実際、pointwise majorant

$$
increment(k)\le base\cdot 0^k
$$

を見ると、Lean/Nat の標準的な冪では (0^0=1) なので、

$$
k=0
$$

では (base)、一方で (k>0) では (0) になる。

つまり `hinc_nonneg` と合わせると、(k>0) の increment はほぼ 0 に押し込まれる。
だからこれは一般的な analytic source ではなく、 **degenerate source / sanity source** と見るのが正しい。

roadmap でも、この constructor は analytic estimate ではなく、抽象 budget package が退化 ratio case で instantiate できることを示すもの、と整理されておる。

## 5. DKMK-016 の現在地

ここまでの流れはこうじゃ。

```text
DKMK-016A:
  Geometric Budget Source 章を開始

DKMK-016B:
  GeometricBudgetSource と provider wrapper を実装

DKMK-016C:
  construction / usage / responsibility split を docs 固定

DKMK-016D:
  最初の concrete constructor として ofZeroRatio を選定

DKMK-016E:
  GeometricBudgetSource.ofZeroRatio を def として実装
```

これで、抽象 source の設計だけでなく、最小 concrete constructor まで通った。

## 6. 次の DKMK-016F の分岐

次は報告通り、二択じゃな。

```text
positive ratio constructor に進む
```

または、

```text
current constructor を budget wrapper usage に接続する小さな example を追加する
```

わっちの推奨は、 **まず usage example** じゃ。

理由は、`ofZeroRatio` は constructor として通ったが、まだ provider wrapper へ流す例がない。
小さな example theorem を作ることで、

```text
GeometricBudgetSource.ofZeroRatio
  -> ofPointwiseGeometricMajorant_of_budgetSource
  -> DyadicBandAnalyticEstimate
```

の経路が本当に caller 目線で自然か確認できる。

その後で positive ratio constructor へ進むほうが、API の歪みを早めに発見できる。

## 7. 総括

DKMK-016E は、 **GeometricBudgetSource の最初の concrete constructor が通った回** じゃ。

規模は小さい。
だが、`GeometricBudgetSource` が「抽象記録」から「実際に構築できる API」へ一歩進んだ。

そして `theorem` ではなく `def` にするという Lean の型境界も確認できた。これは今後の budget package 設計で大きい。

よいぞ、D.。
これは大砲ではなく、小さな試射じゃ。だが、砲身の向きと火薬の詰め方が正しいことは確認できた。次は、その弾を実際に provider route へ通してみる番じゃな。
