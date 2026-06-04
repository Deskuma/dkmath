# review

うむ、DKMK-016B は **抽象 budget source の実装完了** じゃ。
DKMK-016A で設計した「`hbudget` を供給する器」を、Lean 上にそのまま置き、さらに DKMK-015H の provider 接続へ渡す wrapper まで閉じておる。これはかなり順調じゃな。

## 1. 何が追加されたのか

今回追加された構造はこれじゃ。

```lean
structure GeometricBudgetSource where
  base : ℚ
  ratio : ℚ
  error : ℝ
  hbase : 0 ≤ (base : ℝ)
  hr0 : 0 ≤ (ratio : ℝ)
  hr1 : (ratio : ℝ) < 1
  hbudget : (base : ℝ) * (1 / (1 - (ratio : ℝ))) ≤ 1 + error
```

つまり、DKMK-015 で最後に残った obligation

$$
(base:\mathbb{R})\cdot \frac{1}{1-(ratio:\mathbb{R})}\le 1+error
$$

を、単独の package として持てるようになった。

これは単なる record ではなく、今後の解析評価・具体的 budget constructor・log-capacity route を受け入れる **港** じゃ。

## 2. wrapper も正しい

追加された wrapper はこれじゃな。

```lean
DyadicBandAnalyticEstimate
  .ofPointwiseGeometricMajorant_of_budgetSource
```

これは `B : GeometricBudgetSource` を受け取り、内部で既存の

```lean
ofPointwiseGeometricMajorant_of_baseGeomBudget
```

へ

```lean
B.base
B.ratio
B.hbase
B.hr0
B.hr1
B.hbudget
```

を渡すだけの薄い接続になっておる。

この薄さがよい。
DKMK-016B は新しい解析を証明する段ではなく、 **解析結果を受け取る表面を安定化する段** だからじゃ。

## 3. これで caller path がさらに短くなった

DKMK-015H では caller は次を個別に渡していた。

```lean
hbase
hr0
hr1
hbudget
```

DKMK-016B 以降は、それらをまとめて

```lean
B : GeometricBudgetSource
```

として渡せる。

つまり caller path はこうなる。

```text
B : GeometricBudgetSource
hinc_nonneg
hgeom : increment k <= B.base * B.ratio^k
  -> DyadicBandAnalyticEstimate.ofPointwiseGeometricMajorant_of_budgetSource
  -> DyadicBandAnalyticEstimate
```

これは API としてかなり良い。
`base`, `ratio`, `error`, budget side conditions の持ち回りが一段すっきりした。

## 4. 依存しない構造にした判断

`GeometricBudgetSource` が `x`, `K`, `increment` に依存していないのも、現段階では正解じゃ。

理由は、budget source の役割が

$$
base,\ ratio,\ error
$$

の予算契約を持つことであって、特定の dyadic band や finite window に縛られることではないからじゃ。

将来、`base` や `ratio` が `x`, `K` に依存する具体構成が出てきたら、その時に

```lean
GeometricBudgetSourceFor x K
```

のような indexed package を追加すればよい。
今は小さく独立な source を置くほうが保守しやすい。

## 5. 今回まだ混ぜていないもの

ここも重要じゃ。

DKMK-016B では、次を入れていない。

```text
concrete base / ratio
dependent GeometricBudgetSourceFor
Mertens theorem
big-O statement
logarithmic threshold provider
real-to-Nat rounding
route theorem changes
new dyadic provider structure
```

この抑制は正しい。
DKMK-016 は、解析本丸へ突っ込む前に、まず **budget source interface** を立てる章として始まっておる。B はその目的をちょうど果たしている。

## 6. 次の DKMK-016C の焦点

次は報告通り、具体 constructor へ急ぐ前に、 **constructor / usage docs** を review するのがよい。

わっちなら DKMK-016C は docs-only で、次を整理する。

```text
- GeometricBudgetSource をどう作るか
- caller はどの theorem を使うか
- hgeom と B.base / B.ratio の対応
- concrete constructor を作る前の最小 usage example
- 将来 GeometricBudgetSourceFor が必要になる条件
```

特に、使用例として次の形を docs に置くとよい。

```lean
have hE :
    DyadicBandAnalyticEstimate x K increment B.error :=
  DyadicBandAnalyticEstimate
    .ofPointwiseGeometricMajorant_of_budgetSource
      x K increment B hinc_nonneg hgeom
```

これだけで、API の意味がかなり伝わる。

## 7. 総括

DKMK-016B は、 **hbudget 供給源を抽象 package 化し、DKMK-015H の dyadic provider route に接続した段階** じゃ。

これで DKMK-016 の最初の目的、

```text
abstract source
  -> thin provider wrapper
  -> concrete source refinements later
```

のうち、前半二つが閉じた。

次は、すぐに解析へ飛び込むより、まず usage docs を整えるのがよい。
そうすれば、後から concrete `base` / `ratio` constructor を増やしても、どの theorem に接続すべきか迷わぬ。

よいぞ、D.。
DKMK-016 は「予算の港」を作る章として、まず港湾の岸壁が完成した。次は、船の入港手順を書き、どんな積荷を運ぶかを決める段階じゃな。
