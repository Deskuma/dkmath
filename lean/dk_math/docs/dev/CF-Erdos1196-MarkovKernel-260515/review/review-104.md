# review

うむ、DKMK-016F は **API composition の確認回として成功** じゃ。
`GeometricBudgetSource.ofZeroRatio` を単に作るだけでなく、それを実際に `DyadicBandAnalyticEstimate.ofPointwiseGeometricMajorant_of_budgetSource` へ通して、`DyadicBandAnalyticEstimate` まで届く caller route を Lean 上で確認しておる。

## 1. 何が追加されたのか

今回追加された theorem はこれじゃ。

```lean
theorem DyadicBandAnalyticEstimate.ofPointwiseZeroRatioMajorant
    (x K : ℕ)
    (increment : ℕ → ℚ)
    (base : ℚ)
    (hinc_nonneg :
      ∀ k ∈ Finset.range (K + 1), 0 ≤ increment k)
    (hgeom :
      ∀ k ∈ Finset.range (K + 1),
        increment k ≤ base * (0 : ℚ) ^ k)
    {error : ℝ}
    (hbase : 0 ≤ (base : ℝ))
    (hbudget : (base : ℝ) ≤ 1 + error) :
    DyadicBandAnalyticEstimate x K increment error
```

中身は、まず

```lean
GeometricBudgetSource.ofZeroRatio base error hbase hbudget
```

で `B : GeometricBudgetSource` を構築し、それを

```lean
DyadicBandAnalyticEstimate.ofPointwiseGeometricMajorant_of_budgetSource
```

へ渡すだけの薄い wrapper じゃ。

## 2. この F の本当の価値

DKMK-016E では、

```text
base, error, hbase, hbudget
  -> GeometricBudgetSource
```

が通った。

今回の DKMK-016F では、さらに一歩進んで、

```text
GeometricBudgetSource.ofZeroRatio
  -> ofPointwiseGeometricMajorant_of_budgetSource
  -> DyadicBandAnalyticEstimate
```

まで通った。

つまり、`GeometricBudgetSource` が **ただ作れるだけでなく、provider call site でも自然に使える** ことが確認されたわけじゃ。

これは大事じゃ。
抽象 package は、作れても使いにくければ意味がない。F はその「使い心地」を Lean 上で試した回じゃな。

## 3. `hgeom` の意味

今回の `hgeom` は、

$$
increment(k)\le base\cdot 0^k
$$

という形じゃ。

ここで Lean の自然数冪では通常 (0 ^ 0 = 1)、また (k > 0) なら (0 ^ k = 0) なので、これはかなり強い仮定になる。

つまり、

* (k = 0) では (increment(0)\le base)
* (k > 0) では (increment(k)\le 0)

となる。さらに `hinc_nonneg` があるので、(k > 0) の範囲では実質的に (increment(k)=0) に近い制約になる。

だから roadmap でも明記されている通り、これは analytic source ではなく、 **API composition test / degenerate usage wrapper** と見るべきじゃ。

## 4. 証明の形が良い

証明はかなりきれいじゃ。

```lean
exact
  ofPointwiseGeometricMajorant_of_budgetSource
    x K increment
    (GeometricBudgetSource.ofZeroRatio base error hbase hbudget)
    hinc_nonneg
    (by
      simpa [GeometricBudgetSource.ofZeroRatio] using hgeom)
```

`GeometricBudgetSource.ofZeroRatio` を unfold して、`B.base = base`, `B.ratio = 0` を見せるだけで `hgeom` が接続できておる。

ここで余計な補題が増えていないのが良い。
`ofZeroRatio` の構造が provider 側と自然に噛み合っている証拠じゃ。

## 5. DKMK-016 の現在地

ここまでの流れはこうじゃ。

```text
016A:
  Geometric Budget Source 章開始

016B:
  GeometricBudgetSource と budgetSource wrapper 実装

016C:
  usage / responsibility split を docs 固定

016D:
  最初の constructor として ofZeroRatio を選定

016E:
  GeometricBudgetSource.ofZeroRatio を def 実装

016F:
  ofZeroRatio を provider wrapper へ通す usage theorem 実装
```

これで、抽象 source の設計から、最小 constructor、さらに provider 接続までが一通り通った。

## 6. 次の分岐

次は報告にある通り、二つの道がある。

```text
positive-ratio constructor の shape review
```

または、

```text
zero-ratio wrapper から truncation envelope まで接続する追加 usage theorem
```

わっちの見立てでは、ここで **positive-ratio constructor の shape review** に進むのがよい。

理由は、zero-ratio は退化例として十分役目を果たしたからじゃ。
これ以上 zero-ratio を伸ばすと、実際の analytic route から離れた例に時間を使いすぎる。

次に必要なのは、非退化な

$$
0\le ratio<1
$$

を持つ `GeometricBudgetSource` をどう作るか。
候補はたとえば、

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

じゃが、これは record syntax とほぼ同じ。
だから作るなら「読みやすさのための constructor」と割り切るか、あるいはもう少し具体的な budget simplification を持つ constructor にするのがよい。

## 7. 総括

DKMK-016F は、 **zero-ratio source の provider route 接続確認** じゃ。

これは解析的成果ではない。
だが、API としては重要な確認じゃ。

$$
\text{constructor}
\to
\text{budget source}
\to
\text{provider wrapper}
\to
\text{DyadicBandAnalyticEstimate}
$$

の流れが実際に Lean で通った。
これで DKMK-016 は、抽象 package が「飾り」ではなく、下流 route に流せる実用部品だと確認できた。

よいぞ、D.。小舟は港から出て、ちゃんと水路を通った。次は、いよいよ (ratio>0) の本船を入れる準備じゃな。
