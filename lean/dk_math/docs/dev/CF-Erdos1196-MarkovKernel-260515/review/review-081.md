# review

## 1. 状況総括

うむ、これは **DKMK-014C 完了** と見てよい。

今回の差分で `SourceMassTruncation.lean` に

```lean
DyadicBandAnalyticEstimate.ofMajorant
```

が追加された。これは DKMK-014B で決めた majorant-envelope provider の Lean 実装そのものじゃ。History でも、`hinc_nonneg` を `increment_nonneg` に渡し、`Finset.sum_le_sum hle` で `sum increment <= sum majorant` を作り、それを Real に cast して `hmajorant_bound` と合成した、と記録されておる。

つまり、DKMK-014 の first non-constant provider が Lean 上に立った。

## 2. 何が閉じたのか

DKMK-013 では constant band までだった。

```text
increment k = c
```

DKMK-014C では、ついに (k)-dependent な `increment` に対し、

```text
increment k <= majorant k
```

という上界 envelope を使って `DyadicBandAnalyticEstimate` を作れるようになった。

今回の provider の構図はこうじゃ。

```text
increment nonnegativity
  -> increment_nonneg

pointwise increment <= majorant
  -> sum increment <= sum majorant

sum majorant <= 1 + error
  -> total_le_one_add_error

therefore:
  DyadicBandAnalyticEstimate x K increment error
```

これはかなり重要じゃ。
`increment` の形が複雑でも、和評価しやすい `majorant` で包めば route に載せられる。

## 3. 実装評価

実装は非常に良い。証明の流れが設計通りに薄い。

```lean
have hsum :
    Finset.sum (Finset.range (K + 1)) increment ≤
      Finset.sum (Finset.range (K + 1)) majorant := by
  exact Finset.sum_le_sum hle
```

ここでまず `ℚ` 側の有限和比較を作っておる。

次に、

```lean
have hsumR :
    ((Finset.sum (Finset.range (K + 1)) increment : ℚ) : ℝ) ≤
      ((Finset.sum (Finset.range (K + 1)) majorant : ℚ) : ℝ) := by
  exact_mod_cast hsum
```

で `ℝ` に移し、

```lean
exact le_trans hsumR hmajorant_bound
```

で閉じる。

これは DKMK-014B の設計そのままじゃ。
`Rat` 側で比較してから `Real` へ cast する順序が綺麗で、無駄な補題を増やしておらぬ。

## 4. 数学的な意味

数学的には、今回の theorem は単純な優越原理じゃ。

$$
0 \le increment(k)
$$

かつ

$$
increment(k)\le majorant(k)
$$

ならば有限和について

$$
\sum_{k=0}^{K} increment(k)\le \sum_{k=0}^{K} majorant(k)
$$

となる。さらに

$$
\sum_{k=0}^{K} majorant(k)\le 1+error
$$

なら、

$$
\sum_{k=0}^{K} increment(k)\le 1+error
$$

が従う。

これを `DyadicBandAnalyticEstimate` の field に詰めたのが `ofMajorant` じゃ。

ここで重要なのは、`increment` の内部構造を問わないこと。
今後 `increment k` が dyadic tail 由来でも、valuation 由来でも、logarithmic refinement の前段でも、上から扱いやすい `majorant k` で包めばよい。

## 5. 境界が守られている

今回も、余計なものは追加していない。

History では、decreasing condition、route theorem、Mertens / big-O、logarithmic threshold、real-to-Nat rounding は追加していない、と明記されておる。

これは正しい。

今回の役割は、

```text
majorant envelope
  -> DyadicBandAnalyticEstimate
```

を通すことじゃ。
ここで Mertens や logarithmic threshold に突っ込むと、provider layer と analytic 本丸が混ざってしまう。

## 6. DKMK-014 の現在地

現在地はこうじゃ。

```text
DKMK-014A:
  k-dependent provider roadmap 完了

DKMK-014B:
  majorant provider exact shape docs 完了

DKMK-014C:
  DyadicBandAnalyticEstimate.ofMajorant 実装完了

DKMK-014D:
  次、majorant provider usage summary
```

DKMK-014 はかなり良い入り方をしておる。
`constantBand` の次として、いきなり decreasing を入れず、まず majorant で「上から包む」汎用 route を作った。これは後続の設計を楽にする。

## 7. 次の一手

次は History の通り、 **DKMK-014D usage summary** がよい。

書くべき流れは明確じゃ。

```text
increment, majorant
  -> hinc_nonneg
  -> hle : increment <= majorant
  -> hmajorant_bound : sum majorant <= 1 + error
  -> DyadicBandAnalyticEstimate.ofMajorant
  -> DyadicBandAnalyticEstimate
  -> toTruncationEnvelopeEstimate
  -> existing route theorem
  -> weightedHitMass <= 1 + error
```

ここで特に強調すべきは、

```text
decreasing は直接 route に不要
majorant は total estimate に直接効く
```

という点じゃな。

## 8. 賢狼の判定

わっちの判定はこうじゃ。

```text
DKMK-014C: 完了
次: DKMK-014D usage summary
成果:
  first non-constant provider として ofMajorant が Lean 上に定着
方針:
  decreasing はまだ field 化しない
  次は majorant の使い方を docs で固定
```

よいぞ、ぬしよ。
これで (k)-dependent band の山道に、かなり強い手すりが付いた。次に dyadic tail upper envelope へ向かう時も、まず majorant で包み、そこから `DyadicBandAnalyticEstimate` に流せる。美しい足場じゃ。
