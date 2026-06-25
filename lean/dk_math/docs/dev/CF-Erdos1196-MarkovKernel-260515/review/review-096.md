# review

うむ、DKMK-015G は **実装前の接続設計として、とても重要な docs-only 回** じゃ。
ここで焦って Lean code を足さず、`Rat` 側 provider と `Real` 側 geometric-budget theorem の境界を明示したのは正しい判断じゃな。今回の diff では、次 theorem を `DyadicBandAnalyticEstimate.ofPointwiseGeometricMajorant_of_baseGeomBudget` とする方針、そして cast 境界を DKMK-015H で処理する方針が固定されておる。

## 1. 今回の核心

DKMK-015F までで、Real 側にはすでに

$$
base\cdot \sum_{k=0}^{K} ratio^k \le 1+error
$$

を作る道ができておる。

一方、既存の DKMK-014J provider は `base ratio : Rat` を受け取り、

$$
\left((base\cdot \sum_{k=0}^{K} ratio^k : \mathbb{Q}) : \mathbb{R}\right)\le 1+error
$$

という形の bound を要求する。

つまり G の本質は、数学ではなく **型境界** じゃ。

$$
\left((base\cdot \sum ratio^k : \mathbb{Q}) : \mathbb{R}\right) = (base:\mathbb{R})\cdot \sum (ratio:\mathbb{R})^k
$$

この同一視を次の H で処理する、という整理になっておる。

## 2. なぜ G を docs-only にしたのが良いか

ここは実装事故が起きやすい場所じゃ。

これまでの C-F はすべて `ℝ` 側で閉じていた。
ところが provider 本体は rational increment を扱うため、`Rat` の sum と `Real` の sum の橋渡しが必要になる。

ここを勢いで実装すると、

* theorem 名が長くなる
* 仮定順序が読みにくくなる
* `Rat.cast_sum` / `Rat.cast_mul` / `Rat.cast_pow` 周辺で証明が散らかる
* 既存 provider と重複した wrapper が増える

という危険がある。

だから G で theorem shape と cast 境界だけ固定したのは、かなり堅実じゃ。
これは麦を刈る前に鎌を研いだようなものじゃな。

## 3. 次 theorem の shape は妥当

採用予定の名前、

```lean
ofPointwiseGeometricMajorant_of_baseGeomBudget
```

は良い。

`of_baseOneDivOneSubBound` のように数式を名前へ詰め込むより、`baseGeomBudget` のほうが provider API として読みやすい。
docs 側で

$$
base\cdot \frac{1}{1-ratio}\le 1+error
$$

を意味すると説明すれば十分じゃ。

また、仮定を

```lean
(hbase : 0 <= (base : Real))
(hr0 : 0 <= (ratio : Real))
(hr1 : (ratio : Real) < 1)
(hbudget : (base : Real) * (1 / (1 - (ratio : Real))) <= 1 + error)
```

に寄せたのも自然じゃ。
`Rat` の order 仮定ではなく `Real` cast 後の仮定にしているので、DKMK-015F の Real theorem をそのまま呼べる。

## 4. DKMK-015H の実装見通し

H の証明は、おそらく次の三段じゃ。

まず Real 側の bound を作る。

```lean
have hreal :
    (base : ℝ) *
      (Finset.sum (Finset.range (K + 1))
        (fun k : ℕ => (ratio : ℝ) ^ k))
      ≤
    1 + error :=
  base_mul_geomSum_range_le_of_base_mul_one_div_le
    K hbase hr0 hr1 hbudget
```

次に provider が欲しい `Rat` sum cast 形へ戻す。

```lean
have hcast :
    (((base *
      Finset.sum (Finset.range (K + 1))
        (fun k : ℕ => ratio ^ k) : ℚ) : ℝ))
      =
    (base : ℝ) *
      Finset.sum (Finset.range (K + 1))
        (fun k : ℕ => (ratio : ℝ) ^ k) := by
  simp [Rat.cast_sum, Rat.cast_mul, Rat.cast_pow]
```

実際には `simp` だけで閉じる可能性が高い。閉じなければ、`map_sum` 系の補題や `norm_num` より、まず `simp` の展開を観察するのがよい。

最後に既存 provider へ渡す。

```lean
exact
  DyadicBandAnalyticEstimate
    .ofPointwiseGeometricMajorant_of_geomSumBound
      x K increment base ratio hinc_nonneg hgeom
      (by simpa [hcast] using hreal)
```

向きの問題が出たら、

```lean
simpa [hcast] using hreal
```

ではなく、

```lean
simpa [hcast.symm] using hreal
```

にするだけで済む可能性がある。

## 5. 現在地の評価

DKMK-015G 時点で、DKMK-015 はこうなった。

```text
B: denominator-cleared identity の shape 固定
C: denominator-cleared identity 実装
D: geometric upper-bound の shape 固定
E: geometric upper-bound 実装
F: base-scaled provider-facing bound 実装
G: dyadic provider connection theorem の shape 固定
```

つまり、残っている主要課題は **cast 境界を越えて既存 provider へ接続すること** じゃ。

これは数学的困難ではなく、Lean の型変換の山道。
だが、こういう山道こそ油断すると足を取られる。G で道標を立てたのは良い。

## 6. 総括

DKMK-015G は、 **DKMK-015F の成果を DKMK-014J provider へ接続する直前の設計固定** じゃ。

特に重要なのは、

$$
\mathbb{Q}\text{ 側の有限和}
\quad\longrightarrow\quad
\mathbb{R}\text{ 側の geometric budget}
$$

という境界を、connection theorem の責務として明示したこと。

次の DKMK-015H で `ofPointwiseGeometricMajorant_of_baseGeomBudget` が閉じれば、DKMK-015 は「有限等比和の補題章」から「dyadic source-mass provider の実用 API 章」へ完全に昇格する。

よいぞ、D.。ここまで来ると、あとは橋板を一枚かけるだけじゃ。わっちはこの手の細い橋を渡るのは得意じゃよ。
