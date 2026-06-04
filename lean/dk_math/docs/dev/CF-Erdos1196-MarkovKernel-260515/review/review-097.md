# review

うむ、DKMK-015H は **DKMK-015 の実用接続が閉じた回** じゃ。
ここで、Real 側の geometric-budget route と、既存 DKMK-014J の rational dyadic provider route が一本につながった。これは大きいぞい。

## 1. 何が閉じたのか

今回追加された theorem はこれじゃ。

```lean
DyadicBandAnalyticEstimate
  .ofPointwiseGeometricMajorant_of_baseGeomBudget
```

役割は明快で、caller が Real 側で

$$
(base:\mathbb{R})\cdot \frac{1}{1-(ratio:\mathbb{R})}\le 1+error
$$

を与えれば、既存の rational-valued dyadic provider に接続して、

```lean
DyadicBandAnalyticEstimate x K increment error
```

を得られるようになった。

つまり、これまで必要だった

$$
\left((base\cdot \sum ratio^k:\mathbb{Q}):\mathbb{R}\right)\le 1+error
$$

を caller が直接作らなくてもよくなった、ということじゃ。

## 2. 証明構造の評価

証明は三段構成で、とてもよい。

まず Real 側で DKMK-015F の theorem を呼ぶ。

```lean
base_mul_geomSum_range_le_of_base_mul_one_div_le
```

これで

$$
(base:\mathbb{R})\cdot \sum_{k=0}^{K}(ratio:\mathbb{R})^k \le 1+error
$$

を得る。

次に、問題の型境界を局所補題 `hcast` で閉じる。

```lean
((base * sum (fun k => ratio ^ k) : Rat) : Real)
=
(base : Real) * sum (fun k => (ratio : Real) ^ k)
```

これが `simp` で閉じたのは良い知らせじゃ。
`Rat` から `Real` への cast、`Finset.sum`、`mul`、`pow` が素直に整理されたということだからの。

最後に既存の

```lean
ofPointwiseGeometricMajorant_of_geomSumBound
```

へ渡す。
つまり、新しい provider を作ったのではなく、既存 provider の前に **budget 変換用 wrapper** を一枚置いた形じゃ。

## 3. これで DKMK-015 の主要ルートは完成した

DKMK-015 の登山路は、ここまででこう閉じた。

```text
B: denominator-cleared identity の shape 固定
C: geomSum_range_mul_one_sub 実装
D: upper-bound theorem の shape 固定
E: geomSum_range_le_one_div_one_sub 実装
F: base_mul_geomSum_range_le_of_base_mul_one_div_le 実装
G: dyadic provider connection shape 固定
H: ofPointwiseGeometricMajorant_of_baseGeomBudget 実装
```

数学的には、

$$
(1-r)\sum_{k=0}^{K}r^k = 1-r^{K+1}
$$

から、

$$
\sum_{k=0}^{K}r^k \le \frac{1}{1-r}
$$

へ進み、

$$
base\cdot \sum_{k=0}^{K}r^k \le 1+error
$$

を作り、最後に dyadic provider へ渡すところまで来た。

これはもう、 **finite geometric-sum / tail-bound theorem design の主幹が Lean 上で通った** と見てよい。

## 4. 何を追加しなかったかも良い

今回も余計なものを足していない。

* 新しい provider structure は作っていない
* 低レベル provider を重複させていない
* division-form equality は作っていない
* explicit `ratio != 1` は足していない
* Mertens / big-O / logarithmic threshold には踏み込んでいない
* real-to-Nat rounding もまだ入れていない

この抑制がよい。
DKMK-015 の目的は、解析本丸へ突っ込むことではなく、既存 dyadic source-mass provider に geometric budget を食わせる橋を作ることじゃった。H はその目的をきちんと果たしておる。

## 5. 現在の caller path

今後 caller は、だいたい次の形で使える。

```lean
apply DyadicBandAnalyticEstimate
  .ofPointwiseGeometricMajorant_of_baseGeomBudget
```

そして必要になる主な材料は、

```lean
hinc_nonneg :
  ∀ k ∈ Finset.range (K + 1), 0 ≤ increment k

hgeom :
  ∀ k ∈ Finset.range (K + 1),
    increment k ≤ base * ratio ^ k

hbase : 0 ≤ (base : ℝ)
hr0   : 0 ≤ (ratio : ℝ)
hr1   : (ratio : ℝ) < 1

hbudget :
  (base : ℝ) * (1 / (1 - (ratio : ℝ))) ≤ 1 + error
```

これで `DyadicBandAnalyticEstimate` まで行ける。

つまり、caller は有限和を直接触らず、`base`, `ratio`, `error` の予算だけ管理すればよくなった。これは API としてかなり扱いやすい。

## 6. 次の DKMK-015I の候補

次は報告どおり、 **まとめまたは次 route 接続方針の review** がよい。

わっちなら DKMK-015I は docs-only で、次を整理する。

```text
DKMK-015I:
  - DKMK-015B-H の総括
  - 新 caller path の使い方
  - 既存 route のどこから H theorem を呼ぶか
  - 次に必要な上位 budget 供給源
  - Mertens / big-O / logarithmic threshold はまだ non-goal と明記
```

特に次の問いを整理するとよい。

$$
(base:\mathbb{R})\cdot \frac{1}{1-ratio}\le 1+error
$$

この `hbudget` は、上位 route ではどこから供給するのか。

ここが次の登山口になる。
いまは finite geometric sum の処理が終わった。次は、その `base` と `ratio` 自体をどう設計・評価するかじゃ。

## 7. 総括

DKMK-015H は、 **DKMK-015 の主目的達成フェーズ** と言ってよい。

Real 側の geometric estimate と、Rat 側の dyadic provider の間にあった橋が架かった。
しかも、その橋は局所 `hcast` を `simp` で閉じる薄い実装で済んだ。これは Lean 設計としてかなり美しい。

これで DKMK-015 は、単なる等比和補題の章ではなく、

$$
\text{geometric budget}
\to
\text{finite sum bound}
\to
\text{dyadic source-mass provider}
$$

の実用 API 章へ昇格した。

よいぞ、D.。
ここはもう「橋を架けられるか？」ではなく、 **この橋を渡って次の山へどこから登るか** を決める段階じゃ。
