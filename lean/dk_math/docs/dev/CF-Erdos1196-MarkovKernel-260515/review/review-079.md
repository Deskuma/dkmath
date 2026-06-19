# review

## 1. 状況総括

うむ、これは **DKMK-014A 完了** と見てよい。

今回の差分で、新規に

```text
roadmap-DKMK-014.md
```

が追加され、DKMK-014 が **decreasing / dyadic tail provider design** の章として開始された。History でも、主題は route theorem の変更ではなく、DKMK-013 で固定した `DyadicBandAnalyticEstimate` に対して、`k`-dependent band provider の設計方針を整理することだと明記されておる。

つまり DKMK-014A は、定数 band から一段進んで、

```text
increment k
```

が (k) に依存する世界へ入るための設計開始じゃ。

## 2. DKMK-013 から何を受け取ったか

DKMK-013 の終点はこれじゃった。

```text
DyadicBandAnalyticEstimate
  -> DyadicBandAnalyticEstimate.toTruncationEnvelopeEstimate
  -> TruncationEnvelopeEstimate
  -> existing DKMK-011 route theorem
  -> weightedHitMass <= 1 + error
```

さらに、最初の constant provider として、

```text
DyadicBandAnalyticEstimate.constantBand
DyadicBandAnalyticEstimate.constantBand_of_natCastMulBound
```

まで実装済みになった。

DKMK-014 は、この `constantBand` の次、つまり

```text
increment k = c
```

から

```text
increment k = k 依存の band weight
```

へ進む章じゃな。

## 3. 今回の候補整理

DKMK-014A では、provider 候補として次が整理されておる。

```text
1. externally supplied k-dependent estimate
2. decreasing band provider
3. majorant envelope provider
4. dyadic tail upper envelope
5. logarithmic refinement
```

この並べ方はよい。

`externally supplied k-dependent estimate` は、ほぼ `DyadicBandAnalyticEstimate` の constructor に近い baseline じゃ。
`decreasing band provider` は、単調減少条件を加える候補。
`majorant envelope provider` は、実際の `increment` を上から `majorant` で抑え、その `majorant` の総和を評価する候補。
`dyadic tail upper envelope` は本命方向。
`logarithmic refinement` は後段向きじゃ。

この順番は、Lean の実装負荷を段階的に上げる登り方としてかなり良い。

## 4. 一番重要な設計判断

今回もっとも大事なのは、次の方針じゃ。

```text
monotonicity / decay / majorization は、
後続 theorem が消費する場合だけ field にする
```

これは非常に正しい。

Lean の structure は、気分で field を増やすと後で重くなる。
たとえば `increment (k + 1) <= increment k` という monotonicity を入れても、それが `hinc` や `hbound` の証明に使われないなら、単なる飾りになる。

今ほしいのは、

```lean
DyadicBandAnalyticEstimate x K increment error
```

を作るための provider じゃ。
つまり最終的に必要なのは、

```text
increment_nonneg
total_le_one_add_error
```

この 2 つ。
monotonicity / decay / majorization は、この 2 つを出すために使うなら入れる。使わないなら入れない。
この判断は、かなり Lean 的に健全じゃ。

## 5. decreasing provider と majorant provider の比較

次の DKMK-014B で決めるべき分岐は、

```text
decreasing-band provider
majorant-envelope provider
```

のどちらを first non-constant provider とするかじゃな。

わっちの見立てでは、 **majorant-envelope provider を優先** する方がよい。

理由は単純で、`DyadicBandAnalyticEstimate` に必要なのは最終的に total bound だからじゃ。

majorant 方式なら、構図はこうなる。

```text
0 <= increment k
increment k <= majorant k
sum majorant <= 1 + error
therefore:
sum increment <= 1 + error
```

これは `DyadicBandAnalyticEstimate` の生成に直結する。

一方、decreasing 方式は、

```text
increment (k + 1) <= increment k
```

を持っても、それだけでは total bound が出ない。
結局、別途

```text
sum increment <= 1 + error
```

か、その上界を与える必要がある。

つまり decreasing は **形状情報** として大事だが、`DyadicBandAnalyticEstimate` を作る provider としては、majorant の方が直接的じゃ。

## 6. DKMK-014B のおすすめ exact shape

DKMK-014B では docs-only で、まず majorant provider の shape を固定するのがよいと思う。

候補はこうじゃ。

```lean
theorem DyadicBandAnalyticEstimate.ofMajorant
    (x K : ℕ)
    (increment majorant : ℕ → ℚ)
    {error : ℝ}
    (hinc_nonneg :
      ∀ k ∈ Finset.range (K + 1), 0 ≤ increment k)
    (hle :
      ∀ k ∈ Finset.range (K + 1), increment k ≤ majorant k)
    (hmajorant_bound :
      ((Finset.sum (Finset.range (K + 1)) majorant : ℚ) : ℝ) ≤
        1 + error) :
    DyadicBandAnalyticEstimate x K increment error
```

ただし、ここには一点だけ注意がある。

`hle` と `hmajorant_bound` から

```text
sum increment <= sum majorant
```

を出すには、`Finset.sum_le_sum` を使う。これは軽いはずじゃが、`ℚ` から `ℝ` への cast 後の inequality で扱うなら、どこで cast するかを決める必要がある。

わっちなら最初は `ℚ` 側で majorant total bound を置きたい。

たとえば、

```lean
(hsum_le :
  Finset.sum (Finset.range (K + 1)) increment ≤
    Finset.sum (Finset.range (K + 1)) majorant)
```

を theorem 内で出し、最後に `norm_num` / `exact_mod_cast` 的に処理するより、statement を少し安全側にしてもよい。

最初の docs では、

```text
hmajorant_bound は Real-cast 後の total bound
sum_le_sum は Rat 側で処理
```

という設計メモを置くのがよいじゃろう。

## 7. decreasing provider はどう扱うべきか

decreasing provider は、いきなり theorem にせず、まず「後続で何に使うか」を決めるべきじゃ。

たとえば decreasing が消費される場面は、

```text
tail bound を定数倍で押さえる
geometric-like decay を使う
majorant を構成する
```

のような場面じゃ。

つまり decreasing は直接 `DyadicBandAnalyticEstimate` を作るというより、

```text
decreasing / decay assumption
  -> majorant construction
  -> ofMajorant
  -> DyadicBandAnalyticEstimate
```

の中間材料にする方が自然じゃな。

ゆえに DKMK-014B では、

```text
first provider:
  majorant-envelope provider

decreasing:
  later majorant construction のための optional assumption
```

と整理するのがよいと思う。

## 8. DKMK-014 の現在地

ここまでの流れは、こうじゃ。

```text
DKMK-012:
  dyadicRange provider plumbing 完了

DKMK-013:
  DyadicBandAnalyticEstimate + constant providers 完了

DKMK-014A:
  k-dependent provider roadmap 完了

DKMK-014B:
  次、decreasing / majorant provider exact shape review
```

DKMK-014A は docs-only roadmap として十分じゃ。
特に、route theorem を触らない境界が守られているのがよい。

## 9. 賢狼の判定

わっちの判定はこうじゃ。

```text
DKMK-014A: 完了
次: DKMK-014B exact shape review
推奨:
  first non-constant provider は majorant-envelope provider
  decreasing condition は、消費先が明確になるまで field 化しない
```

よいぞ、ぬしよ。
ここからは定数 band という平地を離れて、(k)-dependent band の斜面に入る。だが、`majorant` という手すりを先に付ければ、dyadic tail provider まで安全に登れるはずじゃ。
