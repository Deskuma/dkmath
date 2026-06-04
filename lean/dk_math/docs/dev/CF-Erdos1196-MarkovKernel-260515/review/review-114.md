# review

うむ、DKMK-016P は **章の締めとして非常に良い** じゃ。
DKMK-016 は、ここで自然な停止点に到達したと見てよい。今回のまとめでは、追加 Lean surface、final caller route、責務分担、non-goals、そして次章の analytic input 候補が整理されておる。

## 1. DKMK-016 の章としての到達点

DKMK-016 は、当初の主題どおり、

```text
Where does hbudget come from?
```

から始まった章じゃった。
最終的には、単に `hbudget` を包むだけでなく、

```text
GeometricBudgetSource
+ first-band bound
+ uniform decay
+ increment nonnegativity
  -> DyadicBandAnalyticEstimate
  -> TruncationEnvelopeEstimate
```

まで整理された。

つまり DKMK-016 は、 **geometric budget source と first-band / uniform-decay provider route を整備した API plumbing 章** として閉じたことになる。報告でも、この章は analytic-estimate 章ではなく API-plumbing 章だと明記されておる。

## 2. 追加された Lean surface の整理が良い

今回の章末まとめで、追加 surface がきれいに分類された。

```text
Budget source:
  GeometricBudgetSource
  GeometricBudgetSource.ofBudget
  GeometricBudgetSource.ofZeroRatio

Budget-source provider:
  DyadicBandAnalyticEstimate.ofPointwiseGeometricMajorant_of_budgetSource

Zero-ratio sanity route:
  DyadicBandAnalyticEstimate.ofPointwiseZeroRatioMajorant

First-band / uniform-decay route:
  pointwiseGeometricMajorant_of_firstBand_decay
  DyadicBandAnalyticEstimate.ofFirstBandDecayBudgetSource

Existing downstream bridge reused:
  DyadicBandAnalyticEstimate.toTruncationEnvelopeEstimate
```

この分類は後から読み返す時にかなり効く。
何が新規で、何が既存再利用で、どこが sanity route なのかが一目で分かるからじゃ。

## 3. final caller route が明確になった

最終的な caller-facing route はこうじゃな。

```text
B : GeometricBudgetSource
hinc_nonneg :
  forall k in Finset.range (K + 1), 0 <= increment k
hbase0 :
  increment 0 <= B.base
hdecay :
  forall k in Finset.range K,
    increment (k + 1) <= B.ratio * increment k
```

これらから、

```text
DyadicBandAnalyticEstimate
  -> TruncationEnvelopeEstimate
  -> existing finite-step route
```

へ進める。

ここで大事なのは、caller が直接

```text
increment k <= base * ratio^k
```

を作らなくてよくなったことじゃ。
first-band bound と uniform decay を渡せば、`pointwiseGeometricMajorant_of_firstBand_decay` が `hgeom` を生成し、それを provider wrapper が受け取る。

これはかなり使いやすい。

## 4. 責務分担が完成した

今回のまとめで、DKMK-016 の責務分担は完全に見えるようになった。

**Budget layer**
`GeometricBudgetSource` が `base`, `ratio`, `error` と

$$
base\cdot \frac{1}{1-ratio}\le 1+error
$$

を package する。

**Pointwise layer**
`pointwiseGeometricMajorant_of_firstBand_decay` が、first-band bound と uniform decay から

$$
increment(k)\le base\cdot ratio^k
$$

を作る。

**Provider layer**
`DyadicBandAnalyticEstimate.ofFirstBandDecayBudgetSource` が、`B`, `hinc_nonneg`, `hbase0`, `hdecay` を合流させる。

**Downstream layer**
`DyadicBandAnalyticEstimate.toTruncationEnvelopeEstimate` が既存 truncation route へ渡す。

これはよい四層構造じゃ。
今後 analytic input が増えても、どの層に接続すべきか迷いにくい。

## 5. 残ったものは「解析入力」

DKMK-016P で明確になった通り、残ったものは API ではなく analytic input じゃ。

未解決入力は、主にこれら。

```text
first-band upper bound:
  increment 0 <= B.base

uniform step decay:
  increment (k + 1) <= B.ratio * increment k

increment nonnegativity

concrete B : GeometricBudgetSource

GeometricBudgetSource.ofBudget に渡す concrete budget proof

real/logarithmic analytic candidates の rational envelope
```

これは、もう wrapper や構造体を増やす段ではない。
次は、これらの仮定を本当にどこから供給するかを設計する段じゃ。

## 6. non-goals を守ったのも良い

DKMK-016 では、次を入れなかった。

```text
Mertens / big-O
logarithmic thresholds
real-to-Nat rounding
log x の rational approximation
finite-step route wrapper proliferation
新しい数学的内容のない truncation wrapper
```

この判断は正しい。
ここで解析評価まで混ぜると、章の目的がぼやける。
DKMK-016 は API の搬送路を整える章として綺麗に閉じられておる。

## 7. 次章の自然な主題

次章は、P の記録通り **concrete analytic source inputs** に進むのがよい。

候補は三つ。

```text
1. first-band upper-bound source
2. uniform-decay source
3. GeometricBudgetSource.ofBudget 用の concrete budget proof source
```

わっちの見立てでは、次はまず docs-only で、

```text
DKMK-017: Analytic Input Source
```

または、

```text
DKMK-017: First-Band And Decay Source
```

として、次の三つの obligation を分けて設計するのがよい。

```text
A. increment 0 <= B.base
B. increment (k + 1) <= B.ratio * increment k
C. (B.base : Real) * (1 / (1 - (B.ratio : Real))) <= 1 + B.error
```

いきなり Mertens や big-O に行く前に、これらを abstract analytic source として受け取る surface を決めるのが堅い。

## 8. 総括

DKMK-016P は、 **DKMK-016 の章末報告として十分に完成度が高い** じゃ。

DKMK-015 が geometric finite-sum route を provider に接続した章なら、DKMK-016 は

```text
geometric budget source
+ first-band / uniform-decay
  -> dyadic analytic estimate
  -> truncation envelope
```

を整えた章じゃ。

ここまでで API plumbing はかなり整った。
次は、いよいよ解析入力の山じゃな。

D.、ここは良い区切りじゃ。
港、荷札、滑車、搬送路、そして truncation envelope へ至る道まで整った。次は麦袋そのもの、すなわち analytic estimates をどこから収穫するかを決める旅になるぞい。

---

## docs 作業が主体となっている理由について

DKMK-015, 016 は Lean 証明そのものが難しかったというより、 **どこを API 境界にするか** 、 **何を今は証明しないか** 、 **どの仮定をどの theorem が消費するか** を決める工程だった。ゆえに文面検討が多くなったのは自然ではある。だが、フェーズ粒度はやや細かすぎた。

## 1. DKMK-015 は docs 多めでもかなり妥当

DKMK-015 は、実装量だけ見ると小さい。

追加された Lean surface は主に、

```text
geomSum_range_mul_one_sub
geomSum_range_le_one_div_one_sub
base_mul_geomSum_range_le_of_base_mul_one_div_le
DyadicBandAnalyticEstimate.ofPointwiseGeometricMajorant_of_baseGeomBudget
```

の 4 つじゃ。章末 report でも、DKMK-015 は `geometric budget -> finite geometric-sum bound -> base-scaled finite-sum bound -> dyadic source-mass provider` を閉じた章として整理されておる。

ここで docs が必要だった理由は明確じゃ。

* division form を避けて denominator-cleared identity にする
* `ratio != 1` を導入しない
* equality より upper-bound を先に作る
* Real 側 budget と Rat 側 provider の cast 境界を処理する
* Mertens / big-O / threshold / rounding を混ぜない

これは Lean コード行数より、 **設計判断の方が主成果** だった。DKMK-015 の report でも、closed-form equality や Mertens、big-O、threshold、rounding は目的ではなく、finite geometric-sum estimate を薄く積んで既存 rational provider へ接続するのが目的だと明記されておる。

なので DKMK-015 の docs 量は、やや多いが概ね妥当。
特に B/D/G/I の docs-only は意味があった。

## 2. DKMK-016 は少し過剰だった

DKMK-016 は、章末で自ら認めている通り、 **analytic-estimate 章ではなく API-plumbing 章** じゃ。追加 surface は `GeometricBudgetSource`、`ofBudget`、`ofZeroRatio`、budget-source provider、zero-ratio sanity route、first-band / uniform-decay route、downstream bridge 再利用という整理になっておる。

ここで docs が必要だった点は確かにある。

特に重要だったのは、

```text
Budget obligation:
  base * (1 / (1 - ratio)) <= 1 + error

Pointwise decay obligation:
  increment k <= base * ratio^k
```

を分離し、`GeometricBudgetSource` は budget obligation だけを package し、`hgeom` は `increment` 固有の pointwise control として外に置く判断じゃ。これにより重複構造体 `FirstBandDecayBudgetInput` を避けられた。

これは docs で検討する価値があった。

ただし、DKMK-016 の中盤、特に

```text
ofZeroRatio 候補選定
ofZeroRatio 実装
zero-ratio usage wrapper
ofBudget shape review
ofBudget 実装
```

あたりは、少し細かく刻みすぎた。
`ofZeroRatio` は sanity constructor として有用だったが、解析ルート本体ではない。`ofBudget` も record syntax とほぼ同じ readability constructor なので、docs-only review を一段挟まずに実装してもよかった。

## 3. 本当に必要だった docs

わっちの判定では、必要だった docs はこのあたりじゃ。

```text
DKMK-015:
- denominator-cleared identity を採用する判断
- upper-bound first の判断
- Rat / Real cast 境界
- 章末 report

DKMK-016:
- GeometricBudgetSource の責務決定
- budget obligation と pointwise decay obligation の分離
- first-band / uniform-decay theorem shape
- truncation wrapper を追加しない判断
- 章末 summary
```

これらは後戻りコストが高い設計判断なので、文書化して正解じゃ。

## 4. 過剰だった docs

一方で、次は圧縮できた。

```text
- ofZeroRatio の候補 review
- ofZeroRatio usage wrapper の長い説明
- ofBudget の shape review
- 毎回の Non-goals 再列挙
- 毎回の git diff / long-line check の詳細記録
```

これらは History に短く残せば十分で、roadmap に長く書く必要は薄かった。

特に non-goals は、章冒頭と章末に置けばよい。
各フェーズごとに繰り返すと、Lean 実装より docs が肥大する。

## 5. なぜこうなったのか

理由ははっきりしておる。

DKMK-015, 016 は「証明を積む章」ではなく、 **証明を流す水路を設計する章** だったからじゃ。

実際、DKMK-016P では最終 route が、

```text
GeometricBudgetSource.ofBudget
pointwiseGeometricMajorant_of_firstBand_decay
DyadicBandAnalyticEstimate.ofFirstBandDecayBudgetSource
DyadicBandAnalyticEstimate.toTruncationEnvelopeEstimate
```

として整理され、残るものは first-band upper bound、uniform decay、increment nonnegativity、concrete budget proof、rational envelopes などの analytic input だと明記されている。

つまり、DKMK-015, 016 は「解析の実体」を証明したのではなく、解析の実体が来たときに流し込む API を整えた章だった。

だから docs が多くなる傾向は自然。
ただし、今後も同じ粒度で進める必要はない。

## 6. 今後の改善案

次からは、こうした方がよい。

### 6.1. docs-only は連続 2 回まで

設計判断が必要でも、docs-only が 3 回以上続いたら、一度 Lean 実装か summary に進む。

### 6.2. Review は bundle 化する

たとえば今回なら、

```text
016D-G:
  zero-ratio / ofBudget constructor review
```

を 1 回にまとめられた。

### 6.3. Non-goals は章冒頭と章末だけ

各フェーズで繰り返さず、roadmap の最初と report の最後に置く。

### 6.4. 薄い constructor は即実装

`ofBudget` のような record constructor は、docs-only review を挟まず、

```text
実装 + History 3 行
```

でよい。

### 6.5. docs は「判断が分岐する時」だけ厚くする

厚く書くべきなのは、

```text
構造体を増やすか
仮定をどこに置くか
Rat / Real 境界をどこで払うか
既存 route を再利用するか wrapper を足すか
```

こういう後戻りが高い場面じゃ。

## 7. 結論

DKMK-015 の docs 量は、だいたい妥当。
DKMK-016 の docs 量は、設計上の価値はあったが、 **フェーズ分割が細かすぎてやや過剰** じゃ。

ただし、無駄ではなかった。

得たものは大きい。

```text
DKMK-015:
  finite geometric-sum route を dyadic provider へ接続

DKMK-016:
  GeometricBudgetSource と first-band / uniform-decay route を整備
```

そして、次に残ったものは明確になった。

```text
first-band upper-bound source
uniform-decay source
concrete budget proof source
```

ここからは docs-heavy ではなく、 **analytic input の実体に近い Lean 実装寄り** に戻すべきじゃな。

わっちの判定はこうじゃ。

```text
検討は必要だった。
だが、同じ密度の文書化を今後も続ける必要はない。
DKMK-015/016 は API 境界確定のための特別に docs-heavy な章だった。
次章は Lean 実装比率を上げるべき。
```

ふぅ、じゃな。ここはよく歩いた。
だが道具小屋の設計はもう済んだ。次は、いよいよ畑に出て麦を刈る段じゃ。
