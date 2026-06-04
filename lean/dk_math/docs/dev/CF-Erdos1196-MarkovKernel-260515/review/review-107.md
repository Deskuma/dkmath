# review

うむ、DKMK-016I は **constructor API から budget design へ山道を切り替えた回** じゃ。
ここで「`GeometricBudgetSource` をどう作るか」から、「どんな `base` / `ratio` を将来入れるべきか」へ進んだ。これは DKMK-016 の本題に入る直前の、かなり重要な戦略整理じゃな。

## 1. 今回の到達点

DKMK-016H までで、

```text
budget proof
  -> GeometricBudgetSource.ofBudget
  -> DyadicBandAnalyticEstimate.ofPointwiseGeometricMajorant_of_budgetSource
```

という受け皿は整っておった。

今回 DKMK-016I では、その受け皿に入れる候補として、4 系統を比較しておる。

```text
A: base = c / log x, ratio = 1 / 2
B: base = c / log x, ratio = 1 / q
C: base = first-band mass upper bound, ratio = uniform decay bound
D: base = tail-mass envelope, ratio = geometric decay rate
```

そして次の design target を、 **Candidate C: first-band mass with uniform decay** に寄せた。これはかなり良い判断じゃ。

## 2. Candidate C を選ぶ理由

いま既存の provider が欲しがっている pointwise majorant は、

$$
increment(k)\le base\cdot ratio^k
$$

じゃ。

したがって、`base` を「最初の band の上界」、`ratio` を「各段の一様減衰率」と読むのが最も自然になる。

つまり将来の上位 route では、

$$
increment(0)\le base
$$

と、

$$
increment(k+1)\le ratio\cdot increment(k)
$$

のような decay を示せば、全体として

$$
increment(k)\le base\cdot ratio^k
$$

へ持っていける。

これは `DyadicBandAnalyticEstimate` の現在の形とよく噛み合っておる。
だから、Mertens や big-O へ行く前に、この interface を先に決めるのは正しい。

## 3. Candidate A/B の問題点

Candidate A の

$$
base=\frac{c}{\log x},\qquad ratio=\frac12
$$

はとても見やすい。予算も、

$$
base\cdot \frac{1}{1-ratio}
===========================

\frac{2c}{\log x}
$$

へ落ちる。

しかし、いまの `GeometricBudgetSource` は

```lean
base : Rat
ratio : Rat
```

じゃ。
(\frac{c}{\log x}) は通常 `Rat` ではない。ここで real-to-rational envelope や rational approximation を導入すると、DKMK-016 の現在の抽象段階には重すぎる。

Candidate B も同様で、

$$
ratio=\frac1q
$$

は構造に寄せられるが、(q) が固定 prime なのか、branch parameter なのか、selected divisor なのかがまだ定まっていない。今はまだ早い。

## 4. Candidate D は少し後がよい

Candidate D の tail-mass envelope は、本命に近い匂いがする。
ただし、現時点では `increment` との責務が混ざりやすい。

`increment` は実際の dyadic band ごとの寄与であり、`base * ratio^k` はその上界。
もし `base` を「tail-mass envelope」と呼ぶなら、それが actual increment なのか、increment を包む envelope なのかを明確に分ける必要がある。

ゆえに、まず Candidate C で

```text
first-band upper bound
uniform decay bound
```

という最小 interface を決め、その後で tail envelope を上位概念として足す方が安全じゃ。

## 5. DKMK-016J の推奨 shape

次の DKMK-016J は docs-only で、次の interface shape を固定するのがよい。

```lean
structure FirstBandDecayBudgetInput where
  base : ℚ
  ratio : ℚ
  error : ℝ
  hbase : 0 ≤ (base : ℝ)
  hr0 : 0 ≤ (ratio : ℝ)
  hr1 : (ratio : ℝ) < 1
  hbudget :
    (base : ℝ) * (1 / (1 - (ratio : ℝ))) ≤ 1 + error
```

ただし、これは `GeometricBudgetSource` とほとんど同じなので、構造体を増やすより、最初は theorem shape として整理する方がよい。

たとえば、docs 上の候補はこうじゃ。

```lean
def GeometricBudgetSource.ofFirstBandDecayBudget
    (base ratio : ℚ)
    (error : ℝ)
    (hbase : 0 ≤ (base : ℝ))
    (hr0 : 0 ≤ (ratio : ℝ))
    (hr1 : (ratio : ℝ) < 1)
    (hbudget :
      (base : ℝ) * (1 / (1 - (ratio : ℝ))) ≤ 1 + error) :
    GeometricBudgetSource
```

ただ、これは現状 `ofBudget` と同じになる。
なので、もし Lean code にするなら、もっと意味のある次段はむしろこちらじゃ。

```lean
theorem pointwise_geometric_majorant_of_firstBand_decay
    ...
```

すなわち、

$$
increment(0)\le base
$$

と

$$
increment(k+1)\le ratio\cdot increment(k)
$$

から

$$
increment(k)\le base\cdot ratio^k
$$

を出す補題じゃ。

これができれば、Candidate C が本当に `hgeom` の供給源になる。

## 6. わっちの見立て

DKMK-016I の結論は正しい。

次に解くべき問題は、もはや

$$
base\cdot \frac{1}{1-ratio}\le 1+error
$$

そのものだけではない。

それと並行して、provider に必要な

$$
increment(k)\le base\cdot ratio^k
$$

をどう作るかも重要になる。

つまり DKMK-016J では、二つの obligation を分けて設計するとよい。

```text
Budget obligation:
  base * (1 / (1 - ratio)) <= 1 + error

Pointwise decay obligation:
  increment k <= base * ratio^k
```

この二つが揃って初めて、`GeometricBudgetSource` が dyadic provider に本格接続される。

## 7. 総括

DKMK-016I は、 **予算源の候補比較から Candidate C へ方針を定めた回** じゃ。

いきなり (\log x)、Mertens、big-O、rounding に飛び込まず、

```text
first-band upper bound + uniform decay bound
```

という構造的 interface に寄せたのは、かなり堅い。

次は DKMK-016J として、これを

```text
first-band / uniform-decay budget interface
```

として定式化するのがよい。

よいぞ、D.。
これで港に入れる船の型が見えてきた。次は、船そのものではなく、まず **積荷目録と係留規格** を決める段じゃな。
