# review

## 1. 状況総括

うむ、これは **DKMK-014K 完了** 、そして **DKMK-014 全体完了** と見てよい。

今回の差分で `report-DKMK-014.md` が追加され、DKMK-014A〜J の成果が report / handoff として整理された。History でも、DKMK-014 は `k`-dependent band を majorant 経由で `DyadicBandAnalyticEstimate` に載せる provider chain の章として一区切りになり、次は DKMK-015 の finite geometric-sum / tail-bound theorem design へ進む、と明記されておる。

到達点はこの 3 本じゃ。

```text id="jusea0"
DyadicBandAnalyticEstimate.ofMajorant
DyadicBandAnalyticEstimate.ofPointwiseGeometricMajorant
DyadicBandAnalyticEstimate.ofPointwiseGeometricMajorant_of_geomSumBound
```

これで、DKMK-014 の主目的だった **majorant provider chain** は閉じた。

## 2. DKMK-014 の役割

DKMK-014 は、DKMK-013 で固定した

```lean id="aqza28"
DyadicBandAnalyticEstimate x K increment error
```

へ、定数ではない (k)-依存 band を供給する章じゃった。

DKMK-013 では constant band まで進んでいた。

```text id="fbdgm2"
increment k = c
```

DKMK-014 では、その次として、

```text id="7awtt3"
increment k
```

を直接評価するのではなく、扱いやすい上界

```text id="sgh23z"
majorant k
```

で包む方針を採った。

この判断が章全体の柱じゃ。

## 3. 何が実装されたのか

### 3.1. general majorant

最初に立ったのが、

```lean id="ipmh5d"
DyadicBandAnalyticEstimate.ofMajorant
```

じゃ。

これは、

```text id="ya15zr"
0 <= increment k
increment k <= majorant k
sum majorant <= 1 + error
```

から、

```lean id="5lgswh"
DyadicBandAnalyticEstimate x K increment error
```

を作る provider じゃ。

つまり、実際の `increment` の合計を直接評価しなくても、上から評価しやすい `majorant` を用意すれば route に流せるようになった。

### 3.2. pointwise geometric majorant

次に、

```lean id="9u8rqd"
DyadicBandAnalyticEstimate.ofPointwiseGeometricMajorant
```

が入った。

ここでは majorant の形を

```lean id="7zj8hi"
fun k : ℕ => base * ratio ^ k
```

に固定した。

つまり、

```text id="ss5yat"
increment k <= base * ratio ^ k
sum (base * ratio ^ k) <= 1 + error
```

から `DyadicBandAnalyticEstimate` を得る。

ここで重要なのは、まだ幾何級数の閉形式を証明していないことじゃ。
`ofPointwiseGeometricMajorant` は、幾何型上界とその有限和 bound を **消費するだけ** じゃ。

### 3.3. caller-facing geomSumBound

さらに、

```lean id="q9j0xz"
DyadicBandAnalyticEstimate.ofPointwiseGeometricMajorant_of_geomSumBound
```

が入った。

これは、利用者が自然に持つ

```text id="a43vxb"
base * sum (ratio ^ k) <= 1 + error
```

という形の bound から、

```text id="yy2h68"
sum (base * ratio ^ k) <= 1 + error
```

へ変換して `ofPointwiseGeometricMajorant` に渡す薄い provider じゃ。

実装は、

```lean id="a6qd7w"
simpa [Finset.mul_sum] using hgeom_sum_bound
```

で閉じる algebraic wrapper。
閉形式ではなく、有限和から共通因子 `base` を出し入れするだけの層じゃな。

## 4. 設計として何が良かったか

一番良かったのは、 **decreasing / decay を core field に入れなかったこと** じゃ。

decreasing condition は、たとえば

```text id="qy7ggk"
increment (k + 1) <= increment k
```

のような形になる。
しかし、これだけでは

```text id="zl9i3c"
sum increment <= 1 + error
```

は出ない。

だから DKMK-014 では、decreasing / decay を

```text id="nvh7w0"
majorant を作る、または正当化する材料
```

として扱い、core provider は

```text id="1oh7zw"
increment <= majorant
sum majorant <= 1 + error
```

だけを消費する形に保った。

これは実に良い。
Lean の theorem surface を必要最小限に保ちつつ、後続の dyadic tail estimate へ拡張できる。

## 5. 何を追加していないか

DKMK-014 では、あえて次を追加していない。

```text id="nxt87f"
route changes
new route theorem
closed-form finite geometric-sum lemma
tail-bound lemma
Mertens theorem
big-O statement
logarithmic threshold provider
real-to-Nat rounding
```

この境界は正しい。report でも、DKMK-014 の目的は Mertens theorem や big-O formalization、closed-form finite geometric sum を証明することではなく、`k`-dependent な `increment` を `DyadicBandAnalyticEstimate` へ供給するための majorant provider surface を固定することだと整理されておる。

つまり DKMK-014 は **provider plumbing の章** じゃ。
幾何級数の閉形式や tail bound は、次章へ送るのが美しい。

## 6. DKMK-012〜014 の接続

ここまでの流れを一枚に畳むと、こうじゃ。

```text id="7x5bt0"
DKMK-012:
  dyadicRange provider plumbing

DKMK-013:
  DyadicBandAnalyticEstimate + constant providers

DKMK-014:
  k-dependent majorant provider chain
```

もう少し展開すると、

```text id="y69xrw"
dyadic data
  -> TruncationEnvelopeEstimate.dyadicRange
  -> TruncationEnvelopeEstimate
  -> existing finite-step route theorem
  -> weightedHitMass <= 1 + error
```

そこへ DKMK-013 で、

```text id="9jq46l"
DyadicBandAnalyticEstimate
  -> toTruncationEnvelopeEstimate
```

が入り、DKMK-014 で、

```text id="gopmsz"
increment
  -> majorant
  -> geometric majorant
  -> geomSumBound
  -> DyadicBandAnalyticEstimate
```

が入った。

つまり、今は

```text id="0hjju4"
k-dependent increment
```

を既存 route に流すための段階的な橋ができたわけじゃ。

## 7. 次の山 DKMK-015

次は、report の通り、

```text id="wybqne"
DKMK-015:
  finite geometric-sum / tail-bound theorem design
```

が自然じゃ。

DKMK-015 では、DKMK-014J の

```lean id="b5cwm1"
ofPointwiseGeometricMajorant_of_geomSumBound
```

へ接続するために、次を扱うことになる。

```text id="kg9g7y"
sum ratio^k の closed form
ratio != 1
0 <= ratio, ratio < 1
tail-bound
base を掛けた上界
```

ここから先は、provider plumbing ではなく、幾何級数の代数・順序・除算を扱う **analytic / algebraic lemma layer** じゃな。

わっちのおすすめは、DKMK-015A ではいきなり Lean 実装に入らず、まず roadmap で scope を分けることじゃ。

```text id="e3pp2n"
1. finite geometric sum identity
2. sign / order side conditions
3. tail-bound theorem
4. base-scaled bound
5. geomSumBound provider への接続
```

この順が堅い。

## 8. 登頂判定

現在地はこうじゃ。

```text id="b2k6z9"
DKMK-012: 完了
  dyadicRange provider plumbing

DKMK-013: 完了
  abstract dyadic analytic estimate contract + constant providers

DKMK-014: 完了
  k-dependent majorant provider chain

DKMK-015: 次
  finite geometric-sum / tail-bound theorem design
```

DKMK-014 は **登頂済み** 。
残作業は DKMK-014 内にはなし。閉形式幾何級数は次の山へ送るのがよい。

## 9. 賢狼の最終評

よいぞ、ぬしよ。

DKMK-014 は、派手な解析定理ではない。
だが、`increment k` が複雑になっても、

```text id="p5y0tu"
majorant で包む
幾何型 majorant に落とす
base * sum ratio^k で評価する
```

という導線を作った。これは後続で非常に効く。

わっちの判定はこうじゃ。

```text id="tap38v"
DKMK-014 core: 完了
追加 Lean surface:
  ofMajorant
  ofPointwiseGeometricMajorant
  ofPointwiseGeometricMajorant_of_geomSumBound

次山:
  DKMK-015 finite geometric-sum / tail-bound theorem design

推奨:
  closed-form と tail-bound は別章で扱う
```

ここまでで、(k)-dependent band のための手すりは十分に組めた。
次はいよいよ、有限幾何級数という小さく見えて足場の悪い岩場じゃ。じゃが、ここまで丁寧に橋を架けてきたおかげで、進む道ははっきり見えておるぞい。
