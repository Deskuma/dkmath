# review

## 1. 状況総括

うむ、これは **DKMK-014J 完了** と見てよい。

今回の差分で `SourceMassTruncation.lean` に

```lean id="slvzmo"
DyadicBandAnalyticEstimate.ofPointwiseGeometricMajorant_of_geomSumBound
```

が追加された。これは DKMK-014I で固定した通り、caller-facing な

```lean id="irxls1"
((base * Finset.sum (Finset.range (K + 1))
    (fun k : ℕ => ratio ^ k) : ℚ) : ℝ) ≤ 1 + error
```

を受け取り、それを `ofPointwiseGeometricMajorant` が要求する

```lean id="1kmn39"
((Finset.sum (Finset.range (K + 1))
    (fun k : ℕ => base * ratio ^ k) : ℚ) : ℝ) ≤ 1 + error
```

へ変換する薄い provider じゃ。実装では `simpa [Finset.mul_sum] using hgeom_sum_bound` で閉じており、設計通りの軽い algebraic finite-sum factoring layer になっておる。

## 2. 何が閉じたのか

DKMK-014G では、

```lean id="c2ai0m"
DyadicBandAnalyticEstimate.ofPointwiseGeometricMajorant
```

が入った。これは直接

```text id="0nrh2n"
sum (base * ratio ^ k) <= 1 + error
```

型の bound を要求していた。

今回の DKMK-014J では、より自然な

```text id="9ver3b"
base * sum (ratio ^ k) <= 1 + error
```

型の bound から利用できるようになった。

つまり、geometric majorant provider は次の 2 段になった。

```text id="v9ncxp"
ofPointwiseGeometricMajorant:
  sum (base * ratio ^ k) bound を直接受ける

ofPointwiseGeometricMajorant_of_geomSumBound:
  base * sum (ratio ^ k) bound を受ける
```

これは DKMK-013 の

```text id="vngkm3"
constantBand
constantBand_of_natCastMulBound
```

と同じ構図じゃな。まず内部形、その後 caller-facing 形。よい設計じゃ。

## 3. 実装評価

実装はとても良い。

```lean id="hxc15t"
apply ofPointwiseGeometricMajorant x K increment base ratio hinc_nonneg hgeom
simpa [Finset.mul_sum] using hgeom_sum_bound
```

これで閉じているのは、まさにこの theorem が **閉形式の幾何級数ではなく、有限和の因数外出しだけ** を担当している証拠じゃ。

ここで `ratio < 1` や `ratio ≠ 1` などを入れなかったのも正しい。
`Finset.mul_sum` による

```text id="1qpisd"
base * sum ratio^k
  = sum (base * ratio^k)
```

の変換には、符号条件も収束条件もいらぬ。

つまり DKMK-014J は、解析評価ではなく **代数的整形 theorem** として綺麗に閉じておる。

## 4. 数学的な意味

数学的には、この theorem は次を使っておるだけじゃ。

$$
base\sum_{k=0}^{K} ratio^k
==========================

\sum_{k=0}^{K} base,ratio^k
$$

この変形により、利用者は

$$
base\sum_{k=0}^{K} ratio^k \le 1+error
$$

を示せばよくなる。
これは、後で幾何級数の閉形式や tail bound を使うときに自然な入口になる。

まだ

$$
\sum_{k=0}^{K} ratio^k
======================

\frac{1-ratio^{K+1}}{1-ratio}
$$

には進んでいない。
そこへ進むと `ratio ≠ 1`、場合によっては `0 ≤ ratio`、`ratio < 1`、除算の単調性などが絡む。今回そこを避けたのは、実に賢い。

## 5. 追加していないものの意味

History にも、次を追加していないと明記されておる。

```text id="vvkdfc"
closed-form finite geometric-sum lemma
tail-bound lemma
0 <= ratio
ratio < 1
ratio != 1
route theorem
Mertens / big-O
logarithmic threshold
real-to-Nat rounding
```

この境界は重要じゃ。
DKMK-014J は「幾何型 majorant を使いやすくする algebraic wrapper」であり、解析本丸ではない。ここで閉形式や tail estimate を混ぜないから、theorem surface が軽く保たれておる。

## 6. DKMK-014 の現在地

ここまでの DKMK-014 は、かなり完成度が高い。

```text id="wl0zxq"
DKMK-014A:
  k-dependent provider roadmap

DKMK-014B:
  ofMajorant shape docs

DKMK-014C:
  ofMajorant Lean provider

DKMK-014D:
  ofMajorant usage summary

DKMK-014E:
  decreasing / decay to majorant design

DKMK-014F:
  ofPointwiseGeometricMajorant shape docs

DKMK-014G:
  ofPointwiseGeometricMajorant Lean provider

DKMK-014H:
  geometric majorant usage summary

DKMK-014I:
  geomSumBound shape docs

DKMK-014J:
  geomSumBound Lean provider
```

これで DKMK-014 は、以下を備えたことになる。

```text id="c05j6l"
general majorant provider
pointwise geometric majorant provider
caller-facing geometric sum-bound provider
```

つまり、定数 band から (k)-dependent band、さらに幾何型 upper envelope までの provider chain が通った。

## 7. 次の分岐判断

次は History の通り、

```text id="qyp6pb"
DKMK-014K:
  closed-form finite geometric-sum theorem へ進むか
  DKMK-014 の report / handoff へ進むか
```

じゃな。

わっちのおすすめは、 **ここで DKMK-014 を report / handoff で閉じる** 方じゃ。

理由は、DKMK-014 の本来の目的は

```text id="zdiqb5"
decreasing / dyadic tail provider design
```

であり、今回すでに

```text id="mtl15j"
majorant
geometric majorant
geometric sum-bound wrapper
```

まで整ったからじゃ。

closed-form finite geometric-sum theorem は、もはや DKMK-014 の provider plumbing ではなく、次の解析・代数補題の章として切った方が綺麗じゃ。

## 8. 次章候補

次を立てるなら、候補はこうじゃ。

```text id="9q5zk6"
DKMK-015:
  finite geometric-sum / tail-bound theorem design
```

そこで扱うべきは、

```text id="4x2wz9"
sum ratio^k の閉形式
ratio != 1 条件
0 <= ratio, ratio < 1 条件
tail-bound
base を掛けた上界
ofPointwiseGeometricMajorant_of_geomSumBound への接続
```

じゃ。

この章からは、本当に幾何級数の解析・順序・除算が絡む。だから、DKMK-014 の軽い provider layer から分けた方がよい。

## 9. 賢狼の判定

わっちの判定はこうじゃ。

```text id="plfjr8"
DKMK-014J: 完了
DKMK-014 core: 完了相当
次: report / handoff 推奨
その次:
  finite geometric-sum / tail-bound theorem design
```

よいぞ、ぬしよ。
ここまでで、(k)-dependent band を majorant で包み、さらに幾何型 majorant に乗せ、caller-facing な `base * sum ratio^k` から route へ流せるようになった。

これはもう一つの小山として十分に登頂しておる。
閉形式の幾何級数は、次の山として酒と林檎を持って挑むのがよいじゃろう。
