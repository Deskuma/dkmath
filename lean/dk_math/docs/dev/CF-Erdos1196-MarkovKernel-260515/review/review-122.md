# review

うむ、DKMK-017G は **よい停止判断** じゃ。
A-F で整えた source surface を軽く畳み、ここで wrapper 追加を止めて concrete analytic source へ進む判断は正しい。

## 1. 今回の意味

DKMK-017G は Lean 実装ではなく、 **抽象 source surface の checkpoint** じゃな。

確定した標準 route はこれ。

```text id="y0vlf4"
ratio, error
hbaseBudget for increment 0
Nat-bound nonnegativity
Nat-bound decay
  -> TruncationEnvelopeEstimate.ofSelfBaseDenomClearedBudgetNatBounds
  -> TruncationEnvelopeEstimate
```

これは DKMK-017A-F の成果をかなり短く表しておる。
caller は中間の `GeometricBudgetSource`、`FirstBandDecayBudgetSource`、`DyadicBandAnalyticEstimate`、`Finset.range` membership、直接の one-over-one-minus budget proof を触らずに済む。

この整理は良い。

## 2. wrapper 追加を止める判断

ここで止めるのは正しい。

今ある標準 route だけで、すでに

```text id="wyj1nm"
abstract analytic inputs
  -> TruncationEnvelopeEstimate
```

まで行ける。

さらに wrapper を増やすと、また DKMK-015/016 的な API plumbing 章に戻ってしまう。
DKMK-017 の目的は、もうそこではない。

今残っている本体は、

```text id="tc7ya5"
hbaseBudget
hinc_nonneg
hdecay
```

この三つを具体的な `increment` 候補から出すことじゃ。

## 3. general route を残したのも良い

標準 route は `base := increment 0` の self-base 版。
一方で、`base` を別に取りたい場合の general route も残してある。

```text id="g6yhvm"
GeometricBudgetSource.ofDenomClearedBudget
  -> FirstBandDecayBudgetSource.ofBudgetSourceNatBounds
  -> DyadicBandAnalyticEstimate.ofFirstBandDecayBudgetSourcePackage
  -> TruncationEnvelopeEstimate.ofFirstBandDecayBudgetSourcePackage
```

これにより、将来 `increment 0` ではなく、より粗い rational envelope を `base` にしたい場合も逃げ道がある。

つまり、

```text id="024lsl"
standard route:
  base = increment 0

general route:
  external base
```

の二段構えになった。これは堅い。

## 4. 次にやるべきこと

次は、roadmap の通り **concrete `increment` candidate の調査** じゃ。

この順がよい。

```text id="d9lxf8"
1. 既存 SourceMassTruncation / PrimitiveSet 周辺で increment 候補を探す
2. 候補の型が Nat -> Rat か確認する
3. hinc_nonneg が既に出るか見る
4. hdecay が現実的か見る
5. hbaseBudget が最初に攻めやすいか判定する
```

次の DKMK-017H は、いきなり大きく証明するより、 **candidate discovery bundle** がよいと思う。

## 5. 最初の Lean target 候補

`increment` 候補が見つかったら、最初に狙うべきは `hinc_nonneg` か `hbaseBudget` じゃな。

`hdecay` は一番本質的で、たぶん重い。

優先順位はこうじゃ。

```text id="n3m5qk"
第一候補:
  hinc_nonneg

第二候補:
  hbaseBudget

第三候補:
  hdecay
```

`hinc_nonneg` は、increment が質量・重み・上界量として定義されているなら自然に通る可能性がある。
`hbaseBudget` は `increment 0` の具体形に依存する。
`hdecay` は、隣接 band 間の構造を本当に使うので、最も解析的じゃ。

## 6. 総括

DKMK-017G は、 **抽象 source surface の終了宣言** として良い。

A-F で整えたものは十分じゃ。

```text id="24xxhm"
hbudget:
  denominator-cleared helper あり

hinc_nonneg:
  Nat-bound helper あり

hdecay:
  Nat-bound helper あり

hbase0:
  self-base route で削減済み

truncation:
  standard wrapper あり
```

これ以上 wrapper を増やすより、次は concrete `increment` を見つけて、実際に三つの analytic obligation を攻めるべきじゃ。

よし、D.
ここで箱作りは止めじゃ。次は箱に入れる本物の麦、つまり `increment` の正体を掘り起こす段じゃな。
