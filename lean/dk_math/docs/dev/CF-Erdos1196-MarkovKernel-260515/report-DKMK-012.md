# DKMK-012: report

DKMK-012 は、DKMK-011 で固定した
`TruncationEnvelopeEstimate` に対して、dyadic band provider を設計し、
Lean 上に接続する章である。

DKMK-011 の終点は次だった。

```text
externally supplied finite-step estimate
  -> TruncationEnvelopeEstimate
  -> existing finite-step tail route
  -> weightedHitMass <= 1 + error
```

DKMK-012 では、このうち

```text
TruncationEnvelopeEstimate steps threshold increment error
```

を dyadic range data から供給する入口を固定した。

## 1. 主目的

DKMK-012 の主目的は、Mertens theorem、big-O formalization、
logarithmic threshold provider を証明することではない。

目的は、dyadic band data を `TruncationEnvelopeEstimate` へ渡せる
provider shape と usage を固定することである。

そのため `increment` と `hbound` は、解析側から外部供給される入力として
残した。

## 2. 012A/B: roadmap と provider shape

DKMK-012A では `roadmap-DKMK-012.md` を追加し、章の範囲を固定した。

最初の provider は dyadic range provider とした。

```text
steps     = Finset.range (K + 1)
threshold = fun k : Nat => x * 2^k
```

DKMK-012B では、Lean 実装前に data shape と theorem name を固定した。

入力 data は次である。

```text
x         : Nat
K         : Nat
increment : Nat -> Q
error     : R
```

必要な証明入力は次である。

```text
hinc:
  forall k in Finset.range (K + 1), 0 <= increment k

hbound:
  ((Finset.sum (Finset.range (K + 1)) increment : Q) : R) <=
    1 + error
```

theorem name は次に固定した。

```lean
TruncationEnvelopeEstimate.dyadicRange
```

`dyadicRange` という名前は、dyadic threshold と range-indexed finite
steps の両方を表す。

## 3. 012C: Lean provider

DKMK-012C では、`SourceMassTruncation.lean` に次を追加した。

```lean
TruncationEnvelopeEstimate.dyadicRange
```

この theorem は packaging provider のみに留めた。

```text
increment_nonneg := hinc
analytic_bound.total_le_one_add_error := hbound
```

ここでは次を追加していない。

```text
dyadic-specific route theorem
logarithmic provider
Mertens theorem
big-O statement
computed increment formula
```

## 4. 012D: usage summary

DKMK-012D では、`dyadicRange` の使用経路を docs 上で固定した。

```text
dyadic data
  -> hinc and hbound
  -> TruncationEnvelopeEstimate.dyadicRange
  -> TruncationEnvelopeEstimate
  -> TruncationEnvelopeEstimate.finiteStepTail_weightedHitMass_le_one_add_error
  -> weightedHitMass <= 1 + error
```

この流れでは、route theorem は既存のものを使う。
dyadic 専用の hitting theorem は不要である。

## 5. 012E: increment / hbound design

DKMK-012E では、`increment` と `hbound` の解析的意味を整理した。

```text
increment k:
  第 k dyadic band の analytic upper envelope を表す
  externally supplied rational band weight
```

`hinc` は finite-step source mass construction の非負性を担う。

```text
hinc:
  forall k in Finset.range (K + 1), 0 <= increment k
```

`hbound` は有限個の dyadic band envelope の total estimate を担う。

```text
hbound:
  ((Finset.sum (Finset.range (K + 1)) increment : Q) : R) <=
    1 + error
```

候補となる将来の供給元は次である。

```text
externally supplied band weights
dyadic tail upper envelope
later logarithmic refinement
concrete number-theoretic estimate
```

## 6. 到達点

DKMK-012 は、dyadic band provider の器を固定した章として閉じる。

この章で固定したのは次である。

```text
dyadic range data
  -> TruncationEnvelopeEstimate.dyadicRange
  -> existing DKMK-011 route theorem
```

解析側の実質的な仕事はまだ外部に残っている。

```text
increment k をどう選ぶか
hbound をどう証明するか
```

## 7. 次の山

次の章は、自然には次である。

```text
DKMK-013:
  dyadic tail upper envelope design
```

DKMK-013 では、Mertens theorem へ直行する前に、
`increment` と `hbound` を供給する abstract dyadic analytic estimate
contract を検討する。

想定される方向は次である。

```text
dyadic analytic estimate contract
  -> increment nonnegativity
  -> total estimate
  -> TruncationEnvelopeEstimate.dyadicRange
```

この順序なら、route layer を触らずに analytic layer を段階的に増やせる。
