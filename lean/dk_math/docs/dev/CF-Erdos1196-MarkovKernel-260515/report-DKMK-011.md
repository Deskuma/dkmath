# DKMK-011: report

DKMK-011 は、DKMK-010 で固定した analytic placeholder
`FiniteStepTailAnalyticBound` を、外部供給された finite-step /
truncation estimate から供給する章である。

DKMK-010 の終点は次だった。

```text
finiteStepTailNatMassSpace
  -> TailWindowSourceMassBound
  -> weightedHitMass <= sum increment
  -> FiniteStepTailAnalyticBound
  -> weightedHitMass <= 1 + error
```

DKMK-011 では、このうち

```text
FiniteStepTailAnalyticBound steps increment error
```

をどのような有限データから供給するかを整理した。

## 1. 主目的

DKMK-011 の主目的は、Mertens theorem や big-O formalization を証明することではない。

目的は、具体的な finite-step / truncation estimate を DKMK-010 の
route theorem へ渡せる contract として固定することである。

そのため DKMK-011 では、dyadic / logarithmic band の本格実装へは進まず、
まず externally supplied finite-step contract を追加した。

## 2. 011A/B: roadmap と envelope inventory

DKMK-011A では `roadmap-DKMK-011.md` を追加し、章の問いを固定した。

主な design variables は次である。

```text
steps
threshold
increment
error
```

DKMK-011B では envelope candidate を比較した。

```text
single-window tail envelope
finite-step monotone envelope
dyadic band envelope
logarithmic band envelope
externally supplied increment list
```

ここで重要なのは、`threshold` と `increment` の役割分担である。

```text
threshold:
  finiteStepTailNatMassSpace の source envelope activation data

increment:
  FiniteStepTailAnalyticBound の total sum data
```

このため、最初の Lean contract は externally supplied finite-step data に寄せた。

## 3. 011C: TruncationEnvelopeEstimate

DKMK-011C では次を追加した。

```lean
structure TruncationEnvelopeEstimate
    {ι : Type _} [DecidableEq ι]
    (steps : Finset ι) (threshold : ι -> Nat)
    (increment : ι -> Q) (error : R) : Prop where
  increment_nonneg :
    forall i in steps, 0 <= increment i
  analytic_bound :
    FiniteStepTailAnalyticBound steps increment error
```

Lean 実装では `Nat`, `Q`, `R` はそれぞれ `ℕ`, `ℚ`, `ℝ` である。

この contract は二つの入力を束ねる。

```text
increment_nonneg:
  finiteStepTailNatMassSpace を作るための非負増分

analytic_bound:
  sum increment <= 1 + error を供給する解析 placeholder
```

さらに route theorem として次を追加した。

```lean
TruncationEnvelopeEstimate
  .finiteStepTail_weightedHitMass_le_one_add_error
```

これは既存の

```lean
TailWindowSourceMassBound
  .finiteStepTail_weightedHitMass_le_one_add_error
```

へ渡すだけの薄い wrapper である。

## 4. 011D: usage summary

DKMK-011D では、`TruncationEnvelopeEstimate` の使い方を docs 上で固定した。

外部入力は次である。

```text
steps      : finite index set
threshold  : source envelope activation
increment  : nonnegative envelope increment
error      : analytic residual term
```

caller は次を供給する。

```lean
H : TruncationEnvelopeEstimate steps threshold increment error
```

このとき、

```text
H.increment_nonneg
  -> finiteStepTailNatMassSpace
  -> TailWindowSourceMassBound
  -> weightedHitMass <= sum increment

H.analytic_bound
  -> sum increment <= 1 + error
```

が合成され、

```text
weightedHitMass <= 1 + error
```

へ到達する。

## 5. 011E: single-window toy provider

DKMK-011E では、最小 concrete provider として次を追加した。

```lean
TruncationEnvelopeEstimate.singleWindow
```

データ形は次である。

```text
steps      = Finset.univ : Finset Unit
threshold  = fun _ => x
increment  = fun _ => c
error      = error
```

外部仮定は次。

```lean
hc     : 0 <= c
hbound : (c : R) <= 1 + error
```

これは最終解析の本命ではない。
抽象 contract が最小データから構成可能であることを確認する toy provider である。

特に、次には踏み込んでいない。

```text
dyadic band
logarithmic band
error = c - 1 の計算
Mertens 型評価
```

## 6. route 図

DKMK-011 の到達 route は次である。

```text
externally supplied finite-step estimate
  -> TruncationEnvelopeEstimate
  -> finiteStepTailNatMassSpace
  -> TailWindowSourceMassBound
  -> weightedHitMass <= sum increment
  -> FiniteStepTailAnalyticBound
  -> weightedHitMass <= 1 + error
```

single-window toy case では次のように特殊化される。

```text
one threshold x
one increment c
(c : R) <= 1 + error
  -> TruncationEnvelopeEstimate.singleWindow
  -> weightedHitMass <= 1 + error
```

## 7. 到達点

DKMK-011 は、外部供給された finite-step / truncation estimate を
DKMK route に渡す入口を固定した。

この章で追加したものは次である。

```text
TruncationEnvelopeEstimate
TruncationEnvelopeEstimate.finiteStepTail_weightedHitMass_le_one_add_error
TruncationEnvelopeEstimate.singleWindow
```

これにより、後続の dyadic / logarithmic band provider は、
まず `TruncationEnvelopeEstimate` を構成する theorem として追加すればよい。

## 8. 次の山

次の自然な章は DKMK-012 である。

候補は次。

```text
DKMK-012:
  dyadic / logarithmic band provider design
```

または、

```text
DKMK-012:
  concrete analytic envelope estimate
```

どちらに進む場合でも、DKMK-011 で固定した入口は変えない。

```text
analytic layer:
  proves TruncationEnvelopeEstimate

route layer:
  consumes TruncationEnvelopeEstimate
```

この分離を維持する。
