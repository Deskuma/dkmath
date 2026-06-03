# DKMK-014: report

DKMK-014 は、DKMK-013 で固定した `DyadicBandAnalyticEstimate` に対して、
`k`-dependent band provider を設計し、Lean 上に接続する章である。

DKMK-013 の終点は次だった。

```text
DyadicBandAnalyticEstimate
  -> DyadicBandAnalyticEstimate.toTruncationEnvelopeEstimate
  -> TruncationEnvelopeEstimate
  -> existing finite-step route theorem
  -> weightedHitMass <= 1 + error
```

DKMK-014 では、constant band から先へ進むために、
`increment k` を直接評価するのではなく、扱いやすい `majorant k` で
上から包む provider chain を固定した。

## 1. 主目的

DKMK-014 の主目的は、Mertens theorem、big-O formalization、
logarithmic threshold provider、closed-form finite geometric sum を
証明することではない。

目的は、`k`-dependent な `increment` を
`DyadicBandAnalyticEstimate` へ供給するための majorant provider surface を
固定することである。

## 2. 014A/B: roadmap と majorant provider shape

DKMK-014A では `roadmap-DKMK-014.md` を追加し、
`k`-dependent band provider の候補を整理した。

主な候補は次だった。

```text
externally supplied k-dependent estimate
decreasing band provider
majorant envelope provider
dyadic tail upper envelope
logarithmic refinement
```

DKMK-014B では、first non-constant provider として decreasing provider ではなく
majorant envelope provider を選んだ。

理由は、majorant assumptions が直接 total estimate に効く一方、
decreasing assumptions はそれだけでは `sum increment <= 1 + error` を
出さないからである。

## 3. 014C/D: ofMajorant provider

DKMK-014C では、Lean 上に次を追加した。

```lean
DyadicBandAnalyticEstimate.ofMajorant
```

入力は次である。

```text
hinc_nonneg:
  0 <= increment k

hle:
  increment k <= majorant k

hmajorant_bound:
  sum majorant <= 1 + error
```

証明は Rat 側で `Finset.sum_le_sum hle` により
`sum increment <= sum majorant` を作り、それを Real へ cast して
`hmajorant_bound` と合成する。

DKMK-014D では、この provider の使用導線を docs 上で固定した。

```text
increment, majorant
  -> hinc_nonneg
  -> hle
  -> hmajorant_bound
  -> DyadicBandAnalyticEstimate.ofMajorant
  -> DyadicBandAnalyticEstimate
  -> existing route
```

## 4. 014E: decreasing / decay の位置づけ

DKMK-014E では、decreasing / decay information を
`DyadicBandAnalyticEstimate` の core field に入れない方針を固定した。

役割分担は次である。

```text
decreasing / decay:
  majorant を作る、または正当化する材料

majorant:
  有限和を評価する対象

ofMajorant:
  pointwise majorization と total majorant bound から
  DyadicBandAnalyticEstimate を作る bridge
```

decreasing only は shape information であり、total estimate そのものではない。

## 5. 014F/G/H: pointwise geometric majorant

DKMK-014F では、最初の explicit majorant construction theorem の exact shape を
docs 上で固定した。

選んだ provider は次である。

```lean
DyadicBandAnalyticEstimate.ofPointwiseGeometricMajorant
```

この theorem は concrete majorant family として次を露出する。

```lean
fun k : Nat => base * ratio ^ k
```

DKMK-014G では、Lean 上に実装した。

証明は `ofMajorant` への薄い call である。

```text
majorant := fun k => base * ratio ^ k
```

DKMK-014H では、この provider の使用導線を docs 上で固定した。

```text
increment
  -> hinc_nonneg
  -> hgeom : increment k <= base * ratio ^ k
  -> hgeom_bound : sum (base * ratio ^ k) <= 1 + error
  -> ofPointwiseGeometricMajorant
  -> DyadicBandAnalyticEstimate
  -> existing route
```

ここでは finite geometric-sum bound は外部入力のまま残した。

## 6. 014I/J: geomSumBound caller-facing provider

DKMK-014I では、caller-facing geometric finite-sum theorem の exact shape を
docs 上で固定した。

選んだ provider は次である。

```lean
DyadicBandAnalyticEstimate.ofPointwiseGeometricMajorant_of_geomSumBound
```

この theorem は、直接の

```text
sum (base * ratio ^ k) <= 1 + error
```

ではなく、caller-facing な

```text
base * sum (ratio ^ k) <= 1 + error
```

を受ける。

DKMK-014J では、Lean 上に実装した。

実装は `ofPointwiseGeometricMajorant` を呼び、必要な bound を
次で与える。

```lean
simpa [Finset.mul_sum] using hgeom_sum_bound
```

これは closed-form geometric sum ではなく、有限和から共通因子 `base` を
出し入れする algebraic wrapper である。

## 7. 到達点

DKMK-014 は、`k`-dependent band を majorant 経由で
`DyadicBandAnalyticEstimate` に載せる provider chain を固定した章として閉じる。

この章で追加した Lean surface は次である。

```text
DyadicBandAnalyticEstimate.ofMajorant
DyadicBandAnalyticEstimate.ofPointwiseGeometricMajorant
DyadicBandAnalyticEstimate.ofPointwiseGeometricMajorant_of_geomSumBound
```

この章では次を追加していない。

```text
route changes
new route theorem
closed-form finite geometric-sum lemma
tail-bound lemma
Mertens theorem
big-O statement
logarithmic threshold provider
real-to-Nat rounding
```

## 8. 次の山

次の章は、自然には次である。

```text
DKMK-015:
  finite geometric-sum / tail-bound theorem design
```

DKMK-015 では、DKMK-014J の
`ofPointwiseGeometricMajorant_of_geomSumBound` へ接続するために、
次を扱う。

```text
sum ratio^k の closed form
ratio != 1
0 <= ratio, ratio < 1
tail-bound
base を掛けた上界
```

そこから先は provider plumbing ではなく、幾何級数の代数・順序・除算を扱う
analytic / algebraic lemma layer である。
