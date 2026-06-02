# DKMK-013: report

DKMK-013 は、DKMK-012 で固定した dyadic range provider に対して、
解析側が証明すべき abstract dyadic analytic estimate contract を設計し、
Lean 上に接続する章である。

DKMK-012 の終点は次だった。

```text
dyadic range data
  -> TruncationEnvelopeEstimate.dyadicRange
  -> TruncationEnvelopeEstimate
  -> existing DKMK-011 route theorem
  -> weightedHitMass <= 1 + error
```

DKMK-013 では、このうち外部入力だった

```text
increment_nonneg
total_le_one_add_error
```

を解析側 contract として命名した。

## 1. 主目的

DKMK-013 の主目的は、Mertens theorem、big-O formalization、
logarithmic threshold provider を証明することではない。

目的は、dyadic band family に対する解析側の theorem-facing target を
固定し、それを DKMK-012 の `dyadicRange` provider へ渡すことである。

その target が次である。

```lean
DyadicBandAnalyticEstimate x K increment error
```

## 2. 013A/B: roadmap と exact shape

DKMK-013A では `roadmap-DKMK-013.md` を追加し、章の範囲を固定した。

問いは次である。

```text
increment k をどう選ぶか
hbound をどう証明するか
```

DKMK-013B では、Lean 実装前に contract shape を固定した。

```lean
structure DyadicBandAnalyticEstimate
    (x K : Nat) (increment : Nat -> Q) (error : R) : Prop where
  increment_nonneg :
    forall k in Finset.range (K + 1), 0 <= increment k
  total_le_one_add_error :
    ((Finset.sum (Finset.range (K + 1)) increment : Q) : R) <=
      1 + error
```

Lean 実装では `Nat`, `Q`, `R` はそれぞれ `ℕ`, `ℚ`, `ℝ` である。

`steps` と `threshold` は構造体に持たせない。

```text
steps     = Finset.range (K + 1)
threshold = fun k : Nat => x * 2^k
```

これらは `x`, `K` から決まる derived data だからである。

## 3. 013C: Lean contract and bridge

DKMK-013C では `SourceMassTruncation.lean` に次を追加した。

```lean
DyadicBandAnalyticEstimate
DyadicBandAnalyticEstimate.toTruncationEnvelopeEstimate
```

bridge theorem は `TruncationEnvelopeEstimate.dyadicRange` への薄い wrapper である。

```text
DyadicBandAnalyticEstimate
  -> TruncationEnvelopeEstimate.dyadicRange
  -> TruncationEnvelopeEstimate
```

ここでは route theorem を増やしていない。

## 4. 013D: usage summary

DKMK-013D では、contract の使用経路を docs 上で固定した。

```text
H : DyadicBandAnalyticEstimate x K increment error
  -> H.toTruncationEnvelopeEstimate
  -> TruncationEnvelopeEstimate
  -> TruncationEnvelopeEstimate.finiteStepTail_weightedHitMass_le_one_add_error
  -> weightedHitMass <= 1 + error
```

役割分担は次である。

```text
DyadicBandAnalyticEstimate:
  analytic-side target

TruncationEnvelopeEstimate:
  route-side input

toTruncationEnvelopeEstimate:
  bridge from analytic target to route input
```

## 5. 013E/F/G: constantBand provider

DKMK-013E では、`DyadicBandAnalyticEstimate` の concrete provider 候補を整理した。

候補は次である。

```text
externally supplied dyadic estimate
constant band envelope
decreasing dyadic envelope
dyadic tail upper envelope
logarithmic refinement
```

最初の nontrivial provider として constant band envelope を選んだ。

DKMK-013F では、その exact shape を docs 上で固定した。

```lean
DyadicBandAnalyticEstimate.constantBand
```

DKMK-013G では Lean 上に実装した。

```text
increment k = c
hc : 0 <= c
Finset.sum-form hbound
  -> DyadicBandAnalyticEstimate x K (fun _ => c) error
```

この theorem では finite-sum simplification は行わず、`Finset.sum` 形の
bound を外部から受け取る。

## 6. 013H/I: natCastMulBound provider

DKMK-013H では、constant band provider の caller-facing bound 形を固定した。

```lean
DyadicBandAnalyticEstimate.constantBand_of_natCastMulBound
```

入力 bound は次である。

```text
((((K + 1 : Nat) : Q) * c : Q) : R) <= 1 + error
```

DKMK-013I では Lean 上に実装した。

finite-sum simplification は次で discharge できた。

```text
Finset.sum_const
Finset.card_range
nsmul_eq_mul
```

これにより、constant band provider は次の二つの形で使える。

```text
Finset.sum-form hbound
Nat-cast-multiply hbound
```

## 7. 到達点

DKMK-013 は、abstract dyadic analytic estimate contract と最初の concrete
provider を固定した章として閉じる。

この章で追加した Lean surface は次である。

```text
DyadicBandAnalyticEstimate
DyadicBandAnalyticEstimate.toTruncationEnvelopeEstimate
DyadicBandAnalyticEstimate.constantBand
DyadicBandAnalyticEstimate.constantBand_of_natCastMulBound
```

この章では次を追加していない。

```text
route changes
new route theorem
dyadic tail estimates
Mertens theorem
big-O statement
logarithmic threshold provider
```

## 8. 次の山

次の章は、自然には次である。

```text
DKMK-014:
  decreasing / dyadic tail provider design
```

主題は、constant band から `k`-dependent band へ進むことである。

次章ではまず、まだ Mertens や big-O へ直行せず、次を設計する。

```text
decreasing band provider shape
dyadic tail upper envelope contract
finite total estimate の外部化
which monotonicity or decay assumptions are actually consumed
```

この順序なら、DKMK-013 で作った contract surface を保ったまま、
analytic layer を段階的に拡張できる。
