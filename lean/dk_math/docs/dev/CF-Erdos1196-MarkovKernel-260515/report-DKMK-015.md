# DKMK-015: report

DKMK-015 は、DKMK-014 で固定した pointwise geometric majorant provider に、
finite geometric-sum / geometric-budget route を接続する章である。

DKMK-014 の終点は次だった。

```text
increment k <= base * ratio^k
base * sum ratio^k <= 1 + error
  -> DyadicBandAnalyticEstimate.ofPointwiseGeometricMajorant_of_geomSumBound
  -> DyadicBandAnalyticEstimate
  -> existing finite-step route
```

DKMK-015 では、caller が finite sum を直接評価しなくてもよいように、
`base * (1 / (1 - ratio)) <= 1 + error` から provider へ入る
standard route を作った。

## 1. 主目的

DKMK-015 の主目的は、closed-form division equality、Mertens theorem、
big-O formalization、logarithmic threshold provider、
real-to-Nat rounding を証明することではない。

目的は、finite geometric-sum estimate を Lean 上で薄く積み、
既存の rational dyadic provider へ接続することである。

## 2. 015A/B: roadmap と identity shape

DKMK-015A では `roadmap-DKMK-015.md` を追加し、
DKMK-014J の caller-facing bound へ向かう geometric-sum route を整理した。

DKMK-015B では、最初の algebraic identity として division form ではなく、
denominator-cleared identity を選んだ。

```lean
geomSum_range_mul_one_sub
```

形は次である。

```text
(1 - ratio) * sum ratio^k = 1 - ratio^(K + 1)
```

`ratio != 1` は division form に必要な仮定なので、この段階では導入しない。

## 3. 015C: denominator-cleared identity

DKMK-015C では、Lean 上に次を追加した。

```lean
geomSum_range_mul_one_sub
```

実装は mathlib の既存 theorem を薄く再公開する形で閉じた。

```lean
exact mul_neg_geom_sum ratio (K + 1)
```

この theorem は side condition を持たない algebraic layer である。

## 4. 015D/E: finite geometric-sum upper bound

DKMK-015D では、division-form equality ではなく、下流が必要とする
upper-bound theorem を先に固定した。

DKMK-015E では、Lean 上に次を追加した。

```lean
geomSum_range_le_one_div_one_sub
```

形は次である。

```text
0 <= ratio
ratio < 1
  -> sum ratio^k <= 1 / (1 - ratio)
```

証明は DKMK-015C の denominator-cleared identity から
`(1 - ratio) * sum ratio^k <= 1` を作り、`ratio < 1` から得る
`0 < 1 - ratio` と `le_div_iff₀` で上界へ変形する。

explicit `ratio != 1` は追加していない。

## 5. 015F: base-scaled provider-facing bound

DKMK-015F では、Lean 上に次を追加した。

```lean
base_mul_geomSum_range_le_of_base_mul_one_div_le
```

形は次である。

```text
0 <= base
0 <= ratio
ratio < 1
base * (1 / (1 - ratio)) <= 1 + error
  -> base * sum ratio^k <= 1 + error
```

証明は DKMK-015E の upper bound に
`mul_le_mul_of_nonneg_left` を当て、caller-supplied budget へ
`le_trans` するだけの wrapper である。

## 6. 015G/H: dyadic provider connection

DKMK-015G では、Real 側 geometric-budget theorem と rational-valued
dyadic provider の型境界を docs 上で固定した。

接続 theorem 名は次にした。

```lean
DyadicBandAnalyticEstimate
  .ofPointwiseGeometricMajorant_of_baseGeomBudget
```

DKMK-015H では、Lean 上にこの theorem を追加した。

この theorem は、Real 側の budget

```text
(base : Real) * (1 / (1 - (ratio : Real))) <= 1 + error
```

から、既存の rational-valued provider

```lean
DyadicBandAnalyticEstimate.ofPointwiseGeometricMajorant_of_geomSumBound
```

へ接続する。

主要な型境界は次である。

```text
((base * sum (fun k => ratio ^ k) : Rat) : Real)
=
(base : Real) * sum (fun k => (ratio : Real) ^ k)
```

この cast identity は局所補題 `hcast` として `simp` で閉じた。

## 7. 到達点

DKMK-015 で追加した Lean surface は次である。

```text
geomSum_range_mul_one_sub
geomSum_range_le_one_div_one_sub
base_mul_geomSum_range_le_of_base_mul_one_div_le
DyadicBandAnalyticEstimate.ofPointwiseGeometricMajorant_of_baseGeomBudget
```

これで caller path は次になった。

```text
hinc_nonneg
hgeom : increment k <= base * ratio^k
hbase : 0 <= (base : Real)
hr0   : 0 <= (ratio : Real)
hr1   : (ratio : Real) < 1
hbudget : (base : Real) * (1 / (1 - (ratio : Real))) <= 1 + error
  -> DyadicBandAnalyticEstimate.ofPointwiseGeometricMajorant_of_baseGeomBudget
  -> DyadicBandAnalyticEstimate
  -> existing finite-step route
```

The chapter closes the route:

```text
geometric budget
  -> finite geometric-sum bound
  -> base-scaled finite-sum bound
  -> dyadic source-mass provider
```

## 8. Non-goals

DKMK-015 では次を追加していない。

```text
division-form finite geometric-sum equality
explicit ratio != 1 assumption
new provider structure
duplicate low-level provider
route theorem changes
Mertens theorem
big-O statement
logarithmic threshold provider
real-to-Nat rounding
```

## 9. 次の山

次の章では、次を整理するのが自然である。

```text
Where does hbudget come from?
```

すなわち、

```text
(base : Real) * (1 / (1 - (ratio : Real))) <= 1 + error
```

を上位 route がどのように供給するかを設計する。

候補は、`base` と `ratio` 自体の設計、log-capacity / dyadic band の
具体的な analytic budget、またはそのための abstract budget provider である。

Mertens / big-O / logarithmic threshold / real-to-Nat rounding は、
この次章でもすぐに混ぜるのではなく、まず abstract budget surface として
切り分けるのが安全である。
