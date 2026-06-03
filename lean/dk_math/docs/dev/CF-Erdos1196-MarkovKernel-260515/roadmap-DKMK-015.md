# roadmap: DKMK-015

## 0. Position

DKMK-014 closed the `k`-dependent majorant provider chapter.

The current provider chain is:

```text
increment
  -> majorant
  -> pointwise geometric majorant
  -> caller-facing base * sum ratio^k bound
  -> DyadicBandAnalyticEstimate
  -> existing route
```

The latest Lean provider is:

```lean
DyadicBandAnalyticEstimate.ofPointwiseGeometricMajorant_of_geomSumBound
```

It consumes:

```text
base * sum (ratio ^ k) <= 1 + error
```

DKMK-015 starts the next layer:

```text
finite geometric-sum / tail-bound theorem design
```

## 1. Goal

DKMK-015 should decide how to prove or package the bound:

```text
base * sum (ratio ^ k) <= 1 + error
```

in a way that can feed:

```lean
DyadicBandAnalyticEstimate.ofPointwiseGeometricMajorant_of_geomSumBound
```

The first goal is still theorem-shape design, not a full analytic asymptotic
estimate.

## 2. Main Questions

The chapter should answer:

```text
finite geometric sum identity をどこまで証明するか
ratio != 1 をどの theorem が消費するか
0 <= ratio, ratio < 1 をどの theorem が消費するか
tail-bound を closed form と分けるか
base を掛けた bound をどこで扱うか
```

The route layer should remain unchanged.

## 3. Candidate Theorem Layers

### Candidate 1: finite geometric-sum identity

This candidate proves the algebraic identity:

```text
sum_{k=0}^{K} ratio^k
  = (1 - ratio^(K + 1)) / (1 - ratio)
```

or an equivalent rearranged form.

Possible assumptions:

```text
ratio != 1
```

Status:

```text
algebraic layer; introduces division and ratio != 1
```

### Candidate 2: finite geometric-sum upper bound

This candidate avoids exposing equality and proves an upper bound directly.

Possible target:

```text
sum ratio^k <= 1 / (1 - ratio)
```

Possible assumptions:

```text
0 <= ratio
ratio < 1
```

Status:

```text
order layer; consumes positivity and ratio < 1
```

### Candidate 3: base-scaled bound

This candidate turns a bound on `sum ratio^k` into:

```text
base * sum ratio^k <= 1 + error
```

Possible assumptions:

```text
0 <= base
sum ratio^k <= B
base * B <= 1 + error
```

Status:

```text
scaling layer; consumes base nonnegativity if using order multiplication
```

### Candidate 4: direct caller-facing theorem

This candidate packages the whole path:

```text
ratio side conditions
tail-bound assumptions
base-scaled bound
pointwise geometric majorization
  -> DyadicBandAnalyticEstimate
```

Status:

```text
too broad for first Lean target; useful as later composition theorem
```

## 4. Design Principle

Do not introduce side conditions before a theorem consumes them.

In particular:

```text
ratio != 1:
  belongs to closed-form identity or division theorem

0 <= ratio, ratio < 1:
  belong to upper-bound or tail-bound theorem

0 <= base:
  belongs to base-scaled order theorem
```

The existing provider:

```lean
DyadicBandAnalyticEstimate.ofPointwiseGeometricMajorant_of_geomSumBound
```

does not consume any of these side conditions.

## 5. Proposed Order

DKMK-015 should proceed in small layers.

```text
DKMK-015B:
  finite geometric-sum identity exact shape

DKMK-015C:
  optional Lean identity theorem, if the shape is light enough

DKMK-015D:
  finite geometric-sum upper-bound exact shape

DKMK-015E:
  base-scaled bound exact shape

DKMK-015F:
  connection back to geomSumBound provider
```

This sequence keeps algebra, order, scaling, and provider connection separate.

## 6. Non-goals

DKMK-015A should not:

- change `DyadicBandAnalyticEstimate`;
- change the route theorem;
- introduce Mertens or big-O;
- introduce logarithmic thresholds;
- introduce real-to-Nat rounding;
- prove a full dyadic tail estimate;
- add a broad all-in-one theorem.

## 7. Verification Plan

For docs-only steps:

```text
git diff --check
long-line check on changed docs files
```

For Lean steps:

```text
lake build DkMath.NumberTheory.PrimitiveSet.SourceMassTruncation
lake build DkMath.NumberTheory.PrimitiveSet
```

## 8. Next Step

The next concrete step should be DKMK-015B:

```text
finite geometric-sum identity exact shape review
```

It should decide whether the first closed-form theorem is an equality theorem,
a denominator-cleared identity, or an upper-bound theorem that avoids equality.
