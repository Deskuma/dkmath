# roadmap: DKMK-014

## 0. Position

DKMK-013 closed the abstract dyadic analytic estimate contract chapter.

The current analytic-to-route flow is:

```text
DyadicBandAnalyticEstimate
  -> DyadicBandAnalyticEstimate.toTruncationEnvelopeEstimate
  -> TruncationEnvelopeEstimate
  -> existing DKMK-011 route theorem
  -> weightedHitMass <= 1 + error
```

DKMK-013 also added the first constant-band providers:

```text
DyadicBandAnalyticEstimate.constantBand
DyadicBandAnalyticEstimate.constantBand_of_natCastMulBound
```

DKMK-014 starts the next analytic-provider design layer:

```text
k-dependent decreasing / dyadic tail provider design
```

## 1. Goal

DKMK-014 should decide how to produce:

```lean
DyadicBandAnalyticEstimate x K increment error
```

when `increment` depends on the band index `k`.

The first goal is still a theorem-facing interface, not a Mertens theorem or a
final asymptotic estimate.

## 2. Main Questions

The chapter should answer:

```text
increment k をどう設計するか
非負性をどう出すか
有限 total estimate をどう外部化するか
monotonicity / decay assumptions をどこまで持たせるか
```

The route layer should remain unchanged.

## 3. Candidate Provider Shapes

### Candidate 1: externally supplied k-dependent estimate

This is the direct analogue of the current contract fields.

Data:

```text
x         : Nat
K         : Nat
increment : Nat -> Q
error     : R
```

Proof input:

```text
hinc:
  forall k in Finset.range (K + 1), 0 <= increment k

hbound:
  ((Finset.sum (Finset.range (K + 1)) increment : Q) : R) <=
    1 + error
```

Target:

```lean
DyadicBandAnalyticEstimate x K increment error
```

Status:

```text
essentially constructor-level; useful as API baseline
```

### Candidate 2: decreasing band provider

This candidate adds a decreasing or monotone condition.

Possible data:

```text
x         : Nat
K         : Nat
increment : Nat -> Q
error     : R
```

Possible assumptions:

```text
nonnegativity:
  forall k in Finset.range (K + 1), 0 <= increment k

monotonicity:
  for relevant k, increment (k + 1) <= increment k

total bound:
  finite sum <= 1 + error
```

Status:

```text
design candidate; monotonicity should be included only if consumed
```

The key question is whether monotonicity helps produce `hinc` or `hbound`.
If it is only descriptive, it should not be a field yet.

### Candidate 3: majorant envelope provider

This candidate separates the actual increment from an upper envelope.

Possible data:

```text
increment : Nat -> Q
majorant  : Nat -> Q
error     : R
```

Possible assumptions:

```text
0 <= increment k
increment k <= majorant k
sum majorant <= 1 + error
```

Target:

```text
sum increment <= 1 + error
```

Status:

```text
promising for future dyadic tail estimates, but may need sum comparison lemmas
```

### Candidate 4: dyadic tail upper envelope

This is the main analytic direction.

The provider should eventually express:

```text
each dyadic band contribution is bounded by increment k
sum over k <= 1 + error
```

Status:

```text
main DKMK-014 direction, but not first Lean target
```

### Candidate 5: logarithmic refinement

This remains deferred.

Reason:

```text
logarithmic thresholds require real-to-Nat rounding,
Real.log / Real.exp infrastructure,
and additional comparison lemmas.
```

## 4. Design Principle

Do not add assumptions just because they are mathematically natural.

Only add a field if a later theorem consumes it.

In particular:

```text
monotonicity
decay
majorization
tail comparison
```

should remain outside the core contract until they produce either:

```text
increment_nonneg
total_le_one_add_error
```

or a bridge theorem into `DyadicBandAnalyticEstimate`.

## 5. Non-goals

DKMK-014A should not:

- change `DyadicBandAnalyticEstimate`;
- change `TruncationEnvelopeEstimate`;
- add a route theorem;
- prove a Mertens theorem;
- introduce big-O notation;
- define logarithmic thresholds;
- add real-to-Nat rounding.

## 6. Verification Plan

For docs-only steps:

```text
git diff --check
long-line check on changed docs files
```

For Lean provider steps:

```text
lake build DkMath.NumberTheory.PrimitiveSet.SourceMassTruncation
lake build DkMath.NumberTheory.PrimitiveSet
```

## 7. Next Step

The next concrete step should be DKMK-014B:

```text
decreasing / majorant provider shape review
```

It should decide whether the first non-constant provider is:

- a decreasing-band provider;
- a majorant-envelope provider;
- or another externally supplied k-dependent estimate provider.

The decision should focus on which assumptions are actually consumed to prove
`DyadicBandAnalyticEstimate`.
