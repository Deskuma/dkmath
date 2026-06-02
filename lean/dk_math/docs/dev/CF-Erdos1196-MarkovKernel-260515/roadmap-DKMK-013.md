# roadmap: DKMK-013

## 0. Position

DKMK-012 closed the dyadic provider plumbing.

The current route is:

```text
dyadic range data
  -> TruncationEnvelopeEstimate.dyadicRange
  -> TruncationEnvelopeEstimate
  -> existing DKMK-011 route theorem
  -> weightedHitMass <= 1 + error
```

DKMK-013 starts the analytic-input layer for dyadic bands.

The new question is not how to consume `TruncationEnvelopeEstimate`.
That is already fixed.

The new question is:

```text
increment k をどう選ぶか
hbound をどう証明するか
```

## 1. Goal

DKMK-013 should design an abstract dyadic analytic estimate contract that can
feed `TruncationEnvelopeEstimate.dyadicRange`.

The intended flow is:

```text
dyadic analytic estimate contract
  -> increment nonnegativity
  -> total estimate
  -> TruncationEnvelopeEstimate.dyadicRange
```

The first goal is a theorem-facing interface, not a final analytic theorem.

## 2. Boundary

DKMK-013 should remain in the analytic-input layer.

It should not change:

- `TruncationEnvelopeEstimate`;
- `TruncationEnvelopeEstimate.dyadicRange`;
- `TruncationEnvelopeEstimate.finiteStepTail_weightedHitMass_le_one_add_error`;
- the DKMK-009/010/011/012 route theorems.

The route layer should continue to consume the same
`TruncationEnvelopeEstimate` value.

## 3. Proposed Contract Shape

The contract should likely live near `TruncationEnvelopeEstimate`, but DKMK-013A
does not yet choose the Lean file or exact theorem names.

Candidate data:

```text
x         : Nat
K         : Nat
increment : Nat -> Q
error     : R
```

Candidate structure:

```lean
structure DyadicBandAnalyticEstimate
    (x K : Nat) (increment : Nat -> Q) (error : R) : Prop where
  increment_nonneg :
    forall k in Finset.range (K + 1), 0 <= increment k
  total_le_one_add_error :
    ((Finset.sum (Finset.range (K + 1)) increment : Q) : R) <=
      1 + error
```

This is intentionally close to the inputs of
`TruncationEnvelopeEstimate.dyadicRange`.

The expected bridge would be:

```lean
theorem DyadicBandAnalyticEstimate.toTruncationEnvelopeEstimate
    (H : DyadicBandAnalyticEstimate x K increment error) :
    TruncationEnvelopeEstimate
      (Finset.range (K + 1))
      (fun k : Nat => x * 2^k)
      increment
      error
```

The bridge should be a thin wrapper around:

```lean
TruncationEnvelopeEstimate.dyadicRange
```

## 4. Why Another Contract?

`TruncationEnvelopeEstimate.dyadicRange` is a provider-layer theorem.

It knows how to package:

```text
hinc
hbound
```

into `TruncationEnvelopeEstimate`.

It does not explain where those analytic facts come from.

`DyadicBandAnalyticEstimate` would name the analytic-side promise:

```text
for this dyadic band family,
the band weights are nonnegative
and their total is <= 1 + error
```

This gives future analytic theorems a stable target without changing the route
layer.

## 5. Candidate Sources

Future providers for the contract may include:

- externally supplied band weights;
- a dyadic tail upper envelope;
- a logarithmic refinement of dyadic bands;
- a concrete number-theoretic estimate.

DKMK-013 should start with the abstract contract, then decide which concrete
provider is worth formalizing first.

## 6. Non-goals

DKMK-013A should not:

- prove a Mertens theorem;
- introduce big-O notation;
- define a logarithmic threshold provider;
- compute `increment k` from a log formula;
- add a dyadic-specific hitting route theorem.

Those belong after the analytic contract surface is stable.

## 7. Verification Plan

For docs-only steps:

```text
git diff --check
long-line check on changed docs files
```

For the first Lean contract:

```text
lake build DkMath.NumberTheory.PrimitiveSet.SourceMassTruncation
lake build DkMath.NumberTheory.PrimitiveSet
```

## 8. Next Step

The next concrete step should be DKMK-013B:

```text
DyadicBandAnalyticEstimate exact shape review
```

It should decide:

- whether the contract name should be `DyadicBandAnalyticEstimate`;
- whether it belongs in `SourceMassTruncation.lean`;
- whether the bridge theorem should be named
  `DyadicBandAnalyticEstimate.toTruncationEnvelopeEstimate`;
- whether the contract should store only `hinc` and `hbound`, or also derived
  data such as `steps` and `threshold`.

## 9. DKMK-013B Exact Shape Decision

DKMK-013B fixes the first Lean shape for the abstract dyadic analytic estimate
contract.

### Contract name

Use:

```lean
DyadicBandAnalyticEstimate
```

Reason:

```text
DyadicBand:
  the estimate is attached to the dyadic band family

AnalyticEstimate:
  the contract lives in the analytic-input layer, not the route layer
```

### Placement

Place the first version in:

```text
SourceMassTruncation.lean
```

Reason:

```text
The contract is still small and sits next to TruncationEnvelopeEstimate.
```

If later DKMK-013 work adds logarithmic refinements or several
number-theoretic estimate providers, a separate file can be introduced then.

### Fields

The structure should store only the two analytic facts needed by
`TruncationEnvelopeEstimate.dyadicRange`:

```lean
structure DyadicBandAnalyticEstimate
    (x K : Nat) (increment : Nat -> Q) (error : R) : Prop where
  increment_nonneg :
    forall k in Finset.range (K + 1), 0 <= increment k
  total_le_one_add_error :
    ((Finset.sum (Finset.range (K + 1)) increment : Q) : R) <=
      1 + error
```

Do not store:

```text
steps
threshold
```

Reason:

```text
steps     = Finset.range (K + 1)
threshold = fun k : Nat => x * 2^k
```

are derived from `x` and `K` in the dyadic range provider.

### Bridge theorem

Use:

```lean
DyadicBandAnalyticEstimate.toTruncationEnvelopeEstimate
```

Expected Lean shape:

```lean
theorem DyadicBandAnalyticEstimate.toTruncationEnvelopeEstimate
    {x K : Nat} {increment : Nat -> Q} {error : R}
    (H : DyadicBandAnalyticEstimate x K increment error) :
    TruncationEnvelopeEstimate
      (Finset.range (K + 1))
      (fun k : Nat => x * 2^k)
      increment
      error
```

The proof should be a wrapper around:

```lean
TruncationEnvelopeEstimate.dyadicRange
```

using:

```text
H.increment_nonneg
H.total_le_one_add_error
```

### Non-goals

DKMK-013B does not add Lean code.

DKMK-013C should add only:

```text
DyadicBandAnalyticEstimate
DyadicBandAnalyticEstimate.toTruncationEnvelopeEstimate
```

It should not add:

- a computed formula for `increment k`;
- a Mertens theorem;
- a big-O statement;
- a logarithmic threshold provider;
- a dyadic-specific hitting route theorem.
