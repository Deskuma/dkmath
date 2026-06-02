# roadmap: DKMK-012

## 0. Position

DKMK-011 closed the externally supplied finite-step estimate interface.

The current boundary is:

```text
analytic layer:
  proves TruncationEnvelopeEstimate

route layer:
  consumes TruncationEnvelopeEstimate
```

DKMK-012 starts the next design layer: concrete band providers that can build
`TruncationEnvelopeEstimate`.

The recommended first direction is provider design, not a Mertens theorem.

## 1. Goal

DKMK-012 should decide how dyadic or logarithmic band data can be turned into:

```lean
TruncationEnvelopeEstimate steps threshold increment error
```

without changing the route theorem.

The route theorem remains:

```lean
TruncationEnvelopeEstimate
  .finiteStepTail_weightedHitMass_le_one_add_error
```

DKMK-012 is therefore about producing the input, not changing the consumer.

## 2. Design Questions

### steps

The band index should be finite.

Candidate shapes:

```text
Finset.range (K + 1)
Finset.Icc 0 K
externally supplied finite index set
```

The conservative first Lean target is probably `Finset.range (K + 1)`, since it
keeps the index type as `Nat` and avoids extra finite interval machinery.

### threshold

`threshold : Nat -> Nat` must turn the band index into a natural activation
point for `finiteStepTailNatMassSpace`.

Dyadic candidate:

```text
threshold k = x * 2^k
```

Logarithmic candidate:

```text
threshold k = floor or ceil of x * exp(k * step)
```

The logarithmic candidate is closer to the final asymptotic shape, but it
requires real-to-natural rounding and exponential/log infrastructure.

DKMK-012 should start with the dyadic provider design and keep logarithmic
bands as a later specialization.

### increment

`increment : Nat -> Q` should remain externally supplied at first.

Reason:

```text
increment carries the analytic band estimate.
```

If DKMK-012 tries to compute increments from logs immediately, it will mix
provider plumbing with analytic estimates.  The first provider should only
package a finite band family whose increments are already supplied and proven
nonnegative.

### error

`error : R` remains external.

The provider should assume the analytic total estimate:

```text
sum increment <= 1 + error
```

This is exactly the `FiniteStepTailAnalyticBound` field inside
`TruncationEnvelopeEstimate`.

## 3. Candidate Providers

### DKMK-012A: roadmap and scope

This file is DKMK-012A.

It fixes the rule:

```text
provider design first
analytic theorem later
```

### DKMK-012B: dyadic provider docs

Add a docs inventory for a dyadic band provider.

Proposed data:

```text
x         : Nat
K         : Nat
increment : Nat -> Q
error     : R
```

Derived data:

```text
steps     = Finset.range (K + 1)
threshold = fun k => x * 2^k
```

Required hypotheses:

```text
forall k in steps, 0 <= increment k
((sum k in steps, increment k : Q) : R) <= 1 + error
```

This is enough to build:

```text
TruncationEnvelopeEstimate steps threshold increment error
```

### DKMK-012C: Lean dyadic provider

If DKMK-012B is accepted, add a small Lean provider:

```lean
TruncationEnvelopeEstimate.dyadic
```

Expected shape:

```lean
theorem TruncationEnvelopeEstimate.dyadic
    (x K : Nat) (increment : Nat -> Q)
    (hinc : forall k in Finset.range (K + 1), 0 <= increment k)
    {error : R}
    (hbound :
      ((Finset.sum (Finset.range (K + 1)) increment : Q) : R) <=
        1 + error) :
    TruncationEnvelopeEstimate
      (Finset.range (K + 1))
      (fun k => x * 2^k)
      increment
      error
```

This theorem should be as thin as `singleWindow`.

### DKMK-012D: dyadic usage summary

Document the flow:

```text
dyadic data
  -> TruncationEnvelopeEstimate.dyadic
  -> TruncationEnvelopeEstimate route theorem
  -> weightedHitMass <= 1 + error
```

No route theorem specialization is required unless usage becomes unreadable.

### DKMK-012E: logarithmic provider design

Only after dyadic provider design is stable, decide whether to introduce
logarithmic bands.

Open questions:

- how to round real thresholds into `Nat`;
- whether thresholds should use floor, ceiling, or an external Nat function;
- whether increments should remain externally supplied;
- how much real-log infrastructure is worth importing.

The conservative choice is to make logarithmic thresholds externally supplied
first, then specialize later.

### DKMK-012F: report

Close the chapter with a report explaining:

- dyadic provider data;
- what remains external analytic input;
- why route layer remains unchanged;
- whether logarithmic provider is deferred.

## 4. Non-goals

DKMK-012 should not:

- prove a Mertens theorem;
- prove the final `1 + O(1 / log x)` estimate;
- formalize big-O;
- change `TruncationEnvelopeEstimate`;
- change the DKMK-009/010/011 route theorem;
- introduce real logarithmic rounding before the dyadic design is stable.

## 5. Verification Plan

For docs-only steps:

```text
git diff --check
long-line check on changed docs files
```

For the first Lean provider:

```text
lake build DkMath.NumberTheory.PrimitiveSet.SourceMassTruncation
lake build DkMath.NumberTheory.PrimitiveSet
```

## 6. Next Step

The next concrete step should be DKMK-012B:

```text
dyadic provider docs
```

It should confirm the exact data and theorem shape before Lean implementation.
