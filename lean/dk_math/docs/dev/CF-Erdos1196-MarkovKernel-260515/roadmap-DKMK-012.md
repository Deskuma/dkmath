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
TruncationEnvelopeEstimate.dyadicRange
```

Expected shape:

```lean
theorem TruncationEnvelopeEstimate.dyadicRange
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
  -> TruncationEnvelopeEstimate.dyadicRange
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

## 7. DKMK-012B Dyadic Provider Shape

DKMK-012B fixes the first concrete band-provider shape.

The provider is dyadic and range-indexed:

```text
steps = Finset.range (K + 1)
```

The data are:

```text
x         : Nat
K         : Nat
increment : Nat -> Q
error     : R
```

The derived source-envelope threshold is:

```text
threshold k = x * 2^k
```

The analytic information remains external:

```text
hinc:
  forall k in Finset.range (K + 1), 0 <= increment k

hbound:
  ((Finset.sum (Finset.range (K + 1)) increment : Q) : R) <=
    1 + error
```

These are exactly the two fields needed by `TruncationEnvelopeEstimate`:

```text
hinc:
  increment_nonneg

hbound:
  FiniteStepTailAnalyticBound.total_le_one_add_error
```

### Preferred theorem name

Use:

```lean
TruncationEnvelopeEstimate.dyadicRange
```

instead of `dyadic`.

Reason:

```text
dyadicRange names both choices:
  dyadic thresholds
  range-indexed finite steps
```

### Expected Lean shape

```lean
theorem TruncationEnvelopeEstimate.dyadicRange
    (x K : Nat) (increment : Nat -> Q)
    (hinc : forall k in Finset.range (K + 1), 0 <= increment k)
    {error : R}
    (hbound :
      ((Finset.sum (Finset.range (K + 1)) increment : Q) : R) <=
        1 + error) :
    TruncationEnvelopeEstimate
      (Finset.range (K + 1))
      (fun k : Nat => x * 2^k)
      increment
      error
```

The proof should be a packaging proof only:

```text
increment_nonneg := hinc
analytic_bound  := FiniteStepTailAnalyticBound from hbound
```

No route theorem should change.

### Why not logarithmic yet

The dyadic provider avoids:

- real-to-natural rounding;
- `Real.exp` / `Real.log` imports;
- floor/ceiling choices;
- proving monotonicity or comparison lemmas for rounded thresholds.

The logarithmic provider should wait until this dyadic provider is stable.

## 8. DKMK-012B Decision

DKMK-012C should add only:

```lean
TruncationEnvelopeEstimate.dyadicRange
```

It should not add:

- a dyadic-specific route theorem;
- a logarithmic provider;
- any Mertens or big-O statement;
- computed increments from log formulas.

The route remains:

```text
dyadicRange
  -> TruncationEnvelopeEstimate
  -> existing DKMK-011 route theorem
  -> weightedHitMass <= 1 + error
```

## 9. DKMK-012C Lean Provider

DKMK-012C adds the Lean theorem fixed by DKMK-012B:

```lean
TruncationEnvelopeEstimate.dyadicRange
```

The theorem is a packaging provider only.

It fixes:

```text
steps     = Finset.range (K + 1)
threshold = fun k : Nat => x * 2^k
```

and consumes externally supplied analytic data:

```text
hinc:
  forall k in Finset.range (K + 1), 0 <= increment k

hbound:
  ((Finset.sum (Finset.range (K + 1)) increment : Q) : R) <=
    1 + error
```

The proof only fills:

```text
increment_nonneg := hinc
analytic_bound.total_le_one_add_error := hbound
```

No route theorem, logarithmic provider, Mertens statement, big-O statement, or
computed increment formula is added.

The usage path remains:

```text
dyadicRange
  -> TruncationEnvelopeEstimate
  -> TruncationEnvelopeEstimate.finiteStepTail_weightedHitMass_le_one_add_error
```

## 10. DKMK-012D Usage Summary

DKMK-012D records how the dyadic provider is used.

No new Lean route theorem is needed for this step.

### Input data

The dyadic data are:

```text
x         : Nat
K         : Nat
increment : Nat -> Q
error     : R
```

They determine:

```text
steps     = Finset.range (K + 1)
threshold = fun k : Nat => x * 2^k
```

### Proof inputs

The provider needs exactly two proof inputs:

```text
hinc:
  forall k in Finset.range (K + 1), 0 <= increment k

hbound:
  ((Finset.sum (Finset.range (K + 1)) increment : Q) : R) <=
    1 + error
```

Their roles are:

```text
hinc:
  finite-step source envelope nonnegativity

hbound:
  analytic total estimate
```

### Provider

The data and proof inputs produce:

```lean
TruncationEnvelopeEstimate.dyadicRange x K increment hinc hbound
```

with target:

```lean
TruncationEnvelopeEstimate
  (Finset.range (K + 1))
  (fun k : Nat => x * 2^k)
  increment
  error
```

### Route

The resulting `TruncationEnvelopeEstimate` is consumed by the existing route:

```lean
TruncationEnvelopeEstimate.finiteStepTail_weightedHitMass_le_one_add_error
```

The combined flow is:

```text
dyadic data
  -> hinc and hbound
  -> TruncationEnvelopeEstimate.dyadicRange
  -> TruncationEnvelopeEstimate
  -> TruncationEnvelopeEstimate.finiteStepTail_weightedHitMass_le_one_add_error
  -> weightedHitMass <= 1 + error
```

### Decision

DKMK-012D is documentation only.

It should not add:

- a dyadic-specific route theorem;
- a logarithmic provider;
- a Mertens or big-O statement;
- a computed formula for `increment`.

The next technical question is what analytic estimate should supply
`increment` and `hbound`.

## 11. DKMK-012E Increment / hbound Design

DKMK-012E records the analytic meaning of the two external inputs used by
`dyadicRange`.

This is still a design step.  It does not define a computed formula for
`increment`.

### Meaning of increment

For dyadic data:

```text
steps     = Finset.range (K + 1)
threshold = fun k : Nat => x * 2^k
```

the value:

```text
increment k
```

should be read as an analytic upper envelope for the contribution of the
`k`-th dyadic band.

It is not yet a formula involving logs, Mertens estimates, or asymptotic
notation.  At this stage it is an externally supplied rational band weight.

The nonnegativity hypothesis:

```text
hinc:
  forall k in Finset.range (K + 1), 0 <= increment k
```

keeps the finite-step source mass construction valid.

### Meaning of hbound

The hypothesis:

```text
hbound:
  ((Finset.sum (Finset.range (K + 1)) increment : Q) : R) <=
    1 + error
```

is the analytic total estimate.

It says that the finite collection of dyadic band envelopes has total mass at
most `1 + error`.

This is the only analytic inequality consumed by `TruncationEnvelopeEstimate`.

### Candidate sources

Possible future sources for `increment` and `hbound` are:

- externally supplied band weights;
- a dyadic tail upper envelope;
- a later logarithmic refinement;
- a concrete estimate derived from number-theoretic input.

These candidates should stay separate from the route theorem.

### Non-goals

DKMK-012E should not add:

- a formula for `increment k`;
- a proof of a Mertens estimate;
- a big-O statement;
- a logarithmic threshold provider;
- a dyadic-specific hitting route theorem.

### Next question

The next step after this design note is to decide whether DKMK-012 closes with
a report, or whether it should add a first toy analytic provider for
`increment` and `hbound`.
