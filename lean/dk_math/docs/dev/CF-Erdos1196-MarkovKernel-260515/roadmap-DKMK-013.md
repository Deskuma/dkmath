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

## 10. DKMK-013C Lean Contract

DKMK-013C adds the small Lean contract fixed by DKMK-013B:

```lean
DyadicBandAnalyticEstimate
```

The structure stores only:

```text
increment_nonneg
total_le_one_add_error
```

It does not store:

```text
steps
threshold
```

because these are derived by the dyadic range provider:

```text
steps     = Finset.range (K + 1)
threshold = fun k : Nat => x * 2^k
```

DKMK-013C also adds:

```lean
DyadicBandAnalyticEstimate.toTruncationEnvelopeEstimate
```

This theorem is a wrapper around:

```lean
TruncationEnvelopeEstimate.dyadicRange
```

and passes:

```text
H.increment_nonneg
H.total_le_one_add_error
```

No route theorem, computed increment formula, Mertens theorem, big-O
statement, or logarithmic threshold provider is added.

## 11. DKMK-013D Usage Summary

DKMK-013D records how the dyadic analytic contract is used.

No new Lean route theorem is needed for this step.

### Analytic target

Future analytic work should target:

```lean
DyadicBandAnalyticEstimate x K increment error
```

This contract means:

```text
increment_nonneg:
  every dyadic band increment is nonnegative

total_le_one_add_error:
  the total dyadic band increment is <= 1 + error
```

It is the analytic-input layer promise.

### Provider bridge

The contract is converted to the provider-layer input by:

```lean
DyadicBandAnalyticEstimate.toTruncationEnvelopeEstimate
```

The bridge returns:

```lean
TruncationEnvelopeEstimate
  (Finset.range (K + 1))
  (fun k : Nat => x * 2^k)
  increment
  error
```

It is only a wrapper around:

```lean
TruncationEnvelopeEstimate.dyadicRange
```

### Route consumer

The resulting `TruncationEnvelopeEstimate` is consumed by:

```lean
TruncationEnvelopeEstimate.finiteStepTail_weightedHitMass_le_one_add_error
```

The complete flow is:

```text
H : DyadicBandAnalyticEstimate x K increment error
  -> H.toTruncationEnvelopeEstimate
  -> TruncationEnvelopeEstimate
  -> TruncationEnvelopeEstimate.finiteStepTail_weightedHitMass_le_one_add_error
  -> weightedHitMass <= 1 + error
```

### Layer boundary

The roles are:

```text
DyadicBandAnalyticEstimate:
  analytic-side target

TruncationEnvelopeEstimate:
  route-side input

toTruncationEnvelopeEstimate:
  bridge from analytic target to route input
```

DKMK-013D should not add:

- a route theorem;
- a computed formula for `increment k`;
- a Mertens theorem;
- a big-O statement;
- a logarithmic threshold provider.

The next technical question is what concrete provider should prove
`DyadicBandAnalyticEstimate`.

## 12. DKMK-013E Concrete Provider Candidate Inventory

DKMK-013E records candidate producers of:

```lean
DyadicBandAnalyticEstimate x K increment error
```

This is still a design step.  It does not add a Lean provider.

### Candidate 1: externally supplied dyadic estimate

This is the direct constructor shape.

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
already essentially the structure constructor
```

This candidate is useful as a naming / API check, but it does not add analytic
content.

### Candidate 2: constant band envelope

This is the smallest computed-shape provider candidate.

Data:

```text
x     : Nat
K     : Nat
c     : Q
error : R
```

Increment:

```text
increment k = c
```

Required proof input:

```text
hc:
  0 <= c

hbound:
  (((K + 1) : Nat) * c : Q) coerced to R <= 1 + error
```

Target:

```lean
DyadicBandAnalyticEstimate x K (fun _ => c) error
```

Status:

```text
candidate for the first nontrivial Lean provider
```

This may require a small finite-sum calculation for:

```text
Finset.sum (Finset.range (K + 1)) (fun _ => c)
```

### Candidate 3: decreasing dyadic envelope

This candidate keeps the dyadic structure but leaves the analytic values
mostly external.

Data:

```text
x         : Nat
K         : Nat
increment : Nat -> Q
error     : R
```

Additional proof input may include:

```text
nonnegativity of each band
finite total estimate
optional monotonicity or decay condition
```

Status:

```text
useful design target, but not first Lean target
```

The monotonicity or decay condition should not be added unless it is consumed
by a later theorem.

### Candidate 4: dyadic tail upper envelope

This is the natural next analytic direction.

Data may come from:

```text
external dyadic tail theorem
explicit finite sum estimate
number-theoretic upper bound
```

Target:

```text
produce increment_nonneg and total_le_one_add_error
```

Status:

```text
main DKMK-013 analytic direction, but still too large for the next small step
```

### Candidate 5: logarithmic refinement

This is deferred.

Reason:

```text
logarithmic thresholds require real-to-Nat rounding,
Real.log / Real.exp infrastructure,
and additional monotonicity or comparison lemmas.
```

Status:

```text
later chapter or later DKMK-013 branch
```

### Decision

The first Lean provider should likely be one of:

```text
externally supplied dyadic estimate
constant band envelope
```

The externally supplied provider is almost just the constructor, so the more
useful first concrete provider is probably:

```text
constant band envelope
```

DKMK-013F should decide the exact Lean shape for the constant band provider,
including how to state the finite-sum bound without creating avoidable
coercion friction.

## 13. DKMK-013F Constant Band Provider Shape

DKMK-013F fixes the first exact shape for a constant band provider.

This is still a docs-only step.  It does not add Lean code.

### Chosen provider

Use:

```lean
DyadicBandAnalyticEstimate.constantBand
```

The provider should build:

```lean
DyadicBandAnalyticEstimate x K (fun _ : Nat => c) error
```

from a nonnegative constant band weight and an externally stated finite-sum
bound.

### Expected Lean shape

Use the sum-bound external form first:

```lean
theorem DyadicBandAnalyticEstimate.constantBand
    (x K : Nat) (c : Q)
    (hc : 0 <= c)
    {error : R}
    (hbound :
      ((Finset.sum (Finset.range (K + 1)) (fun _ : Nat => c) : Q) : R) <=
        1 + error) :
    DyadicBandAnalyticEstimate x K (fun _ : Nat => c) error
```

The proof should be direct:

```text
increment_nonneg:
  intro k hk
  exact hc

total_le_one_add_error:
  exact hbound
```

### Why not simplify the sum yet

Do not use this as the first theorem statement:

```text
((((K + 1 : Nat) : Q) * c : Q) : R) <= 1 + error
```

Reason:

```text
This adds finite-sum simplification and Nat/Q/R coercion work at the same time
as the first provider theorem.
```

The first provider should test only that:

```text
constant increments
  -> DyadicBandAnalyticEstimate
```

can be packaged cleanly.

### Optional later theorem

After `constantBand` is stable, a later theorem may add the simplified
finite-sum form:

```lean
DyadicBandAnalyticEstimate.constantBand_of_natCastMulBound
```

or another name chosen after checking the actual Lean coercion shape.

That later theorem would discharge:

```text
Finset.sum (Finset.range (K + 1)) (fun _ : Nat => c)
```

from a statement involving:

```text
((K + 1 : Nat) : Q) * c
```

### Non-goals

DKMK-013F should not add:

- Lean code;
- a finite-sum simplification lemma;
- a simplified constant-band theorem;
- a Mertens theorem;
- a big-O statement;
- a logarithmic threshold provider;
- a dyadic-specific route theorem.

### Next step

DKMK-013G should implement only:

```lean
DyadicBandAnalyticEstimate.constantBand
```

with the `Finset.sum`-form `hbound`.

## 14. DKMK-013G Lean constantBand Provider

DKMK-013G adds:

```lean
DyadicBandAnalyticEstimate.constantBand
```

The theorem uses the exact shape fixed in DKMK-013F:

```text
hc:
  0 <= c

hbound:
  ((Finset.sum (Finset.range (K + 1)) (fun _ : Nat => c) : Q) : R) <=
    1 + error
```

and produces:

```lean
DyadicBandAnalyticEstimate x K (fun _ : Nat => c) error
```

The proof only fills:

```text
increment_nonneg := fun _ _ => hc
total_le_one_add_error := hbound
```

This step deliberately does not add:

- finite-sum simplification;
- a simplified constant-band theorem;
- a computed `((K + 1 : Nat) : Q) * c` bound;
- a route theorem;
- a Mertens theorem;
- a big-O statement;
- a logarithmic threshold provider.

## 15. DKMK-013H Constant Band Sum-Bound Shape

DKMK-013H fixes the exact shape for the optional finite-sum simplification
provider.

This is still a docs-only step.  It does not add Lean code.

### Motivation

`constantBand` currently expects:

```text
((Finset.sum (Finset.range (K + 1)) (fun _ : Nat => c) : Q) : R) <=
  1 + error
```

This is easy for Lean to consume, but callers may naturally have a bound in
terms of:

```text
((K + 1 : Nat) : Q) * c
```

The optional theorem should bridge that caller-facing bound to the existing
`constantBand` theorem.

### Proposed theorem name

Use:

```lean
DyadicBandAnalyticEstimate.constantBand_of_natCastMulBound
```

Reason:

```text
constantBand:
  same target as the existing constant provider

of_natCastMulBound:
  input bound is stated using a Nat-cast count multiplied by c
```

### Proposed Lean shape

Use an explicit Rat expression before coercing to Real:

```lean
theorem DyadicBandAnalyticEstimate.constantBand_of_natCastMulBound
    (x K : Nat) (c : Q)
    (hc : 0 <= c)
    {error : R}
    (hbound :
      ((((K + 1 : Nat) : Q) * c : Q) : R) <= 1 + error) :
    DyadicBandAnalyticEstimate x K (fun _ : Nat => c) error
```

The proof should call:

```lean
DyadicBandAnalyticEstimate.constantBand
```

after proving the finite-sum identity:

```text
Finset.sum (Finset.range (K + 1)) (fun _ : Nat => c)
  = ((K + 1 : Nat) : Q) * c
```

### Implementation risk

The only expected work is finite-sum and coercion normalization.

The theorem should not introduce:

- route changes;
- a new analytic contract;
- computed dyadic tail estimates;
- Mertens or big-O;
- logarithmic thresholds.

### Next step

DKMK-013I should try the Lean implementation of:

```lean
DyadicBandAnalyticEstimate.constantBand_of_natCastMulBound
```

If the finite-sum identity creates too much friction, keep `constantBand` as the
only Lean provider and move on to decreasing / dyadic tail provider design.

## 16. DKMK-013I Lean natCastMulBound Provider

DKMK-013I adds:

```lean
DyadicBandAnalyticEstimate.constantBand_of_natCastMulBound
```

The theorem uses the shape fixed in DKMK-013H:

```text
hbound:
  ((((K + 1 : Nat) : Q) * c : Q) : R) <= 1 + error
```

and produces:

```lean
DyadicBandAnalyticEstimate x K (fun _ : Nat => c) error
```

The implementation calls:

```lean
DyadicBandAnalyticEstimate.constantBand
```

and discharges the finite sum with:

```text
Finset.sum_const
Finset.card_range
nsmul_eq_mul
```

This confirms that the caller-facing Nat-cast-multiply bound is light enough to
keep as a convenience provider.

This step does not add:

- route changes;
- a new analytic contract;
- dyadic tail estimates;
- Mertens or big-O;
- logarithmic thresholds.
