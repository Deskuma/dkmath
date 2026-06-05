# DKMK-017: Analytic Input Source

DKMK-017 starts after DKMK-016 closed the API route:

```text
GeometricBudgetSource
+ first-band bound
+ uniform decay
+ increment nonnegativity
  -> DyadicBandAnalyticEstimate
  -> TruncationEnvelopeEstimate
  -> existing finite-step route
```

The remaining work is no longer API plumbing.  The next chapter should move
toward concrete analytic input sources.

## 0. Work Granularity Policy

DKMK-015 and DKMK-016 were intentionally docs-heavy because they fixed API
boundaries.  DKMK-017 changes the working pace.

The default unit of work is now a larger implementation bundle:

```text
design decision
  -> Lean implementation attempts
  -> self-diagnosis from Lean errors
  -> verification
  -> concise report to reviewer
```

The reviewer should not have to inspect every small constructor, wrapper, or
non-branching proof step.  If the next step is locally decidable, implement and
test it before reporting.

### When to ask for review before implementing

Stop for reviewer judgment only when the decision changes the route shape:

- adding a new structure rather than reusing an existing one;
- moving an assumption across API boundaries;
- choosing between Rat-side and Real-side theorem surfaces;
- deciding whether to introduce a new downstream wrapper;
- accepting a mathematically stronger or weaker analytic obligation;
- changing chapter scope.

### When to proceed without a separate review

Proceed directly when the step is local:

- thin constructors around existing fields;
- wrappers that only compose already accepted theorems;
- helper lemmas whose assumptions are already fixed by the roadmap;
- proof repairs found by Lean during implementation;
- docs updates that only record completed work.

### Docs-only limit

Docs-only review steps should not run three times in a row.  If two consecutive
docs-only steps have happened, the next step should be either:

- a Lean implementation attempt;
- a summary closing the design branch;
- a clear report that the attempted Lean target is not currently feasible.

Non-goals should be recorded at chapter start and chapter end, not repeated in
every phase.

## 1. Chapter Goal

DKMK-017 should design and test sources for the remaining analytic inputs:

```text
A. increment 0 <= B.base
B. increment (k + 1) <= B.ratio * increment k
C. (B.base : Real) * (1 / (1 - (B.ratio : Real))) <= 1 + B.error
```

These are the inputs consumed by:

```text
DyadicBandAnalyticEstimate.ofFirstBandDecayBudgetSource
```

The chapter should keep the DKMK-016 route stable while exploring how much of
A, B, and C can be supplied by Lean-side reusable surfaces.

## 2. First Bundle Target

The first implementation bundle should investigate an abstract analytic source
surface that packages the three remaining obligations without committing to
Mertens, big-O, logarithmic thresholds, or rounding.

Candidate shape:

```lean
structure FirstBandDecayBudgetSource
    (K : Nat)
    (increment : Nat -> Rat) where
  budget : GeometricBudgetSource
  hinc_nonneg :
    forall k in Finset.range (K + 1), 0 <= increment k
  hbase0 :
    increment 0 <= budget.base
  hdecay :
    forall k in Finset.range K,
      increment (k + 1) <= budget.ratio * increment k
```

This shape is intentionally only a candidate.  It reintroduces a combined
source package, so the first bundle must test whether it actually improves
caller ergonomics without duplicating DKMK-016's responsibility split.

Possible implementation outcomes:

1. accept a combined source because it is useful as an analytic-input package;
2. reject it and keep the existing four separate inputs;
3. replace it with a smaller source that only packages A and B;
4. defer structure work and first prove reusable helper lemmas around C.

The report should state which outcome Lean and route ergonomics support.

## 3. Preferred Lean Experiment Order

Within a bundle, prefer this order:

1. search existing source and theorem names around
   `GeometricBudgetSource`, `ofFirstBandDecayBudgetSource`, and
   `SourceMassTruncation`;
2. test the smallest structure or theorem target in Lean;
3. let Lean expose cast, range, and field-access friction;
4. repair local proof issues without stopping for review;
5. run the targeted module build;
6. only then update roadmap and History with the result.

This is the intended change from the DKMK-016 pace: Lean errors are part of the
self-diagnosis loop, not a reason to stop early.

## 4. Verification Plan

For Lean bundles:

```text
lake build DkMath.NumberTheory.PrimitiveSet.SourceMassTruncation
lake build DkMath.NumberTheory.PrimitiveSet
git diff --check
long-line check on changed docs
```

For docs-only setup steps:

```text
git diff --check
long-line check on changed docs
```

## 5. Chapter Non-goals

DKMK-017 should not start by proving:

- Mertens estimates;
- big-O statements;
- logarithmic threshold selection;
- real-to-Nat rounding;
- rational approximations of `log x`;
- a replacement for the DKMK-016 route.

Those may become later inputs, but the first task is to find the right Lean
surface for feeding the already established provider route.

## 6. DKMK-017A First Implementation Bundle

DKMK-017A tested the combined source package proposed in the chapter setup.

### Tried target

Lean target:

```lean
structure FirstBandDecayBudgetSource
    (K : Nat)
    (increment : Nat -> Rat) where
  budget : GeometricBudgetSource
  hinc_nonneg :
    forall k in Finset.range (K + 1), 0 <= increment k
  hbase0 :
    increment 0 <= budget.base
  hdecay :
    forall k in Finset.range K,
      increment (k + 1) <= budget.ratio * increment k
```

Provider target:

```lean
theorem DyadicBandAnalyticEstimate.ofFirstBandDecayBudgetSourcePackage
    (x K : Nat)
    (increment : Nat -> Rat)
    (S : FirstBandDecayBudgetSource K increment) :
    DyadicBandAnalyticEstimate x K increment S.budget.error
```

### Result

The target was accepted.

`FirstBandDecayBudgetSource` is useful as an analytic-input package.  It does
not replace the DKMK-016 responsibility split, and it does not add a new
analytic theorem.  It simply packages the four inputs that are already consumed
together by:

```lean
DyadicBandAnalyticEstimate.ofFirstBandDecayBudgetSource
```

### Lean findings

No Rat / Real cast issue appeared in this bundle.

The package theorem is a direct delegation:

```text
S.budget
S.hinc_nonneg
S.hbase0
S.hdecay
  -> DyadicBandAnalyticEstimate.ofFirstBandDecayBudgetSource
```

This means the combined package is ergonomically valid, but it should stay at
the analytic-input boundary.  It should not be expanded into a second route
layer.

### Decision

Adopt `FirstBandDecayBudgetSource` as the DKMK-017 analytic-input package.

Do not add a new truncation wrapper in this bundle.  The existing route remains:

```text
FirstBandDecayBudgetSource
  -> DyadicBandAnalyticEstimate.ofFirstBandDecayBudgetSourcePackage
  -> DyadicBandAnalyticEstimate
  -> DyadicBandAnalyticEstimate.toTruncationEnvelopeEstimate
```

### Verification

DKMK-017A was checked with:

```text
lake build DkMath.NumberTheory.PrimitiveSet.SourceMassTruncation
```

The primitive-set aggregator build and diff hygiene checks are run after the
chapter notes are updated.

## 7. DKMK-017B Source Constructor Bundle

DKMK-017B tested whether `FirstBandDecayBudgetSource` should rely on raw record
syntax or provide explicit constructors for analytic-input callers.

### Tried targets

Minimal constructor from an existing budget source:

```lean
def FirstBandDecayBudgetSource.ofBudgetSource
    {K : Nat} {increment : Nat -> Rat}
    (B : GeometricBudgetSource)
    (hinc_nonneg :
      forall k in Finset.range (K + 1), 0 <= increment k)
    (hbase0 : increment 0 <= B.base)
    (hdecay :
      forall k in Finset.range K,
        increment (k + 1) <= B.ratio * increment k) :
    FirstBandDecayBudgetSource K increment
```

Constructor from an explicit one-over-one-minus budget:

```lean
def FirstBandDecayBudgetSource.ofBudgetAndDecay
    {K : Nat} {increment : Nat -> Rat}
    (base ratio : Rat)
    (error : Real)
    ...
    FirstBandDecayBudgetSource K increment
```

The second constructor builds:

```text
GeometricBudgetSource.ofBudget
  -> FirstBandDecayBudgetSource.ofBudgetSource
```

### Result

Both constructors were accepted.

`ofBudgetSource` is the minimal package constructor.  `ofBudgetAndDecay` is the
caller-facing constructor for the concrete hbudget input:

```text
(base : Real) * (1 / (1 - (ratio : Real))) <= 1 + error
```

### Lean findings

The first implementation attempt placed the `FirstBandDecayBudgetSource`
namespace before `GeometricBudgetSource.ofBudget`.  Lean correctly failed with:

```text
Unknown constant `DkMath.NumberTheory.PrimitiveSet.GeometricBudgetSource.ofBudget`
```

Moving the constructor namespace after `end GeometricBudgetSource` fixed the
issue.  No proof or coercion problem remained.

### Decision

Adopt both constructors.

This is not a new analytic theorem.  It is the first concrete source-constructor
surface for loading analytic inputs into the DKMK-017 package.

### Verification

DKMK-017B was checked with:

```text
lake build DkMath.NumberTheory.PrimitiveSet.SourceMassTruncation
```

The primitive-set aggregator build and diff hygiene checks are run after the
chapter notes are updated.

## 8. DKMK-017C Budget Inequality Helper Bundle

DKMK-017C tested Real-side helper lemmas for producing the `hbudget` field of
`GeometricBudgetSource`.

### Tried targets

Denominator-cleared helper:

```lean
theorem geometricBudget_le_of_base_le_mul_one_sub
    {base ratio error : Real}
    (hr1 : ratio < 1)
    (hbaseBudget : base <= (1 + error) * (1 - ratio)) :
    base * (1 / (1 - ratio)) <= 1 + error
```

Special case with a `1` budget:

```lean
theorem geometricBudget_le_one_add_error_of_base_le_one_sub
    {base ratio error : Real}
    (hr1 : ratio < 1)
    (herror : 0 <= error)
    (hbaseBudget : base <= 1 - ratio) :
    base * (1 / (1 - ratio)) <= 1 + error
```

Geometric budget source constructors:

```lean
def GeometricBudgetSource.ofDenomClearedBudget
def GeometricBudgetSource.ofBaseLeOneSub
```

### Result

All targets were accepted.

The main helper uses `div_le_iff₀` with:

```text
0 < 1 - ratio
```

derived from `ratio < 1`.  No nonnegativity assumption on `1 + error` is needed
for the denominator-cleared helper.

The special `base <= 1 - ratio` helper needs `0 <= error`, because it upgrades
the target bound from `1` to `1 + error`.

### Decision

Adopt the denominator-cleared helper and both budget source constructors.

This is the first DKMK-017 helper that actually reduces the burden of proving:

```text
(base : Real) * (1 / (1 - (ratio : Real))) <= 1 + error
```

Callers may now prove the denominator-cleared form:

```text
(base : Real) <= (1 + error) * (1 - (ratio : Real))
```

and use `GeometricBudgetSource.ofDenomClearedBudget`.

### Verification

DKMK-017C was checked with:

```text
lake build DkMath.NumberTheory.PrimitiveSet.SourceMassTruncation
```

The primitive-set aggregator build and diff hygiene checks are run after the
chapter notes are updated.

## 9. DKMK-017D Nat-Bound Source Helper Bundle

DKMK-017D tested helper surfaces for supplying `hinc_nonneg` and `hdecay`
without asking analytic callers to work directly with `Finset.range`
membership.

### Tried targets

Nonnegativity conversion:

```lean
theorem rangeSuccNonneg_of_le
    (K : Nat) (increment : Nat -> Rat)
    (hinc_nonneg :
      forall k, k <= K -> 0 <= increment k) :
    forall k in Finset.range (K + 1), 0 <= increment k
```

Uniform decay conversion:

```lean
theorem rangeDecay_of_lt
    (K : Nat) (increment : Nat -> Rat) (ratio : Rat)
    (hdecay :
      forall k, k < K -> increment (k + 1) <= ratio * increment k) :
    forall k in Finset.range K,
      increment (k + 1) <= ratio * increment k
```

Source constructor from Nat-indexed hypotheses:

```lean
def FirstBandDecayBudgetSource.ofBudgetSourceNatBounds
```

### Result

All targets were accepted.

The decay helper deliberately keeps the multiplicative form:

```text
increment (k + 1) <= ratio * increment k
```

It does not introduce division by `increment k`, so no positivity hypothesis on
`increment k` is needed.

### Decision

Adopt the Nat-bound helpers and `ofBudgetSourceNatBounds`.

This is the first DKMK-017 helper that reduces the burden of supplying:

```text
hinc_nonneg
hdecay
```

without changing the provider route or the mathematical strength of the decay
obligation.

### Verification

DKMK-017D was checked with:

```text
lake build DkMath.NumberTheory.PrimitiveSet.SourceMassTruncation
```

The primitive-set aggregator build and diff hygiene checks are run after the
chapter notes are updated.

## 10. DKMK-017E First-Band Self-Base Bundle

DKMK-017E tested whether the remaining first-band input:

```text
hbase0 : increment 0 <= base
```

can be closed by choosing `base := increment 0`.

### Tried targets

Combined denominator-cleared / Nat-bound constructor:

```lean
def FirstBandDecayBudgetSource.ofDenomClearedBudgetNatBounds
```

Self-base constructor:

```lean
def FirstBandDecayBudgetSource.ofSelfBaseDenomClearedBudgetNatBounds
    {K : Nat} {increment : Nat -> Rat}
    (ratio : Rat)
    (error : Real)
    ...
    FirstBandDecayBudgetSource K increment
```

The self-base constructor fixes:

```text
base := increment 0
```

and closes:

```text
increment 0 <= base
```

by reflexivity.

### Result

Both targets were accepted.

The self-base route derives:

```text
0 <= (increment 0 : Real)
```

from the Nat-bound nonnegativity hypothesis at `k = 0`.

### Decision

Adopt both constructors.

`ofDenomClearedBudgetNatBounds` is a library-facing composition wrapper for
the DKMK-017C and DKMK-017D surfaces.

`ofSelfBaseDenomClearedBudgetNatBounds` is the first constructor that removes
the explicit `hbase0` argument.  It does not remove the budget obligation; it
moves it to:

```text
(increment 0 : Real) <= (1 + error) * (1 - (ratio : Real))
```

This is useful when the first band itself is the intended geometric base.

### Verification

DKMK-017E was checked with:

```text
lake build DkMath.NumberTheory.PrimitiveSet.SourceMassTruncation
```

The primitive-set aggregator build and diff hygiene checks are run after the
chapter notes are updated.

## 11. DKMK-017F Truncation Wrapper Checkpoint

DKMK-017F tested whether one final downstream wrapper is useful before moving
from abstract source surfaces to concrete analytic estimates.

### Tried targets

Package-to-envelope wrapper:

```lean
theorem TruncationEnvelopeEstimate.ofFirstBandDecayBudgetSourcePackage
    (x K : Nat)
    (increment : Nat -> Rat)
    (S : FirstBandDecayBudgetSource K increment) :
    TruncationEnvelopeEstimate
      (Finset.range (K + 1))
      (fun k : Nat => x * 2^k)
      increment
      S.budget.error
```

Self-base standard route:

```lean
theorem TruncationEnvelopeEstimate
    .ofSelfBaseDenomClearedBudgetNatBounds
```

### Result

Both targets were accepted.

The package-to-envelope wrapper composes:

```text
DyadicBandAnalyticEstimate.ofFirstBandDecayBudgetSourcePackage
  -> DyadicBandAnalyticEstimate.toTruncationEnvelopeEstimate
```

The self-base route composes:

```text
FirstBandDecayBudgetSource.ofSelfBaseDenomClearedBudgetNatBounds
  -> TruncationEnvelopeEstimate.ofFirstBandDecayBudgetSourcePackage
```

### Decision

Adopt both wrappers.

These wrappers are intentionally downstream and library-facing.  They do not
add analytic assumptions and they do not replace the explicit dyadic route.
They make the standard DKMK-017 caller route visible at the truncation-envelope
boundary:

```text
ratio, error
hbaseBudget for increment 0
Nat-bound nonnegativity
Nat-bound decay
  -> TruncationEnvelopeEstimate
```

### Verification

DKMK-017F was checked with:

```text
lake build DkMath.NumberTheory.PrimitiveSet.SourceMassTruncation
```

The primitive-set aggregator build and diff hygiene checks are run after the
chapter notes are updated.

## 12. DKMK-017G Source Surface Checkpoint

DKMK-017G closes the abstract source-surface pass before moving to concrete
analytic estimates.

### Accepted standard route

The standard caller route is now:

```text
ratio : Rat
error : Real

hr0 :
  0 <= (ratio : Real)

hr1 :
  (ratio : Real) < 1

hbaseBudget :
  (increment 0 : Real) <= (1 + error) * (1 - (ratio : Real))

hinc_nonneg :
  forall k, k <= K -> 0 <= increment k

hdecay :
  forall k, k < K -> increment (k + 1) <= ratio * increment k

TruncationEnvelopeEstimate.ofSelfBaseDenomClearedBudgetNatBounds
  -> TruncationEnvelopeEstimate
```

This route avoids exposing callers to:

- `GeometricBudgetSource`;
- `FirstBandDecayBudgetSource`;
- `DyadicBandAnalyticEstimate`;
- direct `Finset.range` membership proofs;
- direct one-over-one-minus budget proofs.

### General route still available

The more general route remains available when the geometric base is not
`increment 0`:

```text
GeometricBudgetSource.ofDenomClearedBudget
  -> FirstBandDecayBudgetSource.ofBudgetSourceNatBounds
  -> DyadicBandAnalyticEstimate.ofFirstBandDecayBudgetSourcePackage
  -> TruncationEnvelopeEstimate.ofFirstBandDecayBudgetSourcePackage
```

### What is now reduced to concrete analytic input

The remaining mathematical inputs are:

```text
hbaseBudget:
  (increment 0 : Real) <= (1 + error) * (1 - (ratio : Real))

hinc_nonneg:
  forall k, k <= K -> 0 <= increment k

hdecay:
  forall k, k < K -> increment (k + 1) <= ratio * increment k
```

DKMK-017A-F did not prove these.  It made their interface smaller and more
caller-friendly.

### Decision

Stop adding wrappers for now.

The next checkpoint should start concrete analytic source work.  The first
target should be one of:

1. choose or expose a concrete `increment` candidate;
2. prove `hinc_nonneg` for that candidate;
3. prove first-band budget for `increment 0`;
4. prove uniform decay for the candidate.

The preferred next move is to inspect the existing candidate definitions before
adding another abstraction.

### Verification

DKMK-017G is docs-only.  It was checked with:

```text
git diff --check
long-line check on changed docs
```

## 13. DKMK-017H Increment Candidate Discovery Bundle

DKMK-017H searched existing PrimitiveSet / SourceMassTruncation definitions for
a concrete dyadic-band `increment : Nat -> Rat` candidate.

### Search targets

Checked:

- `SourceMassTruncation.lean`
- `DescentBridge.lean`
- `LogCapacityHittingBridge.lean`
- `WeightedPathFamily.lean`
- `WeightProvider.lean`
- nearby PrimitiveSet modules using `increment`, `weight`, `mass`, `band`,
  and `source`

### Findings

No concrete dyadic-band `increment : Nat -> Rat` candidate is currently exposed.

Existing increment-like surfaces split into three groups:

1. Abstract dyadic-band input:
   - `DyadicBandAnalyticEstimate`
   - `TruncationEnvelopeEstimate.dyadicRange`
   - `FirstBandDecayBudgetSource`
   These already take `increment : Nat -> Rat` as caller-supplied input.
2. Finite-step source-mass input:
   - `finiteStepTailHeight`
   - `finiteStepTailNatMassSpace`
   - `finiteStepTailNatMassSpace_logCapacitySourceMassBound`
   These take arbitrary `increment : ι -> Rat`, not a concrete dyadic
   `Nat -> Rat`.
3. Concrete finite/sample weights:
   - `twoStepTailFiniteIncrement : Bool -> Rat`
   - `sampleBoolPathWeight : Bool -> Rat`
   - `sampleBoolSubprobPathWeight : Bool -> Rat`
   These are concrete and nonnegative, but they are Bool-indexed finite samples,
   not dyadic-band `Nat -> Rat` candidates.

### Immediate Lean implication

There is no existing candidate for which the standard DKMK-017 route can now
prove:

```text
hinc_nonneg :
  forall k, k <= K -> 0 <= increment k

hbaseBudget :
  (increment 0 : Real) <= (1 + error) * (1 - (ratio : Real))

hdecay :
  forall k, k < K -> increment (k + 1) <= ratio * increment k
```

without first defining or exposing a concrete dyadic-band increment.

### Candidate ranking

For DKMK-017, the viable next target is not a proof of `hdecay` yet.  It is an
increment-shape definition.

Recommended next candidate:

- define an abstract-but-concrete geometric increment:
  `geometricIncrement base ratio : Nat -> Rat := fun k => base * ratio ^ k`

Why:

- `hinc_nonneg` should be provable from `0 <= base` and `0 <= ratio`;
- `hdecay` should be equality or a one-line inequality;
- `hbaseBudget` connects directly to the existing denominator-cleared budget
  helper;
- it tests the DKMK-017 route with a real `Nat -> Rat` candidate before
  importing heavier analytic estimates.

Not recommended yet:

- using `twoStepTailFiniteIncrement`, because it is `Bool -> Rat`;
- using weighted path sample weights, because they are path-indexed, not
  dyadic-band indexed;
- introducing quotient-path/logarithmic estimates before a dyadic-band
  increment shape exists.

### Decision

DKMK-017H is discovery-only.

The next Lean implementation bundle should introduce a concrete dyadic-band
candidate, preferably `geometricIncrement`, and prove at least `hinc_nonneg`.
If build friction is low, also try the exact decay lemma.

### Verification

DKMK-017H is docs-only.  It was checked with:

```text
git diff --check
long-line check on changed docs
```

## 14. DKMK-017I Geometric Increment Route Test

DKMK-017I introduced the first concrete dyadic-band
`increment : Nat -> Rat` candidate:

```lean
def geometricIncrement (base ratio : Rat) (k : Nat) : Rat :=
  base * ratio ^ k
```

This candidate is intentionally simple.  Its purpose is to test whether the
DKMK-017 self-base route can consume a real `Nat -> Rat` increment without
adding new analytic machinery.

### Lean additions

Added to `SourceMassTruncation.lean`:

- `geometricIncrement`
- `geometricIncrement_nonneg`
- `geometricIncrement_zero`
- `geometricIncrement_decay`
- `geometricIncrement_decay_le`
- `FirstBandDecayBudgetSource.ofGeometricIncrement`
- `TruncationEnvelopeEstimate.ofGeometricIncrement`

### Result

The concrete route is accepted.

The local increment facts close as expected:

```text
0 <= base, 0 <= ratio
  -> forall k, 0 <= geometricIncrement base ratio k

geometricIncrement base ratio 0 = base

geometricIncrement base ratio (k + 1)
  = ratio * geometricIncrement base ratio k
```

The full truncation-envelope route also closes:

```text
base, ratio, error
0 <= base
0 <= ratio
(ratio : Real) < 1
(base : Real) <= (1 + error) * (1 - (ratio : Real))
  -> TruncationEnvelopeEstimate
       (Finset.range (K + 1))
       (fun k : Nat => x * 2^k)
       (geometricIncrement base ratio)
       error
```

### Interpretation

DKMK-017A-H reduced the route to a usable concrete interface.  DKMK-017I shows
that this interface is not merely abstract plumbing: a concrete dyadic-band
source can now reach `TruncationEnvelopeEstimate`.

The remaining analytic burden is exactly the first-band budget:

```text
(base : Real) <= (1 + error) * (1 - (ratio : Real))
```

For this geometric candidate, `hinc_nonneg` and `hdecay` are no longer the
hard inputs.

### Decision

Adopt `geometricIncrement` as the first concrete test source for DKMK-017.

The next checkpoint should decide whether to:

1. derive first-band budget facts for useful `base`, `ratio`, and `error`;
2. specialize the candidate to canonical choices such as `base = 1 - ratio`;
3. connect the candidate to a more analytic/logarithmic source.

### Verification

DKMK-017I was checked with:

```text
lake build DkMath.NumberTheory.PrimitiveSet.SourceMassTruncation
lake build DkMath.NumberTheory.PrimitiveSet
git diff --check
long-line check on changed docs
```

## 15. DKMK-017J Canonical First-Band Budget

DKMK-017J specialized the geometric increment route to the canonical first-band
choice:

```text
base = 1 - ratio
```

This is the first concrete discharge of the remaining DKMK-017I analytic input:

```text
(base : Real) <= (1 + error) * (1 - (ratio : Real))
```

### Lean additions

Added to `SourceMassTruncation.lean`:

- `geometricIncrement_baseEqOneSub_budget`
- `FirstBandDecayBudgetSource.ofGeometricIncrementBaseEqOneSub`
- `TruncationEnvelopeEstimate.ofGeometricIncrementBaseEqOneSub`

### Result

The canonical route is accepted.

The caller now supplies:

```text
base = 1 - ratio
0 <= ratio
(ratio : Real) < 1
0 <= error
```

and obtains:

```text
TruncationEnvelopeEstimate
  (Finset.range (K + 1))
  (fun k : Nat => x * 2^k)
  (geometricIncrement base ratio)
  error
```

The first-band budget is discharged internally:

```text
base = 1 - ratio
0 <= error
  -> (base : Real) <= (1 + error) * (1 - (ratio : Real))
```

Nonnegativity of `base` follows from `(ratio : Real) < 1` and
`base = 1 - ratio`.

### Interpretation

DKMK-017I showed that the concrete geometric increment can reach the envelope
when the first-band budget is supplied.

DKMK-017J removes that supplied budget for the canonical geometric choice.  For
this source, the full DKMK-017 route now only needs nonnegative error and the
usual ratio bounds.

### Decision

Adopt the canonical `base = 1 - ratio` specialization.

This is still a route-validation source, not the final analytic/logarithmic
source.  The next checkpoint can now decide whether to:

1. add a more ergonomic `base := 1 - ratio` theorem with no explicit `base`;
2. connect this geometric source to a finite-step mass theorem;
3. move toward a logarithmic or capacity-derived source.

### Verification

DKMK-017J was checked with:

```text
lake build DkMath.NumberTheory.PrimitiveSet.SourceMassTruncation
lake build DkMath.NumberTheory.PrimitiveSet
git diff --check
long-line check on changed docs
```

## 16. DKMK-017K Finite-Step Route Connection

DKMK-017K connected the canonical geometric increment source to the existing
finite-step mass route.

This follows the review-125 preference:

```text
do not add another thin base := 1 - ratio wrapper yet;
first check whether the DKMK-017J envelope is consumed by the finite-step route.
```

### Lean addition

Added to `SourceMassTruncation.lean`:

- `TruncationEnvelopeEstimate.geometricIncrementBaseEqOneSub_weightedHitMass_le_one_add_error`

### Result

The finite-step connection is accepted.

The route now reaches:

```text
base = 1 - ratio
0 <= ratio
(ratio : Real) < 1
0 <= error
PrimitiveOn A
  -> weightedHitMass A <= 1 + error
```

through:

```text
TruncationEnvelopeEstimate.ofGeometricIncrementBaseEqOneSub
  -> TruncationEnvelopeEstimate.finiteStepTail_weightedHitMass_le_one_add_error
```

The finite-step mass used by the final bound is:

```text
finiteStepTailNatMassSpace
  (Finset.range (K + 1))
  (fun k : Nat => x * 2^k)
  (geometricIncrement base ratio)
```

with nonnegativity supplied by the envelope.

### Interpretation

DKMK-017J made the canonical geometric source reach `TruncationEnvelopeEstimate`.

DKMK-017K shows that this envelope is not a dead endpoint.  It is consumed by
the existing finite-step tail machinery and reaches the DKMK-009 quotient-path
capacity hitting bound.

This completes the route-validation role of the geometric source:

```text
geometricIncrement
  -> canonical first-band budget
  -> truncation envelope
  -> finite-step tail mass
  -> quotient-path weightedHitMass bound
```

### Decision

Adopt the finite-step connection.

The route-validation source is now complete enough.  The next branch should
avoid more convenience wrappers unless they remove real friction.  The useful
next targets are:

1. summarize/close DKMK-017 as route-validation complete;
2. move toward logarithmic or capacity-derived source candidates;
3. identify which analytic source should replace the toy geometric increment.

### Verification

DKMK-017K was checked with:

```text
lake build DkMath.NumberTheory.PrimitiveSet.SourceMassTruncation
lake build DkMath.NumberTheory.PrimitiveSet
git diff --check
long-line check on changed docs
```
