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
