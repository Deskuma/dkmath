# DKMK-016: Geometric Budget Source

DKMK-016 starts after DKMK-015 closed the finite geometric-sum / dyadic
provider connection route.

DKMK-015 ended with the caller path:

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

The remaining question is:

```text
Where does hbudget come from?
```

DKMK-016 should answer this at the interface level before introducing concrete
analytic estimates.

## 1. Scope

The chapter focus is the budget source:

```text
(base : Real) * (1 / (1 - (ratio : Real))) <= 1 + error
```

The first step should not prove a Mertens estimate, a big-O theorem, a
logarithmic threshold, or real-to-Nat rounding.

The first step should define an abstract surface that packages:

- the rational `base`;
- the rational `ratio`;
- the real `error`;
- nonnegativity of `base`;
- nonnegativity of `ratio`;
- strict contractivity of `ratio`;
- the geometric budget bound.

This keeps analytic input separate from the already completed DKMK-015 provider
connection.

## 2. DKMK-016A Abstract Budget Source Shape

DKMK-016A fixes the first interface shape.

Recommended Lean-facing shape:

```lean
structure GeometricBudgetSource where
  base : Rat
  ratio : Rat
  error : Real
  hbase : 0 <= (base : Real)
  hr0 : 0 <= (ratio : Real)
  hr1 : (ratio : Real) < 1
  hbudget : (base : Real) * (1 / (1 - (ratio : Real))) <= 1 + error
```

This is intentionally a small abstract package.

It does not yet mention:

- `x`;
- `K`;
- `increment`;
- pointwise majorization;
- `DyadicBandAnalyticEstimate`;
- finite-step source mass;
- log-capacity states.

Those belong to connection theorems after the budget source shape is stable.

## 3. Candidate Connection Theorem

After the structure exists, the natural connection theorem is:

```lean
theorem DyadicBandAnalyticEstimate
    .ofPointwiseGeometricMajorant_of_budgetSource
    (x K : Nat)
    (increment : Nat -> Rat)
    (B : GeometricBudgetSource)
    (hinc_nonneg :
      forall k in Finset.range (K + 1), 0 <= increment k)
    (hgeom :
      forall k in Finset.range (K + 1),
        increment k <= B.base * B.ratio ^ k) :
    DyadicBandAnalyticEstimate x K increment B.error
```

This should be a thin wrapper around:

```lean
DyadicBandAnalyticEstimate.ofPointwiseGeometricMajorant_of_baseGeomBudget
```

The structure should therefore be introduced before this theorem.

## 4. Why Abstract First

The next analytic problem is not finite geometric sums anymore.

The next problem is to justify:

```text
base / (1 - ratio) <= 1 + error
```

for concrete future choices of `base` and `ratio`.

Keeping this as an abstract budget source first has two advantages:

1. concrete analytic estimates can be plugged in later;
2. the existing dyadic provider route can remain independent of how the budget
   is proved.

This continues the DKMK pattern:

```text
abstract source
  -> thin provider wrapper
  -> concrete source refinements later
```

## 5. Non-goals

DKMK-016A should not add:

- concrete choices of `base` or `ratio`;
- a Mertens theorem;
- a big-O statement;
- a logarithmic threshold provider;
- real-to-Nat rounding;
- route theorem changes;
- a new dyadic provider structure;
- a duplicate of DKMK-015H.

## 6. Verification Plan

For docs-only steps:

```text
git diff --check
long-line check on changed docs
```

For Lean steps:

```text
lake build DkMath.NumberTheory.PrimitiveSet.SourceMassTruncation
lake build DkMath.NumberTheory.PrimitiveSet
git diff --check
long-line check on changed docs
```

## 7. DKMK-016B Lean Abstract Budget Source

DKMK-016B implements the first abstract budget source surface.

Added structure:

```lean
structure GeometricBudgetSource where
  base : Rat
  ratio : Rat
  error : Real
  hbase : 0 <= (base : Real)
  hr0 : 0 <= (ratio : Real)
  hr1 : (ratio : Real) < 1
  hbudget : (base : Real) * (1 / (1 - (ratio : Real))) <= 1 + error
```

Added wrapper:

```lean
theorem DyadicBandAnalyticEstimate
    .ofPointwiseGeometricMajorant_of_budgetSource
    (x K : Nat)
    (increment : Nat -> Rat)
    (B : GeometricBudgetSource)
    (hinc_nonneg :
      forall k in Finset.range (K + 1), 0 <= increment k)
    (hgeom :
      forall k in Finset.range (K + 1),
        increment k <= B.base * B.ratio ^ k) :
    DyadicBandAnalyticEstimate x K increment B.error
```

The Lean implementation is in:

```text
DkMath.NumberTheory.PrimitiveSet.SourceMassTruncation
```

### Proof route

The wrapper is a direct call to:

```lean
DyadicBandAnalyticEstimate.ofPointwiseGeometricMajorant_of_baseGeomBudget
```

It passes:

```text
B.base
B.ratio
B.error
B.hbase
B.hr0
B.hr1
B.hbudget
```

No new analytic estimate is proved here.

### Type-boundary behavior

The structure is not indexed by `x`, `K`, or `increment`.

This keeps the budget source independent of a particular dyadic band provider
instance.  If future budgets depend on `x` or `K`, a later
`GeometricBudgetSourceFor` style package can be added without changing this
abstract source.

### Verification

The implementation was checked with:

```text
lake build DkMath.NumberTheory.PrimitiveSet.SourceMassTruncation
lake build DkMath.NumberTheory.PrimitiveSet
git diff --check
```

### Non-goals

DKMK-016B does not add:

- concrete choices of `base` or `ratio`;
- a dependent `GeometricBudgetSourceFor`;
- a Mertens theorem;
- a big-O statement;
- a logarithmic threshold provider;
- real-to-Nat rounding;
- route theorem changes;
- a new dyadic provider structure;
- a duplicate of DKMK-015H.

## 8. DKMK-016C GeometricBudgetSource Usage Review

DKMK-016C fixes the intended usage of `GeometricBudgetSource` before adding any
concrete constructors.

### Construction pattern

A caller or future constructor should build:

```lean
B : GeometricBudgetSource
```

by supplying:

```text
B.base    : Rat
B.ratio   : Rat
B.error   : Real
B.hbase   : 0 <= (B.base : Real)
B.hr0     : 0 <= (B.ratio : Real)
B.hr1     : (B.ratio : Real) < 1
B.hbudget : (B.base : Real) * (1 / (1 - (B.ratio : Real))) <= 1 + B.error
```

The package should be treated as the source of the geometric budget, not as a
dyadic band estimate by itself.

### Provider usage pattern

Once `B : GeometricBudgetSource` is available, the caller should use:

```lean
have hE :
    DyadicBandAnalyticEstimate x K increment B.error :=
  DyadicBandAnalyticEstimate
    .ofPointwiseGeometricMajorant_of_budgetSource
      x K increment B hinc_nonneg hgeom
```

where:

```text
hinc_nonneg :
  forall k in Finset.range (K + 1), 0 <= increment k

hgeom :
  forall k in Finset.range (K + 1),
    increment k <= B.base * B.ratio ^ k
```

This keeps pointwise band control outside the budget source.

### Responsibility split

`GeometricBudgetSource` is responsible for:

```text
base
ratio
error
base nonnegativity
ratio nonnegativity
ratio contractivity
one-over-one-minus budget
```

`ofPointwiseGeometricMajorant_of_budgetSource` is responsible for:

```text
connecting B to the rational dyadic provider
using hgeom to compare increment with B.base * B.ratio^k
returning DyadicBandAnalyticEstimate x K increment B.error
```

It should not prove a concrete analytic estimate.

### When an indexed source may be needed

The current structure is intentionally not indexed by `x`, `K`, or `increment`.

An indexed package may become useful only when future concrete constructors make
`base`, `ratio`, or `error` depend on the dyadic window, for example:

```lean
structure GeometricBudgetSourceFor (x K : Nat) where
  ...
```

or:

```lean
structure GeometricBudgetSourceFor (K : Nat) where
  ...
```

Until such a dependency is forced by a concrete route, the unindexed
`GeometricBudgetSource` remains the preferred API.

### Next implementation direction

The next Lean step should not duplicate the wrapper.

Possible next steps are:

- add a small constructor theorem for `GeometricBudgetSource`;
- review a concrete `base` / `ratio` candidate;
- introduce an abstract upstream budget predicate;
- or postpone constructors until a concrete analytic route is identified.

### Non-goals

DKMK-016C does not add:

- Lean code;
- concrete choices of `base` or `ratio`;
- a dependent `GeometricBudgetSourceFor`;
- a Mertens theorem;
- a big-O statement;
- a logarithmic threshold provider;
- real-to-Nat rounding;
- route theorem changes;
- a new dyadic provider structure.

## 9. DKMK-016D Concrete Base/Ratio Candidate Review

DKMK-016D reviews the first concrete `base` / `ratio` candidate before adding
another Lean theorem.

The goal is not to solve the analytic budget problem yet.  The goal is to pick
a small first constructor that tests the `GeometricBudgetSource` API without
introducing Mertens, big-O, logarithmic thresholds, or rounding.

### Candidate 1: no constructor yet

The most conservative option is to stop with:

```lean
B : GeometricBudgetSource
```

and require callers to build `B` directly by record syntax.

This keeps the API minimal, but it does not exercise the intended constructor
path.  It also leaves no small example for later concrete constructors to
follow.

### Candidate 2: zero-ratio sanity constructor

The first concrete candidate should be:

```lean
GeometricBudgetSource.ofZeroRatio
```

Expected shape:

```lean
def GeometricBudgetSource.ofZeroRatio
    (base : Rat)
    (error : Real)
    (hbase : 0 <= (base : Real))
    (hbudget : (base : Real) <= 1 + error) :
    GeometricBudgetSource
```

with:

```text
ratio = 0
```

The key budget reduces to:

```text
(base : Real) * (1 / (1 - (0 : Real))) <= 1 + error
```

which should simplify to:

```text
(base : Real) <= 1 + error
```

This constructor is not an analytic result.  It is an API sanity constructor:
it confirms that `GeometricBudgetSource` can be built from a concrete ratio and
then passed into `ofPointwiseGeometricMajorant_of_budgetSource`.

### Candidate 3: external positive ratio constructor

A more general constructor would take a rational ratio and an explicit budget:

```lean
def GeometricBudgetSource.ofBudget
    (base ratio : Rat)
    (error : Real)
    (hbase : 0 <= (base : Real))
    (hr0 : 0 <= (ratio : Real))
    (hr1 : (ratio : Real) < 1)
    (hbudget :
      (base : Real) * (1 / (1 - (ratio : Real))) <= 1 + error) :
    GeometricBudgetSource
```

This is essentially record syntax.  It is useful only if it improves caller
readability.  It should not be the first concrete constructor.

### Candidate 4: analytic budget constructor

Later work may build a source from a real analytic estimate, for example from
specific choices of `base` and `ratio` coming from dyadic bands.

This is not yet ready.  It should wait until a concrete upstream route tells us
what `base`, `ratio`, and `error` should be.

### Chosen next Lean target

The recommended DKMK-016E target is:

```lean
GeometricBudgetSource.ofZeroRatio
```

This is deliberately small and concrete.

It should not introduce:

- `x`;
- `K`;
- `increment`;
- `DyadicBandAnalyticEstimate`;
- Mertens or big-O;
- logarithmic thresholds;
- real-to-Nat rounding.

### Expected proof route

The proof should build the structure directly:

```lean
{
  base := base
  ratio := 0
  error := error
  hbase := hbase
  hr0 := by norm_num
  hr1 := by norm_num
  hbudget := by
    simpa using hbudget
}
```

If `simpa` does not simplify the budget expression, the proof should first
normalize:

```text
1 - (0 : Real) = 1
1 / 1 = 1
base * 1 = base
```

### Non-goals

DKMK-016D does not add:

- Lean code;
- an analytic budget theorem;
- a dependent `GeometricBudgetSourceFor`;
- Mertens or big-O;
- logarithmic thresholds;
- real-to-Nat rounding;
- route theorem changes;
- a new dyadic provider structure.

## 10. DKMK-016E Lean Zero-Ratio Budget Source

DKMK-016E implements the zero-ratio API sanity constructor selected in
DKMK-016D.

Added definition:

```lean
def GeometricBudgetSource.ofZeroRatio
    (base : Rat)
    (error : Real)
    (hbase : 0 <= (base : Real))
    (hbudget : (base : Real) <= 1 + error) :
    GeometricBudgetSource
```

This constructor sets:

```text
ratio := 0
```

and closes the ratio side conditions by `norm_num`.

The budget field reduces from:

```text
(base : Real) * (1 / (1 - (0 : Real))) <= 1 + error
```

to the caller-supplied:

```text
(base : Real) <= 1 + error
```

### Type-boundary note

The implementation is a `def`, not a `theorem`.

The return type is `GeometricBudgetSource`, which is data, not `Prop`.
Therefore Lean correctly rejects:

```lean
theorem GeometricBudgetSource.ofZeroRatio ... : GeometricBudgetSource
```

with:

```text
type of theorem is not a proposition
```

This is useful API pressure: constructor-style packages of evidence should be
implemented as definitions unless the target itself is a proposition.

### Role

`GeometricBudgetSource.ofZeroRatio` is not an analytic estimate.

It is a small constructor proving that the abstract budget package can be
instantiated in a degenerate ratio case.  Future positive-ratio or analytic
budget constructors can use the same structure boundary.

### Verification

The implementation was checked with:

```text
lake build DkMath.NumberTheory.PrimitiveSet.SourceMassTruncation
lake build DkMath.NumberTheory.PrimitiveSet
git diff --check
long-line check on changed files
```

## 11. DKMK-016F Zero-Ratio Usage Wrapper

DKMK-016F checks the caller route from the zero-ratio constructor into the
budget-source provider wrapper.

Added theorem:

```lean
theorem DyadicBandAnalyticEstimate.ofPointwiseZeroRatioMajorant
    (x K : Nat)
    (increment : Nat -> Rat)
    (base : Rat)
    (hinc_nonneg :
      forall k in Finset.range (K + 1), 0 <= increment k)
    (hgeom :
      forall k in Finset.range (K + 1),
        increment k <= base * (0 : Rat) ^ k)
    {error : Real}
    (hbase : 0 <= (base : Real))
    (hbudget : (base : Real) <= 1 + error) :
    DyadicBandAnalyticEstimate x K increment error
```

The proof constructs:

```lean
GeometricBudgetSource.ofZeroRatio base error hbase hbudget
```

and passes it to:

```lean
DyadicBandAnalyticEstimate.ofPointwiseGeometricMajorant_of_budgetSource
```

The only local simplification is unfolding the zero-ratio source so that
`B.base` and `B.ratio` reduce to `base` and `0`.

### Why this step comes before positive-ratio constructors

DKMK-016E showed that the abstract budget package can be constructed.

DKMK-016F confirms that the package is also convenient at the provider call
site:

```text
GeometricBudgetSource.ofZeroRatio
  -> ofPointwiseGeometricMajorant_of_budgetSource
  -> DyadicBandAnalyticEstimate
```

This keeps API pressure visible before adding a less degenerate
positive-ratio constructor.

### Role

This theorem is still not an analytic estimate.

It is a usage wrapper for the degenerate ratio case.  Since `0^0 = 1` and
`0^k = 0` for positive `k`, the hypothesis is intentionally strong away from
the initial dyadic band.  Its purpose is to test API composition, not to model
the eventual analytic source.

### Verification

The implementation was checked with:

```text
lake build DkMath.NumberTheory.PrimitiveSet.SourceMassTruncation
lake build DkMath.NumberTheory.PrimitiveSet
git diff --check
long-line check on changed files
```

## 12. DKMK-016G Positive-Ratio Constructor Shape Review

DKMK-016G reviews the next non-degenerate constructor shape before adding more
Lean code.

The obvious positive-ratio constructor is:

```lean
def GeometricBudgetSource.ofBudget
    (base ratio : Rat)
    (error : Real)
    (hbase : 0 <= (base : Real))
    (hr0 : 0 <= (ratio : Real))
    (hr1 : (ratio : Real) < 1)
    (hbudget :
      (base : Real) * (1 / (1 - (ratio : Real))) <= 1 + error) :
    GeometricBudgetSource
```

This is a named constructor for the full structure fields.  It does not prove
a new analytic estimate and it does not simplify a budget inequality.  Its
only value is API readability at call sites.

### Comparison with record syntax

Direct record syntax already works:

```lean
{
  base := base
  ratio := ratio
  error := error
  hbase := hbase
  hr0 := hr0
  hr1 := hr1
  hbudget := hbudget
}
```

`GeometricBudgetSource.ofBudget` is therefore useful only if we want a stable
named API that hides record-field order and gives later constructors a common
namespace style.

### Comparison with analytic constructors

An analytic constructor would do more work.  For example, it might take a
Mertens-style estimate, a logarithmic threshold, or a rounded dyadic parameter
and derive:

```text
(base : Real) * (1 / (1 - (ratio : Real))) <= 1 + error
```

That is not the role of `ofBudget`.  `ofBudget` should take the budget proof as
input.

### Recommended next Lean step

The next Lean step should add `GeometricBudgetSource.ofBudget` only as a
readability constructor:

```lean
def GeometricBudgetSource.ofBudget
    (base ratio : Rat)
    (error : Real)
    (hbase : 0 <= (base : Real))
    (hr0 : 0 <= (ratio : Real))
    (hr1 : (ratio : Real) < 1)
    (hbudget :
      (base : Real) * (1 / (1 - (ratio : Real))) <= 1 + error) :
    GeometricBudgetSource
```

The proof should be direct record construction.  No provider wrapper, no
finite-sum theorem, and no analytic estimate should be added in the same step.

### Type-boundary rule

As learned in DKMK-016E, this must be a `def`, not a `theorem`.

`GeometricBudgetSource` is data in `Type`, even though it contains proof fields.
Constructor APIs returning it should therefore be definitions.

### Verification

DKMK-016G is docs-only.  It was checked with:

```text
git diff --check
long-line check on changed docs
```

## 13. DKMK-016H Lean Explicit Budget Constructor

DKMK-016H implements the readability constructor reviewed in DKMK-016G.

Added definition:

```lean
def GeometricBudgetSource.ofBudget
    (base ratio : Rat)
    (error : Real)
    (hbase : 0 <= (base : Real))
    (hr0 : 0 <= (ratio : Real))
    (hr1 : (ratio : Real) < 1)
    (hbudget :
      (base : Real) * (1 / (1 - (ratio : Real))) <= 1 + error) :
    GeometricBudgetSource
```

The implementation is direct record construction:

```lean
{
  base := base
  ratio := ratio
  error := error
  hbase := hbase
  hr0 := hr0
  hr1 := hr1
  hbudget := hbudget
}
```

No simplification, finite-sum theorem, provider wrapper, or analytic estimate
is introduced here.

### Role

`GeometricBudgetSource.ofBudget` is the generic constructor for an already
proved one-over-one-minus budget.

It accepts nonnegative contractive ratios:

```text
0 <= (ratio : Real)
(ratio : Real) < 1
```

so it is more accurately a nonnegative-contractive-ratio constructor than a
strict positive-ratio constructor.

### Verification

The implementation was checked with:

```text
lake build DkMath.NumberTheory.PrimitiveSet.SourceMassTruncation
lake build DkMath.NumberTheory.PrimitiveSet
git diff --check
long-line check on changed files
```

## 14. DKMK-016I Concrete Base/Ratio Candidate Review

DKMK-016I shifts from constructor API to candidate budget design.

The target budget shape is:

```text
(base : Real) * (1 / (1 - (ratio : Real))) <= 1 + error
```

This step does not prove Mertens, big-O, logarithmic thresholds, or rounding.
It only compares symbolic candidates for future analytic input.

### Candidate A: logarithmic base with dyadic ratio

Shape:

```text
base  = c / log x
ratio = 1 / 2
```

Budget pressure:

```text
base * (1 / (1 - ratio)) = 2 * c / log x
```

This is simple and matches a dyadic decay intuition.  It is attractive as a
first symbolic candidate because the budget reduces to a single logarithmic
smallness condition.

Risk:

```text
c / log x
```

is not rational-valued without an extra approximation or rational envelope.
Using it directly would require a real-to-rational bridge or an indexed source.

### Candidate B: logarithmic base with prime-dependent ratio

Shape:

```text
base  = c / log x
ratio = 1 / q
```

Budget pressure:

```text
base * (1 / (1 - ratio)) = (c / log x) * (q / (q - 1))
```

This could better match prime-power or quotient-path structure, but it exposes
more parameters.  It should wait until the upstream route says whether `q` is a
fixed prime, a selected divisor, or a local branch parameter.

### Candidate C: first-band mass with uniform decay

Shape:

```text
base  = first band mass upper bound
ratio = uniform decay bound
```

This is the most compatible with the existing pointwise majorant:

```text
increment k <= base * ratio^k
```

It separates two future obligations:

```text
increment 0 <= base
increment (k + 1) <= ratio * increment k
```

or a direct pointwise version of the same decay claim.

This is the best next design target because it matches the current
`DyadicBandAnalyticEstimate` interface without forcing a concrete analytic
formula yet.

### Candidate D: tail-mass envelope as base

Shape:

```text
base  = dyadic band tail mass envelope
ratio = geometric decay rate
```

This is closer to the final route, but it may duplicate the role of
`increment` unless the envelope is clearly separated from the actual dyadic
increments.

It should be considered after Candidate C has a stable interface.

### Recommended next step

The next step should review Candidate C as an interface:

```text
first-band upper bound
uniform decay bound
  -> GeometricBudgetSource.ofBudget
```

The likely Lean-facing package would not prove the analytic decay yet.  It
would name the inputs needed to turn a future first-band/decay estimate into a
`GeometricBudgetSource`.

### Non-goals

DKMK-016I does not add:

- Lean code;
- Mertens or big-O;
- logarithmic thresholds;
- real-to-Nat rounding;
- rational approximation of `log x`;
- a concrete value of `c`;
- a concrete value of `x`;
- a provider wrapper.

### Verification

DKMK-016I is docs-only.  It was checked with:

```text
git diff --check
long-line check on changed docs
```

## 15. DKMK-016J First-Band / Uniform-Decay Interface Review

DKMK-016J fixes the interface obligations behind Candidate C.

The provider route needs two independent inputs:

```text
Budget obligation:
  base * (1 / (1 - ratio)) <= 1 + error

Pointwise decay obligation:
  increment k <= base * ratio^k
```

`GeometricBudgetSource` packages the budget obligation.  It should not also
package the pointwise decay of a particular `increment`, because it is not
indexed by `x`, `K`, or `increment`.

### Recommended interface split

The first-band / uniform-decay interface should remain split:

```text
GeometricBudgetSource.ofBudget
  packages base, ratio, error, hbase, hr0, hr1, hbudget

hgeom
  proves increment k <= base * ratio^k on Finset.range (K + 1)
```

Then the existing provider wrapper combines them:

```lean
DyadicBandAnalyticEstimate
  .ofPointwiseGeometricMajorant_of_budgetSource
    x K increment B hinc_nonneg hgeom
```

This avoids adding a duplicate `FirstBandDecayBudgetInput` structure that would
have the same fields as `GeometricBudgetSource` plus an `increment`-specific
property.

### Future pointwise-decay theorem shape

The meaningful next Lean theorem is not another budget constructor.  It is a
future lemma that turns first-band and uniform-decay hypotheses into `hgeom`.

Candidate shape:

```lean
theorem pointwiseGeometricMajorant_of_firstBand_decay
    (K : Nat)
    (increment : Nat -> Rat)
    (base ratio : Rat)
    (hbase0 : increment 0 <= base)
    (hdecay :
      forall k in Finset.range K,
        increment (k + 1) <= ratio * increment k)
    (hinc_nonneg :
      forall k in Finset.range (K + 1), 0 <= increment k)
    (hr0 : 0 <= ratio) :
    forall k in Finset.range (K + 1),
      increment k <= base * ratio^k
```

This theorem may need careful indexing and algebraic side conditions.  It
should be reviewed before implementation.

### Why not add a structure now

A structure such as:

```lean
structure FirstBandDecayBudgetInput where
  base : Rat
  ratio : Rat
  error : Real
  ...
```

would duplicate `GeometricBudgetSource`.

The actual new content is not another package of `base`, `ratio`, and `error`;
it is the derivation of pointwise geometric control from first-band and decay
assumptions.

### Recommended next step

The next step should review the theorem shape for:

```text
first-band bound + uniform step decay
  -> hgeom
```

before adding Lean code.  In particular, it should check:

- whether `hdecay` should range over `Finset.range K` or all `k < K`;
- whether `hr0 : 0 <= ratio` is enough;
- whether `hinc_nonneg` is needed in the induction proof;
- whether the theorem should be stated over `Rat` only or later generalized.

### Non-goals

DKMK-016J does not add:

- Lean code;
- a new structure;
- an analytic budget theorem;
- Mertens or big-O;
- logarithmic thresholds;
- real-to-Nat rounding;
- a provider wrapper.

### Verification

DKMK-016J is docs-only.  It was checked with:

```text
git diff --check
long-line check on changed docs
```
