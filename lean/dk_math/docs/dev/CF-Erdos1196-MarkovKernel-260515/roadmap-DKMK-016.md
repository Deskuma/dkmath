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
