# DKMK-020: Threshold / Support Policy

DKMK-020 starts after DKMK-019 completed the LogCapacity source facade.

The accepted DKMK-019 endpoint is:

```lean
PrimePowerWitnessProvider
  .logCapacitySourcePathFamily_weightedHitMass_le_one_add_error
```

It exposes the weighted-hit route through a stable path-family subject:

```text
(W.logCapacitySourcePathFamily IOf hIOf s threshold).weightedHitMass A
  <= 1 + error
```

The remaining caller-facing input is:

```text
threshold : Nat -> Nat
```

DKMK-020 is the policy chapter for this threshold, and for the support choices
that determine where the LogCapacity source is allowed to act.

## 1. Chapter Goal

Create a stable threshold/support policy surface for the LogCapacity source
route.

The route should eventually read as:

```text
LogCapacity source at state s
  -> named threshold/support policy
  -> logCapacitySourcePathFamily
  -> weightedHitMass bound
```

without forcing callers to supply an arbitrary anonymous `Nat -> Nat` at the
final theorem boundary.

## 2. Current Friction

DKMK-019 successfully hides:

```text
positiveRatIncrementBelow (...)
finiteStepTailNatMassSpace (...)
globalLogCapacityKernel_applyAtToPrimePowerQuotientPathFamily (...)
```

but it still leaves `threshold` fully external.

That is useful for route validation, but not yet a public policy.

The next problem is not:

```text
prove a sharper analytic estimate
```

The next problem is:

```text
which support and threshold data should become the named public input?
```

## 3. Policy Questions

DKMK-020 should separate three decisions.

### Support set

The current route uses:

```text
IOf s.1 : Finset Nat
```

The support policy should decide whether the public surface keeps this as an
external family or packages a canonical support for each state.

### Threshold map

The current route accepts:

```text
threshold : Nat -> Nat
```

The threshold policy should decide whether to introduce:

```lean
PrimePowerWitnessProvider.logCapacitySourceThreshold
```

or a small structure packaging a support family and threshold map together.

### Compatibility predicate

A named policy may need to record that thresholds are only relevant on the
selected support:

```text
q in IOf s.1
```

The first Lean bundle should test whether such compatibility is needed now, or
whether it would only add unused assumptions.

## 4. Preferred First Surface

The first implementation target should be intentionally thin.

Candidate:

```lean
structure LogCapacitySourcePolicy
    (T : PrimePowerDivisorTransitionKernel) where
  IOf : Nat -> Finset Nat
  hIOf :
    forall n q, q in IOf n -> q in T.toDivisorTransitionKernel.index n
  threshold : Nat -> Nat
```

Then add wrapper names:

```lean
PrimePowerWitnessProvider.logCapacityPolicyPathFamily
PrimePowerWitnessProvider
  .logCapacityPolicyPathFamily_weightedHitMass_le_one_add_error
```

The intended theorem conclusion is:

```text
(W.logCapacityPolicyPathFamily P s).weightedHitMass A <= 1 + error
```

This keeps the existing mathematics unchanged while moving the public API from
three loose inputs:

```text
IOf, hIOf, threshold
```

to one named policy input:

```text
P : LogCapacitySourcePolicy T
```

## 5. Why Not Source Expansion First

DKMK-019 already produced a stable facade for the current source.  Adding more
sources before choosing the threshold/support policy would likely duplicate the
same public API decision for every source.

Therefore DKMK-020 should first settle the policy surface.  Analytic source
expansion should become a later chapter once the policy boundary is stable.

## 6. First Implementation Target

DKMK-020A is analysis and roadmap setup.

DKMK-020B should test:

```lean
structure LogCapacitySourcePolicy
```

and thin wrappers over the DKMK-019 endpoint.

The expected Lean work is local:

```text
unpack P.IOf
unpack P.hIOf
unpack P.threshold
call logCapacitySourcePathFamily
call logCapacitySourcePathFamily_weightedHitMass_le_one_add_error
```

No new analytic proof should be required.

## 7. Non-Goals

DKMK-020 should not start:

```text
Mertens theorem
big-O route
new source families
threshold optimization
Real-native finite-step mass refactor
new asymptotic support theorem
```

This chapter is a policy/API chapter.  It should only add mathematical
assumptions if Lean shows they are necessary for the named policy surface.

## 8. Verification Plan

For Lean bundles:

```text
lake build DkMath.NumberTheory.PrimitiveSet.SourceMassTruncation
lake build DkMath.NumberTheory.PrimitiveSet
git diff --check
long-line check on changed docs
```

For this docs-only setup:

```text
git diff --check
long-line check on changed docs
```
