# DKMK-018: Analytic Source Replacement

DKMK-018 starts after DKMK-017 closed the route-validation chapter.

DKMK-017 proved that a concrete `Nat -> Rat` source can travel through:

```text
TruncationEnvelopeEstimate
  -> finiteStepTailNatMassSpace
  -> quotient-path weightedHitMass bound
```

The test source was:

```lean
geometricIncrement base ratio : Nat -> Rat
```

It is now accepted as a route-validation source, not as the final analytic
source.

## 1. Chapter Goal

Replace the toy geometric source with a meaningful analytic source candidate.

Candidate directions:

```text
logarithmic source
capacity-derived source
dyadic band mass estimate
quotient-path local decay source
```

The key question is:

```text
what can replace geometricIncrement while still feeding the DKMK-017 route?
```

## 2. DKMK-018A Candidate Surface Survey

DKMK-018A searched the existing PrimitiveSet code for analytic source surfaces
near log, capacity, quotient-path, and dyadic-band routes.

### Existing surfaces

The closest existing candidates are:

1. Real log-ratio route:
   - `RealLog.lean`
   - `RealLogBudget`
   - `RealLogProductBudget`
   - `realLogRatioWeightProvider`
   - `realLogRatioWeightProvider_subProbability`
2. Multiplicity / valuation budget route:
   - `ValuationBudget.lean`
   - `NatBaseMultiplicityBudgetOn`
   - `realLogProductBudget_of_multiplicityBudget`
   - `realLogRatioWeightProvider_subProbability_of_multiplicityBudget`
3. Capacity-derived route:
   - `LogCapacityKernel.lean`
   - `PrimePowerWitnessProvider.logCapacityKernel`
   - `logCapacityKernel_normalized_subProbability`
   - `logCapacityKernelRealWeightProvider`
4. DKMK-017 dyadic route:
   - `SourceMassTruncation.lean`
   - `geometricIncrement`
   - `TruncationEnvelopeEstimate`
   - `finiteStepTailNatMassSpace`

### Main type gap

The meaningful analytic candidates are currently Real-valued:

```text
Real.log (p : Real) / Real.log (n : Real)
RealWeightProvider
CapacityKernel.normalizedWeight
```

The DKMK-017 route consumes rational increments:

```text
increment : Nat -> Rat
finiteStepTailNatMassSpace ... increment
TruncationEnvelopeEstimate ... increment error
```

Therefore the immediate obstacle is not nonnegativity or sub-probability.
Those already exist on the Real side.  The obstacle is the bridge:

```text
Real analytic weight
  -> Rat finite-step increment
```

or a controlled generalization of the finite-step route to Real increments.

### Candidate ranking

Recommended first candidate:

```text
Real log-ratio / capacity-derived source
```

Reason:

- it already has nonnegativity and sub-probability lemmas;
- it is tied to prime-power witnesses and log-capacity kernels;
- it is mathematically meaningful for Erdos #1196;
- it exposes the real DKMK-018 type problem directly.

Not recommended as the next first target:

- more `geometricIncrement` wrappers;
- another toy rational source;
- a full Real-valued finite-step mass refactor before checking the smaller
  bridge surface.

### First Lean surface to try

The next checkpoint should test a small bridge interface, not a full refactor.

Candidate shape:

```text
RealAnalyticIncrementEnvelope
  realIncrement : Nat -> Real
  ratIncrement  : Nat -> Rat
  compare       : forall k, (ratIncrement k : Real) <= realIncrement k
  rat_nonneg    : forall k, 0 <= ratIncrement k
  real_budget   : finite real sum <= 1 + error
```

This keeps `finiteStepTailNatMassSpace` rational-valued while letting Real log
analysis supply an upper envelope.

The first Lean experiment should answer:

```text
Can a Real-valued analytic majorant certify the existing Rat increment route?
```

If yes, DKMK-018 can avoid a large Real-mass refactor.  If no, the chapter
should explicitly decide whether to generalize finite-step mass from `Rat` to
`Real`.

### Decision

DKMK-018A is discovery and planning.

The next implementation bundle should test the smallest Real-majorant bridge
around `TruncationEnvelopeEstimate` or `DyadicBandAnalyticEstimate`, while
preserving the existing rational finite-step mass route.

### Verification

DKMK-018A is docs-only.  It was checked with:

```text
git diff --check
long-line check on changed docs
```

## 3. DKMK-018B Real-Majorant Bridge

DKMK-018B tested whether a Real-valued analytic majorant can certify the
existing rational finite-step route.

### Lean additions

Added to `SourceMassTruncation.lean`:

- `TruncationEnvelopeEstimate.ofRealMajorant`
- `TruncationEnvelopeEstimate.ofRealWeightProviderMajorant`
- `DyadicBandAnalyticEstimate.ofRealMajorant`

### Result

The bridge is accepted.

For a finite step set, the route now accepts:

```text
increment : i -> Rat
majorant  : i -> Real

forall i in steps, 0 <= increment i
forall i in steps, (increment i : Real) <= majorant i
sum majorant <= 1 + error
```

and produces:

```text
TruncationEnvelopeEstimate steps threshold increment error
```

The dyadic-band version also closes:

```text
DyadicBandAnalyticEstimate x K increment error
```

from a Real-valued majorant over `Finset.range (K + 1)`.

### Provider bridge

DKMK-018B also implemented the next bridge surface toward DKMK-018C:

```text
RealWeightProvider
+ pointwise majorization of a Rat increment
+ provider SubProbability
+ 0 <= error
  -> TruncationEnvelopeEstimate
```

This means `logCapacityKernelRealWeightProvider` can be used in the next
checkpoint as a Real source, provided a rational increment is chosen below its
weights.

### Interpretation

The large Real-native finite-step refactor is not needed yet.

The existing rational finite-step mass route can remain in place while Real
analysis supplies an upper envelope.

### Decision

Adopt the Real-majorant bridge.

The next checkpoint should attach an actual Real log/capacity source, starting
with:

```text
PrimePowerWitnessProvider.logCapacityKernelRealWeightProvider
```

or another `RealWeightProvider` from the Real log-ratio route.

### Verification

DKMK-018B was checked with:

```text
lake build DkMath.NumberTheory.PrimitiveSet.SourceMassTruncation
lake build DkMath.NumberTheory.PrimitiveSet
git diff --check
long-line check on changed docs
```
