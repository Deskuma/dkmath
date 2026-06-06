# DKMK-019: report

DKMK-019 is the LogCapacity source facade chapter.

DKMK-018 closed the first analytic source replacement route:

```text
LogCapacityKernel Real provider
  -> positive Rat under-approximation
  -> TruncationEnvelopeEstimate
  -> finiteStepTailNatMassSpace
  -> quotient-path weightedHitMass bound
```

The remaining problem was not mathematical.  The route was correct, but the
caller-facing theorem still exposed a long construction chain.

DKMK-019 packages that route into named source, mass, and path-family surfaces.

## 1. Starting Point

The accepted DKMK-018 endpoint was:

```lean
PrimePowerWitnessProvider
  .logCapacityKernel_finiteStepTail_weightedHitMass_le_one_add_error
```

It proved the desired bound, but its type exposed:

```text
s.1
IOf s.1
logCapacityKernelRealWeightProvider
logCapacityKernelRealWeightProvider_weight_pos
RealWeightProvider.positiveRatIncrementBelow
finiteStepTailNatMassSpace_dvdMonotone
globalLogCapacityKernel_applyAtToPrimePowerQuotientPathFamily
```

DKMK-019 set out to preserve the route while shortening that public surface.

## 2. Source Facade

DKMK-019B introduced the first facade bundle:

```lean
PrimePowerWitnessProvider.logCapacitySourceRatIncrement
PrimePowerWitnessProvider.logCapacitySourceTruncationEnvelope
PrimePowerWitnessProvider.logCapacitySourceFiniteStepMass
PrimePowerWitnessProvider.logCapacitySourceFiniteStepMass_dvdMonotone
PrimePowerWitnessProvider.logCapacitySource_weightedHitMass_le_one_add_error
```

This changed the reading from an exposed rational-selection expression to:

```text
logCapacitySourceRatIncrement W IOf hIOf s
logCapacitySourceTruncationEnvelope W IOf hIOf s threshold herror
logCapacitySourceFiniteStepMass W IOf hIOf s threshold
```

The mathematics remained the DKMK-018 route.  The change was API-facing.

## 3. Path-Family Facade

DKMK-019C then hid the remaining quotient-path construction:

```lean
PrimePowerWitnessProvider.logCapacitySourcePathFamily
PrimePowerWitnessProvider
  .logCapacitySourcePathFamily_weightedHitMass_le_one_add_error
```

The final theorem now reads with a path-family subject:

```text
(W.logCapacitySourcePathFamily IOf hIOf s threshold).weightedHitMass A
  <= 1 + error
```

This is the desired caller-facing form for the DKMK-018 endpoint.

## 4. Final Facade Stack

The completed stack is:

```text
logCapacitySourceRatIncrement
  -> logCapacitySourceTruncationEnvelope
  -> logCapacitySourceFiniteStepMass
  -> logCapacitySourcePathFamily
  -> weightedHitMass bound
```

Each layer is a thin wrapper around an already accepted route component.

## 5. Decision

DKMK-019 is complete as a facade chapter.

It answers the chapter question:

```text
Can the accepted DKMK-018 analytic source route be exposed through a stable
LogCapacity source API?
```

Answer:

```text
Yes.  The route can now be called through named source, mass, and path-family
facades, ending in a short weightedHitMass theorem.
```

## 6. Non-Goals

DKMK-019 did not add:

```text
new analytic estimates
new source families
Mertens theorem
big-O route
threshold optimization
support-filter policy
Real-native finite-step mass refactor
```

Those remain later branches.

## 7. Next Branch

The preferred next chapter is DKMK-020.

Two directions are natural:

```text
threshold/support policy
analytic source expansion
```

The threshold/support policy is the better first candidate because DKMK-019
now gives a stable facade for the current source route.  Expanding sources
before deciding the support policy would likely duplicate caller-facing API
decisions.
