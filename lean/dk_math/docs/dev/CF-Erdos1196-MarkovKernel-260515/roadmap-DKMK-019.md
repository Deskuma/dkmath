# DKMK-019: LogCapacity Source Facade

DKMK-019 starts after DKMK-018 completed the first analytic source replacement
route.

The accepted DKMK-018 endpoint is:

```lean
PrimePowerWitnessProvider
  .logCapacityKernel_finiteStepTail_weightedHitMass_le_one_add_error
```

It proves the desired weighted-hit bound, but its type exposes the full
construction:

```text
s.1
IOf s.1
logCapacityKernelRealWeightProvider
logCapacityKernelRealWeightProvider_weight_pos
RealWeightProvider.positiveRatIncrementBelow
finiteStepTailNatMassSpace_dvdMonotone
```

DKMK-019 is the API simplification chapter for this route.

## 1. Chapter Goal

Create a caller-facing façade for the log-capacity source replacement route.

The façade should make the route read as:

```text
LogCapacity source at state s
  -> finite-step mass space
  -> quotient-path weightedHitMass bound
```

without forcing callers to see the positive-rational selection expression.

## 2. Current Friction

The DKMK-018F theorem is mathematically right, but not caller-friendly.

The friction appears in two places.

### Increment expression

The rational source is currently written inline:

```text
RealWeightProvider.positiveRatIncrementBelow
  (logCapacityKernelRealWeightProvider s.1 (IOf s.1) ...)
  (logCapacityKernelRealWeightProvider_weight_pos s.1 (IOf s.1) ...)
```

This is correct, but it is too long to be a stable public source expression.

### Mass-space expression

The finite-step source mass space is also written inline:

```text
finiteStepTailNatMassSpace_dvdMonotone
  (IOf s.1)
  threshold
  increment
  increment_nonneg
```

This makes the theorem conclusion difficult to scan.

## 3. Preferred Surface

The first Lean bundle should introduce a small set of aliases and wrappers.

Candidate names:

```lean
PrimePowerWitnessProvider.logCapacitySourceRatIncrement
PrimePowerWitnessProvider.logCapacitySourceTruncationEnvelope
PrimePowerWitnessProvider.logCapacitySourceFiniteStepMass
PrimePowerWitnessProvider.logCapacitySource_weightedHitMass_le_one_add_error
```

The intended shape is:

```text
logCapacitySourceRatIncrement W IOf hIOf s : Nat -> Rat
```

then:

```text
logCapacitySourceTruncationEnvelope W IOf hIOf s threshold herror
```

and finally:

```text
logCapacitySource_weightedHitMass_le_one_add_error
```

with the conclusion expressed using `logCapacitySourceFiniteStepMass`.

## 4. First Implementation Target

DKMK-019A is analysis and roadmap setup.

DKMK-019B should test the smallest useful Lean surface:

```lean
noncomputable def logCapacitySourceRatIncrement
```

and then prove:

```lean
theorem logCapacitySourceTruncationEnvelope
```

If those close cleanly, the same bundle should also add:

```lean
def logCapacitySourceFiniteStepMass
theorem logCapacitySource_weightedHitMass_le_one_add_error
```

The theorem should be a thin wrapper over the accepted DKMK-018F theorem or
over `TruncationEnvelopeEstimate.finiteStepTail_weightedHitMass_le_one_add_error`.

## 5. Design Constraints

Do not change the route mathematics.

Keep these fixed:

```text
Real provider remains LogCapacityKernel-derived
Rat finite-step route remains the downstream route
positive rational under-approximation remains noncomputable
error assumption remains 0 <= error
primitive target remains PrimitiveOn A
```

The façade should remove caller friction, not introduce a new source theory.

## 6. Non-goals

DKMK-019 should not start:

```text
new asymptotic analysis
Mertens theorem
big-O route
Real-native finite-step mass route
another analytic source family
threshold optimization
```

Those are later branches.

## 7. Verification Plan

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

## 8. DKMK-019B Facade Implementation

DKMK-019B implemented the first caller-facing façade bundle.

### Lean additions

Added to `SourceMassTruncation.lean`:

- `PrimePowerWitnessProvider.logCapacitySourceRatIncrement`
- `PrimePowerWitnessProvider.logCapacitySourceTruncationEnvelope`
- `PrimePowerWitnessProvider.logCapacitySourceFiniteStepMass`
- `PrimePowerWitnessProvider.logCapacitySourceFiniteStepMass_dvdMonotone`
- `PrimePowerWitnessProvider.logCapacitySource_weightedHitMass_le_one_add_error`

### Result

The full façade bundle is accepted.

The positive-rational source is now named:

```text
logCapacitySourceRatIncrement W IOf hIOf s
```

The truncation envelope is now exposed as:

```text
logCapacitySourceTruncationEnvelope W IOf hIOf s threshold herror
```

The finite-step mass-space layer is now named:

```text
logCapacitySourceFiniteStepMass W IOf hIOf s threshold
logCapacitySourceFiniteStepMass_dvdMonotone W IOf hIOf s threshold
```

The final caller-facing theorem is:

```text
logCapacitySource_weightedHitMass_le_one_add_error
```

Its conclusion mentions the façade monotonicity proof instead of the raw
`positiveRatIncrementBelow` expression.

### Interpretation

This does not change the mathematics of DKMK-018.

The change is API-facing:

```text
positiveRatIncrementBelow (...)      -> logCapacitySourceRatIncrement
finiteStepTailNatMassSpace (...)     -> logCapacitySourceFiniteStepMass
weighted-hit route wrapper           -> logCapacitySource_weightedHitMass...
```

The route now reads as a named log-capacity source rather than as an exposed
construction chain.

### Decision

Adopt this façade bundle as the DKMK-019B surface.

The next checkpoint should decide whether the façade is sufficiently short, or
whether a still higher-level theorem should hide the monotonicity proof name in
the weighted-hit conclusion.

### Verification

DKMK-019B was checked with:

```text
lake build DkMath.NumberTheory.PrimitiveSet.SourceMassTruncation
lake build DkMath.NumberTheory.PrimitiveSet
git diff --check
long-line check on changed docs
```

## 9. DKMK-019C Path-Family Facade

DKMK-019C added the final path-family façade layer.

### Lean additions

Added to `SourceMassTruncation.lean`:

- `PrimePowerWitnessProvider.logCapacitySourcePathFamily`
- `PrimePowerWitnessProvider.logCapacitySourcePathFamily_weightedHitMass_le_one_add_error`

### Result

The quotient-path application is now named as a log-capacity source path
family:

```text
logCapacitySourcePathFamily W IOf hIOf s threshold
```

The final weighted-hit theorem can now be read with the path family as the
subject:

```text
(W.logCapacitySourcePathFamily IOf hIOf s threshold).weightedHitMass A
  <= 1 + error
```

### Interpretation

This completes the caller-facing façade stack:

```text
logCapacitySourceRatIncrement
  -> logCapacitySourceTruncationEnvelope
  -> logCapacitySourceFiniteStepMass
  -> logCapacitySourcePathFamily
  -> weightedHitMass bound
```

The theorem no longer exposes the raw `positiveRatIncrementBelow` expression
or the raw quotient-path application in its final subject.

### Decision

Adopt `logCapacitySourcePathFamily` as the preferred caller-facing subject for
the DKMK-019 route.

The next checkpoint should decide whether DKMK-019 can be summarized as a
completed façade chapter.

### Verification

DKMK-019C was checked with:

```text
lake build DkMath.NumberTheory.PrimitiveSet.SourceMassTruncation
lake build DkMath.NumberTheory.PrimitiveSet
git diff --check
long-line check on changed docs
```
