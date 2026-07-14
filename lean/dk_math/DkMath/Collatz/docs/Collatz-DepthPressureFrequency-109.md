# Collatz Depth-Pressure Frequency 109

## Purpose

Checkpoint 108 proved the mixed depth-mode distribution:

```text
controlledDepthCount + pressureDepthCount = len
```

Checkpoint 109 applies the finite half vocabulary to the pressure depth count
itself.

This lets us say, still in `Nat`:

```text
pressure depths are at most half of the depth range
pressure depths are more than half of the depth range
```

No rational or real frequency is introduced.

## Frequency Predicates

Source predicates:

```lean
SourcePressureAtMostHalfOnDepthRange
SourcePressureMoreThanHalfOnDepthRange
```

Tail predicates:

```lean
TailPressureAtMostHalfOnDepthRange
TailPressureMoreThanHalfOnDepthRange
```

These are thin wrappers around:

```lean
AtMostHalf pressureDepthCount len
MoreThanHalf pressureDepthCount len
```

## Frequency Dichotomy

The finite split is:

```lean
sourcePressureAtMostHalf_or_moreThanHalfOnDepthRange
tailPressureAtMostHalf_or_moreThanHalfOnDepthRange
```

Each depth range is therefore in one of two pressure-frequency modes:

```text
pressure occupies at most half
or
pressure occupies more than half
```

## Reading Through The Mixed Distribution

The partition from checkpoint 108 gives:

```text
controlledDepthCount + pressureDepthCount = len
```

Therefore:

```text
2 * pressureDepthCount <= len
```

is equivalent to:

```text
pressureDepthCount <= controlledDepthCount
```

The implemented directions are:

```lean
sourcePressureDepthCount_le_controlled_of_atMostHalf
sourcePressureAtMostHalf_of_pressureDepthCount_le_controlled
tailPressureDepthCount_le_controlled_of_atMostHalf
tailPressureAtMostHalf_of_pressureDepthCount_le_controlled
```

Similarly:

```text
len < 2 * pressureDepthCount
```

is equivalent to:

```text
controlledDepthCount < pressureDepthCount
```

The implemented directions are:

```lean
sourceControlledDepthCount_lt_pressure_of_pressureMoreThanHalf
sourcePressureMoreThanHalf_of_controlledDepthCount_lt_pressure
tailControlledDepthCount_lt_pressure_of_pressureMoreThanHalf
tailPressureMoreThanHalf_of_controlledDepthCount_lt_pressure
```

## Local Pressure And Outruns

Checkpoint 106 already proved:

```lean
moreThanHalf_continuation_of_continuationOutruns
moreThanHalf_tailContinuation_of_tailContinuationOutruns
```

Checkpoint 109 proves the reverse direction:

```lean
continuationOutruns_of_moreThanHalf_continuation
tailContinuationOutruns_of_moreThanHalf_tailContinuation
```

Thus the local modes are interderivable:

```text
ContinuationOutrunsRecovery
  <-> MoreThanHalf continuation retention
```

and similarly for the shifted-tail window.

## Mathematical Reading

The current finite hierarchy is:

```text
local depth:
  controlled or pressure

finite depth range:
  controlledDepthCount + pressureDepthCount = len

frequency layer:
  pressureDepthCount is at most half or more than half of len
```

This provides the first precise surface for saying:

```text
there are too many pressure depths
```

without introducing real-valued density.

## Next Candidate

The next natural checkpoint is to count the cause-side predicate:

```text
ContinuationOutrunsRecovery
```

over a depth range, then compare it with:

```text
MoreThanHalf pressure depth count
```

Since checkpoint 109 proves local equivalence in both directions, an
outruns-depth count should match the pressure-depth count if the same range and
window are used.

This would sharpen the pressure count from a descriptive mode count into a
cause-side failure count.
