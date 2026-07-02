# Report Petal 105

## Summary

Checkpoint 105 introduced comparison-condition predicates for the Collatz
Petal finite mass calculus.

The goal was not to prove unconditional contraction.  The goal was to name the
missing local comparison that would imply contraction-like `AtMostHalf`
statements.

## Implemented Lean Surface

Local comparison predicates:

```lean
RecoveryDominatesContinuation
TailRecoveryDominatesContinuation
```

Budget coverage predicates:

```lean
RecoveryCoversHalfRetention
TailRecoveryCoversHalfRetention
```

Finite range predicates:

```lean
RecoveryDominatesOnRange
TailRecoveryDominatesOnRange
```

Predicate-facing half criteria:

```lean
atMostHalf_continuation_of_recoveryDominates
atMostHalf_tailContinuation_of_tailRecoveryDominates
atMostHalf_continuation_of_recoveryCoversHalf
atMostHalf_tailContinuation_of_tailRecoveryCoversHalf
```

Range extraction theorems:

```lean
atMostHalf_continuation_of_recoveryDominatesOnRange
atMostHalf_tailContinuation_of_tailRecoveryDominatesOnRange
```

Failure-mode predicates:

```lean
ContinuationOutrunsRecovery
TailContinuationOutrunsRecovery
ContinuationOutrunsRecoveryOnRange
TailContinuationOutrunsRecoveryOnRange
```

## Mathematical Reading

The current finite calculus is:

```text
M = R + K
K <= R -> 2K <= M
```

Checkpoint 105 turns `K <= R` into a named hypothesis:

```text
RecoveryDominatesContinuation
```

and turns the range form into:

```text
RecoveryDominatesOnRange
```

This makes the next gap precise:

```text
what structural observation proves RecoveryDominatesContinuation?
```

## Docs Updated

Updated:

```text
lean/dk_math/DkMath/Collatz/README.md
lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
```

Added:

```text
lean/dk_math/DkMath/Collatz/docs/Collatz-ComparisonPredicates-105.md
```

## Verification

Passed:

```text
lake build DkMath.Collatz.PetalBridge
```

No new `sorry` was introduced in `DkMath.Collatz.PetalBridge`.

Known upstream warning remains unchanged:

```text
DkMath.NumberTheory.ZsigmondyCyclotomicResearch.lean:152:6:
declaration uses `sorry`
```

## Additional Inference

This checkpoint makes the future proof obligation sharper.

Before 105, the missing step was vague:

```text
show contraction
```

After 105, the missing step is a named bridge:

```text
structural observation -> RecoveryDominatesContinuation
```

or:

```text
structural observation -> RecoveryCoversHalfRetention
```

## Next Candidate

The obstruction-style predicate for the opposite case was small enough to add
in this checkpoint:

```text
ContinuationOutrunsRecovery
```

If recovery does not dominate, then continuation is strictly larger than
recovery.  Naming that failure mode would give the False/obstruction path a
target:

```text
ContinuationOutrunsRecovery on a range
  -> address pressure / height drift / collision pressure
```

This fits the current project style: prove truth where possible, and name the
failure condition when the proof needs another structure.

The next checkpoint can now try to attach a first weak consequence to
`ContinuationOutrunsRecoveryOnRange`, probably not a contradiction yet, but an
accumulated pressure statement over the finite range.
