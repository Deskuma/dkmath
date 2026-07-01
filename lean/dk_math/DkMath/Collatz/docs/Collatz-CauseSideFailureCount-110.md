# Collatz Cause-Side Failure Count 110

## Purpose

Checkpoint 109 made pressure frequency a finite `Nat` statement:

```text
pressureDepthCount is at most half or more than half of len
```

Checkpoint 110 connects that descriptive pressure count to the cause-side
failure predicate:

```text
ContinuationOutrunsRecovery
```

The point is to read a pressure count in two ways:

```text
descriptive side:
  MoreThanHalf continuation retention

cause side:
  continuation outruns recovery
```

## Cause-Side Counts

Source failure count:

```lean
sourceContinuationOutrunsDepthCount
```

Tail failure count:

```lean
tailContinuationOutrunsDepthCount
```

These count depths in `[r, r + len)` where the cause-side failure predicate
holds.

## Local Equivalence

Checkpoint 110 records the local equivalences:

```lean
continuationOutruns_iff_moreThanHalf_continuation
tailContinuationOutruns_iff_moreThanHalf_tailContinuation
```

The forward direction was already available from checkpoint 106:

```lean
moreThanHalf_continuation_of_continuationOutruns
moreThanHalf_tailContinuation_of_tailContinuationOutruns
```

The reverse direction was added at checkpoint 109:

```lean
continuationOutruns_of_moreThanHalf_continuation
tailContinuationOutruns_of_moreThanHalf_tailContinuation
```

## Count Equality

The main checkpoint theorem is:

```lean
sourceContinuationOutrunsDepthCount_eq_pressureDepthCount
```

and the shifted-tail counterpart:

```lean
tailContinuationOutrunsDepthCount_eq_pressureDepthCount
```

These say:

```text
cause-side failure count = descriptive pressure count
```

for the same finite depth range.

## Controlled-Side Reverse Direction

Checkpoint 110 also adds:

```lean
recoveryDominates_of_atMostHalf_continuation
tailRecoveryDominates_of_atMostHalf_tailContinuation
```

Together with the existing predicate-facing half criteria, the local controlled
mode is also interderivable:

```text
RecoveryDominatesContinuation
  <-> AtMostHalf continuation retention
```

Thus both branches now have aligned readings:

```text
controlled:
  RecoveryDominatesContinuation
  <-> AtMostHalf continuation retention

pressure:
  ContinuationOutrunsRecovery
  <-> MoreThanHalf continuation retention
```

## Mathematical Reading

The depth-mode distribution now has two synchronized presentations:

```text
descriptive distribution:
  controlledDepthCount + pressureDepthCount = len

cause-side distribution:
  dominanceDepthCount + outrunsDepthCount = len
```

Checkpoint 110 closes the pressure/outruns side of the bridge:

```text
outrunsDepthCount = pressureDepthCount
```

The dominance/controlled count equality is the natural next target.

## Next Candidate

Define dominance depth counts:

```lean
sourceRecoveryDominanceDepthCount
tailRecoveryDominanceDepthCount
```

Then prove:

```text
sourceRecoveryDominanceDepthCount = sourceContinuationControlledDepthCount
tailRecoveryDominanceDepthCount = tailContinuationControlledDepthCount
```

After that, prove the cause-side partition:

```text
dominanceDepthCount + outrunsDepthCount = len
```

This would complete the double presentation of the depth-mode distribution.
