# Collatz Cause-Side Depth Distribution 111

## Purpose

Checkpoint 111 completes the second presentation of the finite depth-mode
distribution in `DkMath.Collatz.PetalBridge`.

The previous checkpoints already had the descriptive distribution:

```text
controlledDepthCount + pressureDepthCount = len
```

where the two modes are written with finite ratio predicates:

```text
AtMostHalf
MoreThanHalf
```

Checkpoint 110 connected the failure side to its cause-side predicate:

```text
ContinuationOutrunsRecovery = MoreThanHalf continuation
```

Checkpoint 111 adds the matching dominance side:

```text
RecoveryDominatesContinuation = AtMostHalf continuation
```

and then counts it over a depth range.

## New Count Objects

The new source count is:

```lean
sourceRecoveryDominanceDepthCount
```

It counts depths in `[r, r + len)` where:

```lean
RecoveryDominatesContinuation n k depth
```

The shifted-tail version is:

```lean
tailRecoveryDominanceDepthCount
```

It counts depths where:

```lean
TailRecoveryDominatesContinuation n k depth
```

These are cause-side counts.  They do not mention `AtMostHalf` directly.

## Local Equivalence

The local source equivalence is:

```lean
recoveryDominates_iff_atMostHalf_continuation
```

The local shifted-tail equivalence is:

```lean
tailRecoveryDominates_iff_atMostHalf_tailContinuation
```

These theorems close the local reading:

```text
RecoveryDominatesContinuation
  <-> continuation is at most half of retention

TailRecoveryDominatesContinuation
  <-> tail continuation is at most half of tail retention
```

This is the controlled-side analogue of the checkpoint 110 pressure/failure
equivalence.

## Count Equality

The local equivalences lift to range counts:

```lean
sourceRecoveryDominanceDepthCount_eq_controlledDepthCount
tailRecoveryDominanceDepthCount_eq_controlledDepthCount
```

Thus the controlled count can be read in two ways:

```text
descriptive:
  AtMostHalf depths

cause-side:
  recovery-dominates-continuation depths
```

This matters because later arguments may produce either kind of evidence.  A
ratio-budget proof can use the descriptive side, while a structural comparison
proof can use the cause-side version.

## Cause-Side Partition

The final checkpoint 111 theorems are:

```lean
sourceCauseSideDepthCount_add_eq_len
tailCauseSideDepthCount_add_eq_len
```

They state:

```text
dominanceDepthCount + outrunsDepthCount = len
```

This is not a new induction.  It is obtained by rewriting the existing
descriptive partition:

```text
controlledDepthCount + pressureDepthCount = len
```

through the two bridge equalities:

```text
dominanceDepthCount = controlledDepthCount
outrunsDepthCount = pressureDepthCount
```

## Mathematical Reading

The finite depth range now has a completed two-face interpretation.

Descriptive face:

```text
AtMostHalf mode
MoreThanHalf mode
```

Cause-side face:

```text
RecoveryDominatesContinuation
ContinuationOutrunsRecovery
```

The first face is useful for finite budget and frequency language.  The second
face is useful for mechanism language: which local comparison caused the
budget mode.

This checkpoint does not prove that pressure is rare.  It proves that the
question can be asked equivalently on either side.

## Next Candidate

The next natural surface is cause-side frequency.  Checkpoint 109 introduced
frequency predicates for the descriptive pressure count:

```lean
SourcePressureAtMostHalfOnDepthRange
SourcePressureMoreThanHalfOnDepthRange
TailPressureAtMostHalfOnDepthRange
TailPressureMoreThanHalfOnDepthRange
```

Since checkpoint 110 proved:

```text
outrunsDepthCount = pressureDepthCount
```

we can add cause-side aliases such as:

```lean
SourceOutrunsAtMostHalfOnDepthRange
SourceOutrunsMoreThanHalfOnDepthRange
TailOutrunsAtMostHalfOnDepthRange
TailOutrunsMoreThanHalfOnDepthRange
```

and bridge them back to the existing pressure-frequency predicates.

That would make the next checkpoint a thin API layer rather than another
counting induction.
