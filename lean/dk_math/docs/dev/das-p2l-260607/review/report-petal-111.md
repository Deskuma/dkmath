# Report Petal 111

## Summary

Checkpoint 111 completes the dominance side of the cause-side depth
distribution in `DkMath.Collatz.PetalBridge`.

The previous checkpoint counted the failure side:

```text
ContinuationOutrunsRecovery
```

and proved that this count is the same as the descriptive pressure count:

```text
MoreThanHalf continuation
```

This checkpoint adds the matching dominance count:

```text
RecoveryDominatesContinuation
```

and proves that it is the same as the descriptive controlled count:

```text
AtMostHalf continuation
```

The result is a completed double presentation of the finite depth-mode
distribution.

## Lean Additions

New cause-side dominance counts:

```lean
sourceRecoveryDominanceDepthCount
tailRecoveryDominanceDepthCount
```

New local equivalences:

```lean
recoveryDominates_iff_atMostHalf_continuation
tailRecoveryDominates_iff_atMostHalf_tailContinuation
```

New count equalities:

```lean
sourceRecoveryDominanceDepthCount_eq_controlledDepthCount
tailRecoveryDominanceDepthCount_eq_controlledDepthCount
```

New cause-side partitions:

```lean
sourceCauseSideDepthCount_add_eq_len
tailCauseSideDepthCount_add_eq_len
```

## Mathematical Result

The descriptive distribution was already available:

```text
controlledDepthCount + pressureDepthCount = len
```

Checkpoint 110 gave:

```text
outrunsDepthCount = pressureDepthCount
```

Checkpoint 111 gives:

```text
dominanceDepthCount = controlledDepthCount
```

Therefore the cause-side distribution is now theorem-level:

```text
dominanceDepthCount + outrunsDepthCount = len
```

This makes the finite depth range readable in two synchronized ways:

```text
descriptive:
  AtMostHalf / MoreThanHalf

cause-side:
  RecoveryDominatesContinuation / ContinuationOutrunsRecovery
```

## Implementation Note

The first proof attempt used later aliases:

```lean
atMostHalf_continuation_of_recoveryDominates
atMostHalf_tailContinuation_of_tailRecoveryDominates
```

Those names occur later in the file, so the local equivalence was instead
proved from the earlier base theorems:

```lean
atMostHalf_continuation_of_continuation_le_recovery
atMostHalf_tailContinuation_of_tailContinuation_le_tailRecovery
```

This keeps the theorem order acyclic and avoids moving older API blocks.

## Documentation Updates

Updated:

```text
DkMath/Collatz/README.md
DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
```

Added:

```text
DkMath/Collatz/docs/Collatz-CauseSideDepthDistribution-111.md
```

## Verification

Passed:

```text
lake build DkMath.Collatz.PetalBridge
lake build DkMath.Collatz.Collatz2K26
rg -n "\bsorry\b" DkMath/Collatz/PetalBridge.lean
git diff --check
```

The no-sorry check returned no matches in `DkMath/Collatz/PetalBridge.lean`.

```text
Known upstream warning during the integration build:
DkMath.NumberTheory.ZsigmondyCyclotomicResearch.lean:152:6 uses sorry.
```

## Next Candidate

The next thin API layer is cause-side frequency.

Checkpoint 109 already has descriptive pressure-frequency predicates:

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

we can introduce cause-side aliases:

```lean
SourceOutrunsAtMostHalfOnDepthRange
SourceOutrunsMoreThanHalfOnDepthRange
TailOutrunsAtMostHalfOnDepthRange
TailOutrunsMoreThanHalfOnDepthRange
```

and bridge them to the existing pressure-frequency predicates by rewriting.

This should be a light checkpoint.  It should not require another count
induction.
