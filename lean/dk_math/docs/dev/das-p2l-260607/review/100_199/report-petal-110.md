# Report Petal 110: Cause-Side Failure Count

## Summary

Checkpoint 110 implements cause-side failure counts and proves that they equal
the descriptive pressure depth counts.

The key result is:

```text
sourceContinuationOutrunsDepthCount
  = sourceContinuationPressureDepthCount
```

and the shifted-tail counterpart.

## Lean Additions

Implemented in:

```text
lean/dk_math/DkMath/Collatz/PetalBridge.lean
```

Cause-side failure counts:

```lean
sourceContinuationOutrunsDepthCount
tailContinuationOutrunsDepthCount
```

Local equivalence between cause-side failure and descriptive pressure:

```lean
continuationOutruns_iff_moreThanHalf_continuation
tailContinuationOutruns_iff_moreThanHalf_tailContinuation
```

Count equality:

```lean
sourceContinuationOutrunsDepthCount_eq_pressureDepthCount
tailContinuationOutrunsDepthCount_eq_pressureDepthCount
```

Additional controlled-side reverse bridge:

```lean
recoveryDominates_of_atMostHalf_continuation
tailRecoveryDominates_of_atMostHalf_tailContinuation
```

All additions passed without `sorry`.

## Mathematical Result

Before this checkpoint, pressure depth count was a descriptive count:

```text
MoreThanHalf continuation retention
```

Checkpoint 110 proves it is also a cause-side failure count:

```text
ContinuationOutrunsRecovery
```

Thus pressure is no longer merely an observed mode.  It is synchronized with
the underlying comparison failure:

```text
continuation outruns recovery
```

Locally, both branches are now aligned:

```text
RecoveryDominatesContinuation
  <-> AtMostHalf continuation retention

ContinuationOutrunsRecovery
  <-> MoreThanHalf continuation retention
```

The source/tail pressure count equality then lifts the local equivalence to a
finite depth range.

## Implementation Note

The count equality was proved by induction on `len`.

At the successor step, the final singleton was handled by `by_cases` on the
cause-side predicate and then converted through:

```lean
continuationOutruns_iff_moreThanHalf_continuation
tailContinuationOutruns_iff_moreThanHalf_tailContinuation
```

This follows the same reliable pattern as checkpoint 108: keep `decide` and
`countP` indicator reasoning inside the proof body where `classical` is
available.

## Documentation Updates

Updated:

```text
lean/dk_math/DkMath/Collatz/README.md
lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
```

Added:

```text
lean/dk_math/DkMath/Collatz/docs/Collatz-CauseSideFailureCount-110.md
```

## Additional Inference

The next natural target is the controlled-side cause count.

The new controlled reverse bridge:

```lean
recoveryDominates_of_atMostHalf_continuation
```

and the existing forward bridge:

```lean
atMostHalf_continuation_of_recoveryDominates
```

show local equivalence between:

```text
RecoveryDominatesContinuation
```

and:

```text
AtMostHalf continuation retention
```

Therefore a dominance depth count should equal the controlled depth count.

Expected next surface:

```lean
sourceRecoveryDominanceDepthCount =
  sourceContinuationControlledDepthCount

tailRecoveryDominanceDepthCount =
  tailContinuationControlledDepthCount
```

After that, a cause-side partition should follow:

```text
dominanceDepthCount + outrunsDepthCount = len
```

## Verification

Commands run for this checkpoint:

```text
lake build DkMath.Collatz.PetalBridge
lake build DkMath.Collatz.Collatz2K26
rg -n "\bsorry\b" DkMath/Collatz/PetalBridge.lean
git diff --check -- <touched files>
```

Results:

```text
lake build DkMath.Collatz.PetalBridge: passed
lake build DkMath.Collatz.Collatz2K26: passed
rg sorry in DkMath/Collatz/PetalBridge.lean: no matches
git diff --check on touched files: passed
```

The targeted `DkMath.Collatz.PetalBridge` build passed before documentation
sync, and the integration build passed after documentation sync.

Known upstream warning:

```text
DkMath.NumberTheory.ZsigmondyCyclotomicResearch.lean declares a theorem using sorry
```

This warning is outside the Collatz `PetalBridge` checkpoint.

## Next Implementation Candidate

Proceed to dominance-side cause counts.

Minimal API:

```lean
noncomputable def sourceRecoveryDominanceDepthCount
    (n : OddNat) (k r len : ℕ) : ℕ := ...

noncomputable def tailRecoveryDominanceDepthCount
    (n : OddNat) (k r len : ℕ) : ℕ := ...
```

Then prove equality with the controlled counts and close the cause-side
partition.
