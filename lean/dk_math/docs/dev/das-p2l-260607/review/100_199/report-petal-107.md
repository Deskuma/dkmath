# Report Petal 107: Pressure Profile

## Summary

Checkpoint 107 implements the pressure-profile layer requested by
`__next_implementation-107.md`.

Checkpoint 106 proved the local pressure conversion:

```text
ContinuationOutrunsRecovery
  -> MoreThanHalf continuation retention
```

Checkpoint 107 packages that statement across a finite depth range and adds a
small depth-mode counting experiment.

## Lean Additions

Implemented in:

```text
lean/dk_math/DkMath/Collatz/PetalBridge.lean
```

Generic range predicate:

```lean
MoreThanHalfOnRange
```

Source and tail continuation pressure profiles:

```lean
SourceContinuationPressureOnRange
TailContinuationPressureOnRange
```

Failure-range to pressure-profile bridges:

```lean
sourceContinuationPressure_of_outRunsOnRange
tailContinuationPressure_of_outRunsOnRange
```

Profile extraction theorems:

```lean
moreThanHalf_of_sourceContinuationPressure
moreThanHalf_of_tailContinuationPressure
```

Additional experiment: pressure depth counts:

```lean
sourceContinuationPressureDepthCount
tailContinuationPressureDepthCount
sourceContinuationPressureDepthCount_eq_len_of_pressureOnRange
tailContinuationPressureDepthCount_eq_len_of_pressureOnRange
```

The count experiment passed without `sorry`.

## Mathematical Result

The new route is:

```text
ContinuationOutrunsRecoveryOnRange
  -> SourceContinuationPressureOnRange
  -> sourceContinuationPressureDepthCount = len
```

and similarly:

```text
TailContinuationOutrunsRecoveryOnRange
  -> TailContinuationPressureOnRange
  -> tailContinuationPressureDepthCount = len
```

This converts a prolonged failure range into a finite depth-mode object.

The important distinction is:

```text
window residue counts:
  count orbit labels inside one residue channel

pressure depth counts:
  count depths where the local branch is pressure
```

Thus the implementation has moved from mass distribution inside a fixed depth
to mode distribution across depths.

## Documentation Updates

Updated:

```text
lean/dk_math/DkMath/Collatz/README.md
lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
```

Added:

```text
lean/dk_math/DkMath/Collatz/docs/Collatz-PressureProfile-107.md
```

## Additional Inference

Checkpoint 107 suggests that the next useful object is a mixed depth-mode
distribution.

At each depth, checkpoint 106 gives:

```text
RecoveryDominatesContinuation
or
ContinuationOutrunsRecovery
```

Therefore a finite range should be decomposable into:

```text
controlled depths
pressure depths
```

The expected next target is:

```lean
noncomputable def sourceContinuationControlledDepthCount ...
noncomputable def sourceContinuationPressureDepthCount ...
```

with a theorem of the shape:

```text
controlledDepthCount + pressureDepthCount = len
```

This is the depth-mode analogue of the checkpoint 100 source distribution
theorem:

```text
sum of residue channel counts = window size
```

The difference is that the new distribution is over modes across depths, not
over residues across orbit labels.

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

The first targeted build passed after one repair:

```text
pressure depth count definitions needed explicit classical decidability
around decide (MoreThanHalf ...)
```

Known upstream warning:

```text
DkMath.NumberTheory.ZsigmondyCyclotomicResearch.lean declares a theorem using sorry
```

This warning is outside the Collatz `PetalBridge` checkpoint.

## Next Implementation Candidate

Proceed to mixed pressure/control depth counts.

Suggested minimal surface:

```lean
noncomputable def sourceContinuationControlledDepthCount
    (n : OddNat) (k r len : ℕ) : ℕ := ...

noncomputable def tailContinuationControlledDepthCount
    (n : OddNat) (k r len : ℕ) : ℕ := ...
```

Then prove a partition theorem:

```text
controlledDepthCount + pressureDepthCount = len
```

The likely proof route is induction on `len`, using the local dichotomy:

```lean
recoveryDominates_or_continuationOutruns
tailRecoveryDominates_or_tailContinuationOutruns
```

This should stay finite and `Nat`-valued.
