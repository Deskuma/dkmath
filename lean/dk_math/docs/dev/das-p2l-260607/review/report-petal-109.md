# Report Petal 109: Depth-Pressure Frequency

## Summary

Checkpoint 109 implements depth-pressure frequency witnesses.

Checkpoint 108 closed:

```text
controlledDepthCount + pressureDepthCount = len
```

Checkpoint 109 applies `AtMostHalf` and `MoreThanHalf` to the pressure depth
count itself, still entirely as finite `Nat` inequalities.

## Lean Additions

Implemented in:

```text
lean/dk_math/DkMath/Collatz/PetalBridge.lean
```

Frequency predicates:

```lean
SourcePressureAtMostHalfOnDepthRange
SourcePressureMoreThanHalfOnDepthRange
TailPressureAtMostHalfOnDepthRange
TailPressureMoreThanHalfOnDepthRange
```

Frequency dichotomy:

```lean
sourcePressureAtMostHalf_or_moreThanHalfOnDepthRange
tailPressureAtMostHalf_or_moreThanHalfOnDepthRange
```

At-most-half frequency as count comparison:

```lean
sourcePressureDepthCount_le_controlled_of_atMostHalf
sourcePressureAtMostHalf_of_pressureDepthCount_le_controlled
tailPressureDepthCount_le_controlled_of_atMostHalf
tailPressureAtMostHalf_of_pressureDepthCount_le_controlled
```

More-than-half frequency as count comparison:

```lean
sourceControlledDepthCount_lt_pressure_of_pressureMoreThanHalf
sourcePressureMoreThanHalf_of_controlledDepthCount_lt_pressure
tailControlledDepthCount_lt_pressure_of_pressureMoreThanHalf
tailPressureMoreThanHalf_of_controlledDepthCount_lt_pressure
```

Additional local reverse-pressure experiment:

```lean
continuationOutruns_of_moreThanHalf_continuation
tailContinuationOutruns_of_moreThanHalf_tailContinuation
```

The reverse local direction passed without `sorry`.

## Mathematical Result

The depth range can now be read in three layers:

```text
1. local mode:
   AtMostHalf or MoreThanHalf

2. mixed distribution:
   controlledDepthCount + pressureDepthCount = len

3. frequency:
   pressureDepthCount is at most half or more than half of len
```

Using the mixed distribution:

```text
2 * pressureDepthCount <= len
```

is equivalent to:

```text
pressureDepthCount <= controlledDepthCount
```

and:

```text
len < 2 * pressureDepthCount
```

is equivalent to:

```text
controlledDepthCount < pressureDepthCount
```

This is the desired finite pressure-frequency surface.

## Additional Inference

Checkpoint 109 also closes the reverse local direction:

```text
MoreThanHalf continuation retention
  -> ContinuationOutrunsRecovery
```

The forward direction already existed from checkpoint 106:

```text
ContinuationOutrunsRecovery
  -> MoreThanHalf continuation retention
```

Therefore source/tail local pressure and outruns modes are now interderivable.

This suggests the next checkpoint:

```text
outruns-depth count = pressure-depth count
```

The pressure count currently counts `MoreThanHalf`.  A new cause-side count
could count `ContinuationOutrunsRecovery`.  Local equivalence should allow
their equality over the same depth range.

## Documentation Updates

Updated:

```text
lean/dk_math/DkMath/Collatz/README.md
lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
```

Added:

```text
lean/dk_math/DkMath/Collatz/docs/Collatz-DepthPressureFrequency-109.md
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

Proceed to cause-side failure counts.

Suggested minimal surface:

```lean
noncomputable def sourceContinuationOutrunsDepthCount
    (n : OddNat) (k r len : ℕ) : ℕ := ...

noncomputable def tailContinuationOutrunsDepthCount
    (n : OddNat) (k r len : ℕ) : ℕ := ...
```

Then prove:

```text
sourceContinuationOutrunsDepthCount = sourceContinuationPressureDepthCount
tailContinuationOutrunsDepthCount = tailContinuationPressureDepthCount
```

This would connect the descriptive pressure mode back to the cause-side
failure predicate.
