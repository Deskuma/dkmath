# Report Petal 108: Mixed Depth-Mode Distribution

## Summary

Checkpoint 108 implements the mixed depth-mode distribution requested by
`__next_implementation-108.md`.

Checkpoint 107 introduced pressure depth counts.  Checkpoint 108 adds the
controlled side and proves:

```text
controlled depth count + pressure depth count = len
```

for both the source and shifted-tail windows.

## Lean Additions

Implemented in:

```text
lean/dk_math/DkMath/Collatz/PetalBridge.lean
```

Controlled depth counts:

```lean
sourceContinuationControlledDepthCount
tailContinuationControlledDepthCount
```

Depth-count bounds:

```lean
sourceContinuationPressureDepthCount_le_len
tailContinuationPressureDepthCount_le_len
sourceContinuationControlledDepthCount_le_len
tailContinuationControlledDepthCount_le_len
```

Mixed distribution theorems:

```lean
sourceContinuationControlledDepthCount_add_pressureDepthCount_eq_len
tailContinuationControlledDepthCount_add_pressureDepthCount_eq_len
```

The final partition theorems passed without `sorry`.

## Mathematical Result

At each depth, the local finite split is:

```text
AtMostHalf continuation retention
or
MoreThanHalf continuation retention
```

Checkpoint 108 counts these modes across a finite depth interval:

```text
[r, r + len)
```

The resulting conservation law is:

```text
controlledDepthCount + pressureDepthCount = len
```

This is the depth-mode analogue of checkpoint 100:

```text
sum of residue channel counts = window size
```

The new distribution is not over orbit labels.  It is over depth positions.

## Implementation Note

An initial attempt exposed indicator theorems with theorem statements of the
form:

```lean
if AtMostHalf ... then 1 else 0
```

and later:

```lean
if decide (AtMostHalf ...) then 1 else 0
```

That failed because the statement itself needed `Decidable` instances before
the proof body could introduce `classical`.

The working route keeps the final singleton indicator split inside the
partition proof.  There, `classical` is already available, and `by_cases`
handles the final depth directly.

This is worth remembering for later `countP`-based mixed profiles:

```text
avoid exposing Prop-valued if/decide indicators in theorem statements
unless a decidability surface is deliberately part of the API.
```

## Documentation Updates

Updated:

```text
lean/dk_math/DkMath/Collatz/README.md
lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
```

Added:

```text
lean/dk_math/DkMath/Collatz/docs/Collatz-MixedDepthModeDistribution-108.md
```

## Additional Inference

The useful next layer is pressure frequency over depth ranges.

Now that we have:

```text
controlledDepthCount + pressureDepthCount = len
```

we can reuse the finite ratio predicates:

```lean
AtMostHalf
MoreThanHalf
AtMostRatioNat
```

on the depth-mode counts themselves.

Candidate next statements:

```lean
AtMostHalf
  (sourceContinuationPressureDepthCount n k r len)
  len
```

or:

```lean
MoreThanHalf
  (sourceContinuationPressureDepthCount n k r len)
  len
```

These would say that pressure occupies at most half, or more than half, of the
depth range.  This remains finite and `Nat`-valued.

The obstruction route then becomes:

```text
too many pressure depths
  -> retention cylinder remains too dominant
  -> height drift / collision / carrier pressure must compensate
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

The targeted `DkMath.Collatz.PetalBridge` build passed after repairing the
indicator theorem approach described above.

Known upstream warning:

```text
DkMath.NumberTheory.ZsigmondyCyclotomicResearch.lean declares a theorem using sorry
```

This warning is outside the Collatz `PetalBridge` checkpoint.

## Next Implementation Candidate

Proceed to depth-pressure frequency witnesses.

Minimal API:

```lean
def SourcePressureAtMostHalfOnDepthRange
    (n : OddNat) (k r len : ℕ) : Prop :=
  AtMostHalf (sourceContinuationPressureDepthCount n k r len) len

def SourcePressureMoreThanHalfOnDepthRange
    (n : OddNat) (k r len : ℕ) : Prop :=
  MoreThanHalf (sourceContinuationPressureDepthCount n k r len) len
```

Add tail counterparts and thin projection/constructor theorems.  Do not move
to rational or real frequencies yet.
