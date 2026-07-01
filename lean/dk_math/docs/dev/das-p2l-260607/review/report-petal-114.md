# Report Petal 114

## Summary

Checkpoint 114 tested the tail-facing height bridge from source continuation
mass.

The expected route was:

```text
continuation mass
  -> tail retention
  -> tail height >= 2
  -> sumS lower bound
```

The experiment found a correction:

```text
source continuation mass at parent depth 2
  -> tail retention depth 2
  -> tail exact height 1
```

So the direct extra-peeling bridge at this depth is false in the intended
direction.

## Lean Additions

Meaning-name aliases:

```lean
sourceContinuationMass_le_tailRetentionMass
sourceContinuationMass_le_tailSplitMass
```

Correct tail height bridge:

```lean
tailRetentionMass_depth_two_eq_heightCountEq_one
tailRetentionMass_depth_two_le_heightCountEq_one
sourceContinuationMass_depth_two_le_tailHeightCountEq_one
```

## Important Negative Finding

The review suggested testing:

```text
tail retention depth 1 or continuation depth zero
  -> tail residue mod4 = 1
  -> tail height >= 2
```

The actual residue arithmetic shows the safe nearby bridge is different:

```text
tail retention depth 2 = 3 mod 4 = exact height 1
```

Therefore this checkpoint does not add:

```lean
sumS_ge_window_add_sourceContinuationMass_depth_two
```

That statement would use the wrong tail height side.

## Mathematical Reading

The continuation-retention channel is a base-retention channel at this layer.
It preserves an exact height-one tail state rather than forcing extra peeling.

This is useful because it prevents a bad drift argument from entering the API.
The next extra-height bridge should instead look at:

```text
3 mod 8 delayed-peeling source
recovery sibling channels
deeper delayed continuation branches
```

## Documentation Updates

Updated:

```text
DkMath/Collatz/README.md
DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
```

Added:

```text
DkMath/Collatz/docs/Collatz-TailFacingHeightBridge-114.md
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

The next checkpoint should inspect a recovery-side extra-height bridge.

Candidate:

```text
source recovery sibling mass
  -> tail recovery sibling
  -> tail height >= 2, if the residue is 1 mod 4
```

If that route fails, the next likely candidate is a delayed continuation
branch, following the existing `3 mod 8` delayed-drift pattern.
