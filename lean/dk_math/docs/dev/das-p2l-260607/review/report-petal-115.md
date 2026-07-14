# Report Petal 115: Recovery Delayed Branch

## Summary

Checkpoint 115 rechecked the route toward extra peeling after checkpoint 114.

The important recovery result is not:

```text
tail recovery at parent depth 2 -> immediate height >= 2
```

The theorem-supported correction is:

```text
tail recovery at parent depth 1 -> immediate height >= 2
tail recovery at parent depth 2 -> delayed 3 mod 8 color
```

Thus the extra-peeling channel exists, but at parent depth `2` it is delayed by
one step.

## Implemented Lean Surface

File:

```text
lean/dk_math/DkMath/Collatz/PetalBridge.lean
```

New shifted-tail color counts:

```lean
orbitWindowResidueCountMod8EqThreeTail
orbitWindowResidueCountMod8EqSevenTail
```

Immediate recovery at parent depth `1`:

```lean
tailRecoveryMass_depth_one_eq_tailResidueCount_mod4_eq_one
tailRecoveryMass_depth_one_le_heightCountGe_two
```

Delayed recovery at parent depth `2`:

```lean
tailRecoveryMass_depth_two_eq_tailResidueCount_mod8_eq_three
tailRecoveryMass_depth_two_le_tailResidueCount_mod8_eq_three
```

Exact-height-one reservoir split:

```lean
tailHeightCountEq_one_split_mod8_three_seven
```

Delayed tail extra-height bridge:

```lean
tailMod8Three_le_nextTailHeightCountGe_two
tailResidueCountMod8EqThree_delayed_drift
```

Source-side hooks:

```lean
sourceRecoveryMass_depth_three_le_tailResidueCount_mod8_eq_three
sourceContinuationMass_depth_two_le_tailMod8Three_add_tailMod8Seven
```

## Main Mathematical Reading

The checkpoint converts the vague phrase "continuation pressure may create
extra peeling" into a more precise finite channel grammar.

Checkpoint 114:

```text
source continuation at parent depth 2
  -> tail exact height 1
```

Checkpoint 115:

```text
tail exact height 1
  = tail 3 mod 8 + tail 7 mod 8
```

Then:

```text
tail 3 mod 8
  -> next tail height >= 2
  -> delayed contribution to sumS
```

The current theorem-level reading is:

```text
pressure or recovery channel
  -> exact-height-one reservoir
  -> color split
  -> delayed extra peeling from the 3 mod 8 color
```

## Corrected Expectations

The proposed theorem

```lean
tailRecoveryMass_depth_two_le_heightCountGe_two
```

is not the right local target.  At parent depth `2`, tail recovery is the
`3 mod 8` cell, which is exact height `1` at the current tail index.

The valid immediate theorem is instead:

```lean
tailRecoveryMass_depth_one_le_heightCountGe_two
```

The valid delayed theorem is:

```lean
tailMod8Three_le_nextTailHeightCountGe_two
```

and its accumulated-height version:

```lean
tailResidueCountMod8EqThree_delayed_drift
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
lean/dk_math/DkMath/Collatz/docs/Collatz-RecoveryDelayedBranch-115.md
```

The new public note records the distinction:

```text
parent depth 1 recovery = immediate extra peeling
parent depth 2 recovery = delayed 3 mod 8 color
```

## Verification

Commands run:

```text
lake build DkMath.Collatz.PetalBridge
lake build DkMath.Collatz.Collatz2K26
rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge.lean
git diff --check -- <touched files>
```

Result:

```text
Both builds completed successfully.
No `sorry` was found in `DkMath.Collatz.PetalBridge`.
`git diff --check` reported no whitespace errors.
```

Known unrelated warning remains:

```text
DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:152:6:
declaration uses `sorry`
```

## Next Implementation Candidates

### 1. Split the continuing color

The next natural experiment is to split the continuing color:

```text
tail 7 mod 8
  -> tail 7 mod 16 / tail 15 mod 16
```

and identify which child becomes delayed-peeling at the next resolution.

### 2. Build a recursive delayed-reservoir tower

The low-resolution pattern suggests a reusable finite grammar:

```text
continuing reservoir at resolution 2^r
  -> delayed-peeling child
  -> continuing child
```

This should be attempted as a thin theorem family only after the `3 mod 8` /
`7 mod 8` checkpoint is accepted.

### 3. Connect pressure-heavy ranges to delayed mass

The current bridge still does not prove that pressure-heavy depth ranges
produce enough `3 mod 8` mass.  A future theorem should connect:

```text
sourceContinuationPressureOnRange
```

or the cause-side outruns vocabulary to:

```text
orbitWindowResidueCountMod8EqThreeTail
```

or to the recursive delayed-reservoir tower.

That is the likely next route from local channel grammar back to `sumS`
growth.
