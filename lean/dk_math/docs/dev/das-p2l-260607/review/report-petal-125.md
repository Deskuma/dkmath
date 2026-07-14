# Report Petal 125

## Summary

Checkpoint 125 was a trajectory-correction checkpoint.

The main subject changed from direct `3n+1` language to:

```text
Odd gnomon correction
  n + (2n+1) = 3n+1

Power-of-two alignment evaluation
  v2 (3n+1)

Residual shape extraction
  (3n+1) / 2^height

Relative scale update
  the residual odd shape becomes the next state
```

The existing PetalBridge theorems still apply.  The correction is about the
reading and the module boundary: low-level Collatz arithmetic now starts in
`DkMath.Collatz.GnomonEvaluation`, while `DkMath.Collatz.PetalBridge` remains
the finite observation and pressure/margin layer.

## Code Changes

New file:

```text
lean/dk_math/DkMath/Collatz/GnomonEvaluation.lean
```

Implemented definitions:

```lean
OddGnomonLayer
RawGnomonStep
RawGnomonHeight
RawGnomonResidualShape
RawGnomonRemainderAtDepth
FirstFailedPow2Depth
```

Implemented theorems:

```lean
rawGnomonStep_eq_three_mul_add_one
rawGnomonStep_eq_threeNPlusOne
square_succ_eq_square_add_oddGnomonLayer
sum_oddGnomonLayer_eq_square
sum_odd_eq_square
square_add_eq_square_add_gnomon_sum
rawGnomonHeight_eq_s
rawGnomonRemainderAtDepth_eq_zero_of_le_height
```

Updated integration:

```text
lean/dk_math/DkMath/Collatz/Collatz2K26.lean
```

`Collatz2K26` now imports `DkMath.Collatz.GnomonEvaluation` and lists it in
the package structure comment.

## PetalBridge Correction

`PetalBridge.lean` now has an explicit checkpoint-125 module comment warning:

```text
carrier nesting is not pressure-prefix nesting
```

Reason:

```text
pressure(depth) is not membership.
pressure(depth) is retention(depth) < 2 * continuation(depth).
```

Both masses can shrink with depth, but their ratio can change non-monotonically.

New diagnostic predicates/theorems:

```lean
SourcePressurePrefixFailure
sourcePressurePrefixFailure_lt
not_isSourcePressureDepth_of_prefixFailure_left
isSourcePressureDepth_of_prefixFailure_right
sourcePressurePrefixFailure_iff_margin
not_selectedPressurePrefix_of_prefixFailure
SourcePressureSelectedSetDownClosed
downClosed_iff_no_prefixFailure
```

The core equivalence is:

```text
SourcePressurePrefixFailure
  <-> j1 < j2 and margin(j1) <= 0 and 0 < margin(j2)
```

This turns the observed prefix failure into a Lean object rather than a loose
Python note.

## Documentation Changes

Updated:

```text
lean/dk_math/DkMath/Collatz/README.md
lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
lean/dk_math/DkMath/Collatz/docs/Collatz-PressureMargin-124.md
```

Added:

```text
lean/dk_math/DkMath/Collatz/docs/Collatz-GnomonEvaluation-125.md
```

The documentation now records:

```text
raw step = odd gnomon correction
height = power-of-two alignment depth
accelerated odd label = residual shape / next relative scale
sumS = cumulative power-of-two alignment evaluation
```

## Verification

Commands run:

```text
lake build DkMath.Collatz.GnomonEvaluation
lake build DkMath.Collatz.PetalBridge
lake build DkMath.Collatz.Collatz2K26
rg -n "\bsorry\b" touched Collatz Lean files
git diff --check -- tracked touched files
rg -n "[ \t]$" new files
```

All passed.  The `sorry` search found no new `sorry` in
`GnomonEvaluation.lean` or `PetalBridge.lean`.

Known unrelated build warning still appears when `PetalBridge` dependencies
replay:

```text
DkMath.NumberTheory.ZsigmondyCyclotomicResearch declaration uses sorry
```

This warning is outside the Collatz checkpoint.

## Inference

The most important correction is that the prefix hypothesis should not be the
default target.  The safer target is:

```text
classify pressure sign patterns
```

In particular:

```text
pressure frontier:
  first place where margin becomes positive

pressure island:
  positive margin not forming a prefix

pressure obstruction:
  shallow margin <= 0 and deep margin > 0
```

The Lean side now has the predicate for the third case.

## Suggested Next Implementation

Two routes are natural.

### Route A: residual-shape bridge

Connect `RawGnomonResidualShape` to the accelerated map:

```lean
RawGnomonResidualShape n.1 = (T n).1
```

or a named bridge with the exact existing `T` spelling.

This likely needs the existing `padicValNat` maximality / division facts, not
ad-hoc arithmetic.

### Route B: failure classification

Add finite predicates for pressure islands/frontiers:

```lean
SourcePressureIsland
SourcePressureFrontier
FirstSourcePressureFailurePair
```

Before proving strong theorems, extend the Python scan with:

```text
first_failure_pair
shallow_margin
deep_margin
margin_jump
retention_shallow
retention_deep
continuation_shallow
continuation_deep
retention_drop
continuation_drop
```

Then choose the next Lean theorem based on the observed failure type.

## Recommendation

Prefer Route A first if the reviewer wants the new gnomon reading tied more
tightly to the old Collatz core.

Prefer Route B first if the reviewer wants to continue the pressure-profile
experiment.

Both routes are now separated cleanly enough that they can progress without
making `PetalBridge.lean` absorb more low-level arithmetic vocabulary.
