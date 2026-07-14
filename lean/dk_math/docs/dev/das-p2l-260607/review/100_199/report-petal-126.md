# Report Petal 126

## Summary

Checkpoint 126 prioritizes Route A:

```text
Connect the new gnomon residual-shape vocabulary to the existing accelerated
Collatz map.
```

The main theorem is:

```lean
rawGnomonResidualShape_eq_T_val
```

This proves that the checkpoint-125 residual shape is exactly the natural value
of the existing accelerated map `T`.

## Code Changes

Updated:

```text
lean/dk_math/DkMath/Collatz/GnomonEvaluation.lean
```

New Route A theorems:

```lean
rawGnomonResidualShape_eq_T_val
rawGnomonResidualShape_odd
rawGnomonStep_eq_pow_height_mul_residualShape
two_pow_succ_rawGnomonHeight_not_dvd
rawGnomonRemainderAtDepth_firstFailed_ne_zero
```

The exact reading is now:

```text
RawGnomonStep = 2^RawGnomonHeight * RawGnomonResidualShape
RawGnomonResidualShape = T value
RawGnomonResidualShape is odd
height + 1 is the first non-dividing power-of-two depth
```

Updated:

```text
lean/dk_math/DkMath/Collatz/PetalBridge.lean
```

New window lift:

```lean
orbitWindowHeight_eq_rawGnomonHeight_oddOrbitLabel
```

New Route B starter predicates/theorems:

```lean
SourcePressureFrontier
sourcePressureFrontier_iff_margin
sourcePressurePrefixFailure_of_frontier_pos
```

## Mathematical Result

Checkpoint 125 established:

```text
j <= height -> raw remainder at depth j is zero
```

Checkpoint 126 adds:

```text
j = height + 1 -> raw remainder at depth j is nonzero
```

So the alignment boundary is no longer just a one-sided observation.  It is now
exact:

```text
RawGnomonHeight is the last fully aligned power-of-two depth.
FirstFailedPow2Depth is the first depth where the residual odd shape appears.
```

This is stronger than a narrative reading of the Collatz step.  The shape
extraction is connected to the actual accelerated map and to a precise
divisibility boundary.

## Pressure Result

Route B was not expanded into islands yet.  Instead, a small safe predicate was
added:

```lean
SourcePressureFrontier
```

It means:

```text
the first depth whose source pressure margin is positive
```

The margin theorem:

```lean
sourcePressureFrontier_iff_margin
```

states:

```text
frontier j
  <-> margin(j) > 0 and every shallower margin is <= 0
```

If `0 < j`, the frontier produces a concrete prefix failure:

```lean
sourcePressurePrefixFailure_of_frontier_pos
```

This keeps the checkpoint-125 correction intact:

```text
frontier is not prefix
first positive margin is not all-positive prefix
```

## Documentation Changes

Updated:

```text
lean/dk_math/DkMath/Collatz/README.md
lean/dk_math/DkMath/Collatz/docs/Collatz-GnomonEvaluation-125.md
lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
```

Added:

```text
lean/dk_math/DkMath/Collatz/docs/Collatz-GnomonResidualShape-126.md
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

The usual unrelated dependency warning can still appear when replaying
`PetalBridge` dependencies:

```text
DkMath.NumberTheory.ZsigmondyCyclotomicResearch declaration uses sorry
```

## Inference

The residual shape route is now strong enough to support two next directions.

### Direction A: residual-shape window profiles

Define finite window profiles for residual shapes:

```lean
noncomputable def orbitWindowResidualShape
noncomputable def orbitWindowResidualShapeSeq
```

Likely theorem:

```lean
orbitWindowResidualShape_eq_oddOrbitLabel_succ
```

Meaning:

```text
the residual shape extracted from oddOrbitLabel n i is oddOrbitLabel n (i+1)
```

This would turn the pointwise `RawGnomonResidualShape = T` bridge into a window
dynamics theorem.

### Direction B: pressure sign-pattern classification

The next safe pressure predicates are:

```lean
SourcePressureLocalIsland
SourcePressureIsland
FirstSourcePressureFailurePair
```

But they should be driven by Python classification first:

```text
first_failure_pair
margin_jump
retention_drop
continuation_drop
first_frontier_depth
is_island
```

## Recommended Next Checkpoint

Prefer Direction A first:

```text
orbitWindowResidualShape
orbitWindowResidualShapeSeq
residual shape at index i equals odd label at i+1
```

Reason:

```text
PetalBridge pressure profiles observe finite orbit windows.
The residual-shape bridge should therefore be lifted from one point to the
whole window before adding heavier pressure-island terminology.
```

After that, return to pressure islands with better semantics:

```text
an island is a positive-margin event in the residual-shape window profile
```
