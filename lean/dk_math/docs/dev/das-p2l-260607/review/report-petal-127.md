# Report Petal 127

## Summary

Checkpoint 127 lifts the pointwise residual-shape theorem into finite orbit
windows.

Checkpoint 126 closed:

```text
RawGnomonResidualShape n.val = (T n).val
```

Checkpoint 127 closes:

```text
orbitWindowResidualShape n i = oddOrbitLabel n (i + 1)
```

So a finite Collatz observation window can now be read as a finite chain of
residual-shape extractions.

## Code Changes

Updated:

```text
lean/dk_math/DkMath/Collatz/PetalBridge.lean
```

New window definitions:

```lean
orbitWindowResidualShape
orbitWindowResidualShapeSeq
orbitWindowFirstFailedPow2Depth
```

New window bridge theorems:

```lean
orbitWindowResidualShape_eq_oddOrbitLabel_succ
orbitWindowResidualShapeSeq_eq_shifted_oddOrbitLabels
orbitWindow_rawGnomonStep_factor
orbitWindow_firstFailed_remainder_ne_zero
```

The key theorem is:

```lean
orbitWindowResidualShape_eq_oddOrbitLabel_succ
```

Meaning:

```text
the residual shape extracted from the current odd label is the next odd label
```

## Pressure Additions

Checkpoint 127 also adds thin sign-pattern vocabulary:

```lean
SourcePressureSignChangeUp
sourcePressureSignChangeUp_of_frontier_pos
SourcePressureLocalIsland
```

This is intentionally modest.  These are observation predicates, not a pressure
prefix theorem.

The added theorem:

```lean
sourcePressureSignChangeUp_of_frontier_pos
```

shows that a positive frontier gives a local upward margin sign change at the
previous depth.

## Mathematical Reading

The finite window now has the following verified structure at every index:

```text
label_i
  -> RawGnomonStep label_i
  -> orbitWindowHeight n i
  -> orbitWindowResidualShape n i
  -> label_{i+1}
```

The raw factorization theorem states:

```text
RawGnomonStep (label_i)
  = 2 ^ orbitWindowHeight n i * orbitWindowResidualShape n i
```

Thus `PetalBridge` is no longer only a height/residue observation surface.  It
now exposes the actual finite residual-shape dynamics of the accelerated
Collatz orbit.

## Documentation Changes

Updated:

```text
lean/dk_math/DkMath/Collatz/README.md
lean/dk_math/DkMath/Collatz/docs/Collatz-GnomonResidualShape-126.md
lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
```

Added:

```text
lean/dk_math/DkMath/Collatz/docs/Collatz-WindowResidualShape-127.md
```

## Verification

Commands run:

```text
lake build DkMath.Collatz.PetalBridge
lake build DkMath.Collatz.Collatz2K26
rg -n "\bsorry\b" touched Collatz Lean files
git diff --check -- tracked touched files
rg -n "[ \t]$" new files
```

All passed.  No new `sorry` was introduced in `PetalBridge.lean` or
`GnomonEvaluation.lean`.

The usual unrelated dependency warning may still appear when replaying
`PetalBridge` dependencies:

```text
DkMath.NumberTheory.ZsigmondyCyclotomicResearch declaration uses sorry
```

## Inference

The Route A chain is now:

```text
pointwise residual shape = T
window residual shape = next odd label
residual-shape sequence = shifted label sequence
```

This suggests that the next shape-dynamics checkpoint should add ordered
profile helpers analogous to the existing height-profile helpers:

```lean
orbitWindowResidualShapeSeq_length
orbitWindowResidualShapeSeq_get?_eq_some
orbitWindowResidualShapeSeq_take_get?_eq_some
```

These would make residual-shape windows as ergonomic as height windows.

## Suggested Next Checkpoint

Two natural routes remain.

### Route A: residual-shape sequence API

Add list API:

```lean
orbitWindowResidualShapeSeq_length
orbitWindowResidualShapeSeq_get?_eq_some
orbitWindowResidualShapeSeq_take_length
orbitWindowResidualShapeSeq_take_get?_eq_some
```

This is low risk and would mirror the established `orbitWindowHeightSeq` API.

### Route B: pressure sign-pattern classification

Use Python summaries to decide which predicates deserve theorem support:

```text
positive blocks
local islands
first frontier depth
margin jump
retention drop
continuation drop
```

If continuing Route B in Lean, the next safe theorem is likely a margin
equivalence for `SourcePressureLocalIsland`.

## Recommendation

Prefer Route A for one more checkpoint.

Reason:

```text
The finite window now has residual-shape dynamics, but it still lacks the list
helper API that made height profiles useful.
```

After the residual-shape list API exists, pressure-island statements can refer
to a richer window surface rather than only to margins.
