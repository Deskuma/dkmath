# Report Petal 128

## Summary

Checkpoint 128 continues Route A: make the residual-shape profile as usable as
the height profile.

The implementation now treats

```lean
orbitWindowResidualShapeSeq n k
```

as a normal finite observation list.  It has length, direct `get?`, prefix
length, and prefix `get?` lemmas.  This closes the basic list API gap left by
checkpoint 127.

The checkpoint also adds the first-failed-depth sequence and records the
expected relation:

```text
first failed depth = observed height + 1
```

Finally, the local source-pressure island predicate now has a margin-language
equivalence, so the pressure side can be read directly as a sign pattern.

## Implemented Lean Surface

### Residual Shape Sequence

Added:

```lean
orbitWindowResidualShapeSeq_length
orbitWindowResidualShapeSeq_get?_eq_some
orbitWindowResidualShapeSeq_get?_eq_some_shifted_label
orbitWindowResidualShapeSeq_take_length
orbitWindowResidualShapeSeq_take_get?_eq_some
```

These mirror the existing `orbitWindowHeightSeq` helper API.

The most useful operational theorem is:

```lean
orbitWindowResidualShapeSeq_get?_eq_some_shifted_label
```

It says that reading the residual-shape profile at time `i` recovers the next
odd orbit label:

```text
(orbitWindowResidualShapeSeq n k)[i]?
  = some (oddOrbitLabel n (i + 1))
```

under `i < k`.

This turns the checkpoint-127 identity into a list-indexed theorem.

### First Failed Depth Sequence

Added:

```lean
orbitWindowFirstFailedPow2DepthSeq
orbitWindowFirstFailedPow2DepthSeq_length
orbitWindowFirstFailedPow2Depth_eq_height_add_one
```

The theorem

```lean
orbitWindowFirstFailedPow2Depth_eq_height_add_one
```

fixes the boundary interpretation:

```text
height h:
  depths <= h succeed
  depth h + 1 first fails
```

This is the clean bridge from 2-adic height to obstruction depth.

### Local Pressure Island

Added:

```lean
sourcePressureLocalIsland_iff_margin
```

This rewrites the predicate

```lean
SourcePressureLocalIsland n k r j
```

as the sign condition

```text
j > 0
margin(j) > 0
margin(j - 1) <= 0
margin(j + 1) <= 0
```

This is intentionally local.  It does not claim prefix structure, down-closure,
or global uniqueness.  It is only the margin-sign reading of an isolated
positive depth.

## Documentation Updates

Updated:

```text
lean/dk_math/DkMath/Collatz/README.md
lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
lean/dk_math/DkMath/Collatz/docs/Collatz-WindowResidualShape-127.md
```

Added:

```text
lean/dk_math/DkMath/Collatz/docs/Collatz-ResidualShapeSequence-128.md
```

The new checkpoint document records:

- residual-shape list API,
- first-failed-depth sequence,
- local island margin equivalence,
- the index-axis warning,
- suggested next routes.

## Axis Correction

The important design constraint remains:

```text
i = orbit-window time index
j = pressure-depth index
```

These are different axes.

The current code now has enough one-dimensional API for both sides:

```text
time profile:
  label_i
  height_i
  residual_i = label_{i+1}
  first_failed_depth_i

depth profile:
  margin(j)
  frontier(j)
  sign_change(j)
  local_island(j)
```

The next real object should be introduced deliberately as a two-dimensional
view:

```text
ShapePressureGrid:
  time i x depth j
```

Do not encode this prematurely as a one-index theorem.

## Additional Inference

The implemented `first_failed_depth = height + 1` theorem suggests a natural
next list API:

```lean
orbitWindowFirstFailedPow2DepthSeq_get?_eq_some
orbitWindowFirstFailedPow2DepthSeq_take_length
orbitWindowFirstFailedPow2DepthSeq_take_get?_eq_some
```

These should be easy and will make the height/residual/failed-depth profiles
parallel:

```text
orbitWindowHeightSeq
orbitWindowResidualShapeSeq
orbitWindowFirstFailedPow2DepthSeq
```

After that, pressure-side work should probably return to numerical scans and
classify sign-pattern shapes before adding larger predicates.

## Suggested Checkpoint 129

Recommended next step:

```text
Route A small close-out:
  add first-failed-depth sequence get?/take helpers
```

Then switch back to Route B:

```text
pressure sign-pattern scan:
  positive blocks
  local islands
  frontier depth
  sign-change-up positions
```

This keeps the Lean API small while preparing the later `ShapePressureGrid`.

## Verification

Expected verification commands:

```text
lake build DkMath.Collatz.PetalBridge
lake build DkMath.Collatz.Collatz2K26
rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/GnomonEvaluation.lean lean/dk_math/DkMath/Collatz/PetalBridge.lean
git diff --check
```

Result:

```text
PetalBridge build: passed
Collatz2K26 build: passed
local Collatz sorry scan: passed, no hits in GnomonEvaluation/PetalBridge
diff whitespace check: passed
```

The `Collatz2K26` build still reports the existing unrelated warning:

```text
DkMath.NumberTheory.ZsigmondyCyclotomicResearch.lean:152:6:
declaration uses `sorry`
```

No new Collatz-side `sorry` was introduced.
