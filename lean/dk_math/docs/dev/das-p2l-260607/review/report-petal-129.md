# Report Petal 129

## Summary

Checkpoint 129 completes the small Route A close-out requested by the previous
report.

The first-failed-depth profile now has the same basic list API as the height
and residual-shape profiles:

```text
length
get?
take length
take get?
```

It also has `height + 1` versions of the `get?` lemmas, which makes the
boundary interpretation directly usable from list indexing.

## Implemented Lean Surface

Added:

```lean
orbitWindowFirstFailedPow2DepthSeq_get?_eq_some
orbitWindowFirstFailedPow2DepthSeq_get?_eq_some_height_add_one
orbitWindowFirstFailedPow2DepthSeq_take_length
orbitWindowFirstFailedPow2DepthSeq_take_get?_eq_some
orbitWindowFirstFailedPow2DepthSeq_take_get?_eq_some_height_add_one
orbitWindow_threeProfiles_get?_eq_some
```

The main theorem reading is:

```text
first_failed_i = height_i + 1
```

and this can now be recovered both from the full sequence and from prefixes.

## Three Time Profiles

The following three ordered profiles now share the same basic interface:

```lean
orbitWindowHeightSeq
orbitWindowResidualShapeSeq
orbitWindowFirstFailedPow2DepthSeq
```

The added theorem

```lean
orbitWindow_threeProfiles_get?_eq_some
```

packages their aligned `get?` facts at a single in-window time index.

This is intentionally a time-profile theorem.  It does not mix the time index
`i` with the pressure-depth index `j`.

## Added Inference

Route A is now basically closed for the current one-dimensional time profiles.

The next useful work is not another guessed theorem about pressure.  The better
route is a pressure sign-pattern scan that carries the aligned time-profile
data:

```text
height_seq
residual_shape_seq
first_failed_depth_seq
residual_mod_8_seq
residual_mod_16_seq
residual_mod_32_seq
positive_depths
positive_blocks
local_islands
sign_change_up_positions
first_frontier_depth
frontier_margin
margin_jump
retention_drop
continuation_drop
```

The target question is:

```text
Which time-profile features correlate with pressure-depth sign patterns?
```

This is the data route toward a later `ShapePressureGrid`.

## Documentation Updates

Updated:

```text
lean/dk_math/DkMath/Collatz/README.md
lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
lean/dk_math/DkMath/Collatz/docs/Collatz-ResidualShapeSequence-128.md
```

Added:

```text
lean/dk_math/DkMath/Collatz/docs/Collatz-FirstFailedDepthSequence-129.md
```

## Suggested Checkpoint 130

Recommended route:

```text
Route B pressure scan
```

Use Python or a lightweight generated table first.  Do not add a large Lean
predicate until the scan shows a stable sign-pattern feature.

If a Lean-only checkpoint is needed before the scan, keep it very thin:

```lean
SourcePressurePositiveBlock
```

but the preferred next step is still numerical classification of pressure
sign-patterns paired with the three time profiles.

## Verification

Commands:

```text
lake build DkMath.Collatz.PetalBridge
lake build DkMath.Collatz.Collatz2K26
rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/GnomonEvaluation.lean lean/dk_math/DkMath/Collatz/PetalBridge.lean
git diff --check
```

Initial result:

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
