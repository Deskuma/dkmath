# Report Petal 141

## Scope

Checkpoint 141 generalizes the singleton `SourcePressurePulse` vocabulary to a
thin interval vocabulary for positive pressure runs.

This checkpoint remains local to pressure-depth indices.  It does not claim a
global pressure-prefix theorem and does not introduce a full pressure grid.

## Lean changes

Updated:

```text
lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
```

Added:

```lean
def SourcePressureRun
def SourcePressureRunHasLeftCrossing
def SourcePressureRunHasRightFall
def SourcePressureIntervalPulse

theorem sourcePressureIntervalPulse_run
theorem sourcePressureIntervalPulse_left
theorem sourcePressureIntervalPulse_right
theorem sourcePressureIntervalPulse_singleton_of_localIsland
```

`SourcePressureRun` is deliberately only a meaning-name alias for the existing
`SourcePressurePositiveBlock`.  This avoids duplicating an equivalent block
definition while giving later code a more interval-oriented name.

The left crossing predicate includes the guard:

```lean
0 < a
```

This is intentional.  It prevents the predecessor address `a - 1` from
silently collapsing at the left boundary.

The new singleton bridge is:

```lean
SourcePressureLocalIsland n k r j
  -> SourcePressureIntervalPulse n k r j 1
```

So the existing local island is now visible both as a singleton pulse and as
an interval pulse of length one.

## Python observation changes

Updated:

```text
python/Collatz/PetalBridge/pressure_sign_pattern_scan.py
```

Added row fields:

```text
interval_pulse_blocks
interval_pulse_count
positive_block_without_left_crossing_count
positive_block_without_right_fall_count
```

Added summary fields:

```text
rows_with_interval_pulse
rows_with_positive_block_without_left_crossing
rows_with_positive_block_without_right_fall
```

Generated:

```text
python/Collatz/PetalBridge/results/pressure_sign_pattern_scan_141_16383_k64_d12.csv
python/Collatz/PetalBridge/results/pressure_sign_pattern_scan_141_16383_k64_d12.md
```

Important convention:

```text
left crossing is checked only for blocks with start > r_start
```

If a positive block starts at the observed left boundary, the scan does not
have the previous pressure depth, so it does not classify that case as a left
crossing failure.

Main observed summary:

```text
rows: 8192
rows with positive pressure depths: 4421
rows with local islands: 252
rows_with_local_pressure_pulse: 252
rows_with_interval_pulse: 404
rows_with_positive_block_without_left_crossing: 0
rows_with_positive_block_without_right_fall: 0
rows_with_sign_change_up_iff_crossing_failure: 0
rows_with_sign_change_down_iff_falling_failure: 0
```

The scan supports the intended reading:

```text
positive run with observable boundaries
  = left crossing + positive plateau + right falling
```

within the checkpoint-141 observation window.

## Inference

`SourcePressureIntervalPulse` is now the better negotiation unit for longer
positive pressure blocks.  The older prefix-failure language remains useful
as an obstruction, but the constructive reading is now:

```text
prefix failure can indicate a pressure pulse / interval pulse
```

This reframes non-prefix behavior as positive structure rather than merely as
failure of monotonicity.

The current Lean API is intentionally thin.  It names the interval shape and
gives projections, but it does not yet prove maximality, uniqueness, or
coverage by runs.

## Verification

Commands run:

```text
python3 -m py_compile python/Collatz/PetalBridge/pressure_sign_pattern_scan.py
lake build DkMath.Collatz.PetalBridge.PressureFrontier
lake build DkMath.Collatz.PetalBridge
python3 python/Collatz/PetalBridge/pressure_sign_pattern_scan.py --max-n 16383 --steps 64 --r-start 2 --depth-len 12 --name-suffix _141_16383_k64_d12
rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
```

Result:

```text
pass
```

The `rg` check returned no matches in `PressureFrontier.lean`.

The build still reports the pre-existing unrelated warning:

```text
DkMath.NumberTheory.ZsigmondyCyclotomicResearch: declaration uses `sorry`
```

## Suggested next checkpoint

Two routes are now reasonable.

Route A: split the pressure-decay vocabulary into:

```text
DkMath.Collatz.PetalBridge.PressureDecay
```

Route B: add thin interval-run extraction helpers:

```lean
sourcePressureIntervalPulse_of_run_boundaries
sourcePressureIntervalPulse_left_signChange
sourcePressureIntervalPulse_right_signChange
```

I would do Route B first if the next checkpoint remains mathematical, and
Route A first if file size starts blocking review.
