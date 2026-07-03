# Report Petal 142

## Scope

Checkpoint 142 added consumer-side helpers for
`SourcePressureIntervalPulse`.

The interval pulse vocabulary remains thin:

```text
run + left crossing + right fall
```

No maximality, uniqueness, coverage, or prefix theorem was added.

## Lean changes

Updated:

```text
lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
```

Added constructor:

```lean
theorem sourcePressureIntervalPulse_of_run_boundaries
```

Added sign-profile projections:

```lean
theorem sourcePressureIntervalPulse_left_pos
theorem sourcePressureIntervalPulse_left_signChange
theorem sourcePressureIntervalPulse_right_signChange
```

Added net-drop projections:

```lean
theorem sourcePressureIntervalPulse_left_crossing
theorem sourcePressureIntervalPulse_right_falling
```

These helpers make interval pulses directly usable in later accounting
lemmas.  A caller no longer needs to unfold the interval predicate to recover
the left guard, the two sign changes, or the integer net-drop crossing/falling
forms.

## Python observation changes

Updated:

```text
python/Collatz/PetalBridge/pressure_sign_pattern_scan.py
```

Added requested summary aliases:

```text
rows_with_interval_pulse_left_crossing_failure
rows_with_interval_pulse_right_falling_failure
```

These are the same boundary sanity checks introduced in checkpoint 141, now
named from the interval-pulse extraction viewpoint.

Generated:

```text
python/Collatz/PetalBridge/results/pressure_sign_pattern_scan_142_16383_k64_d12.csv
python/Collatz/PetalBridge/results/pressure_sign_pattern_scan_142_16383_k64_d12.md
```

Main observed summary:

```text
rows: 8192
rows_with_interval_pulse: 404
rows_with_interval_pulse_left_crossing_failure: 0
rows_with_interval_pulse_right_falling_failure: 0
rows_with_sign_change_up_iff_crossing_failure: 0
rows_with_sign_change_down_iff_falling_failure: 0
```

The existing convention remains:

```text
left crossing is checked only for blocks with start > r_start
```

Blocks beginning at the observed left boundary do not expose their previous
depth in this scan, so they are not counted as left-crossing failures.

## Inference

The useful contract is now:

```text
SourcePressureIntervalPulse
  -> run
  -> left sign change
  -> right sign change
  -> left net-drop crossing
  -> right net-drop falling
```

This is a stable enough API for downstream pressure-decay accounting.  The
next mathematical step can consume interval pulses without unfolding their
definition.

The next engineering step is increasingly clear: `PressureFrontier.lean` now
contains frontier, block, net-drop, pulse, and interval vocabulary.  A careful
split into `DkMath.Collatz.PetalBridge.PressureDecay` is becoming worthwhile,
but it should be done as a minimal movement checkpoint to avoid import cycles.

## Verification

Commands run:

```text
python3 -m py_compile python/Collatz/PetalBridge/pressure_sign_pattern_scan.py
lake build DkMath.Collatz.PetalBridge.PressureFrontier
lake build DkMath.Collatz.PetalBridge
python3 python/Collatz/PetalBridge/pressure_sign_pattern_scan.py --max-n 16383 --steps 64 --r-start 2 --depth-len 12 --name-suffix _142_16383_k64_d12
rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
git diff --check
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

Do the import-safe split:

```text
DkMath.Collatz.PetalBridge.PressureDecay
```

Minimal first move:

```text
move only the integer drop / net-drop / crossing-falling balance sheet
leave frontier and island-facing bridge theorems in PressureFrontier
```

That keeps the mathematical API stable while reducing file pressure.
