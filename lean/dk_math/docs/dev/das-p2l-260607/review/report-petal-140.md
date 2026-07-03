# Report Petal 140

## Scope

Checkpoint 140 named the local pressure island crossing/falling shape as a
first-class Lean predicate:

```lean
SourcePressurePulse n k r j
```

The implementation stays inside the current pressure-depth vocabulary.  It
does not introduce a pressure-prefix theorem, a shape grid, or any global
interval theorem.

## Lean changes

Updated:

```text
lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
```

Added:

```lean
def SourcePressurePulse
theorem sourcePressurePulse_of_localIsland
theorem sourcePressurePulse_left
theorem sourcePressurePulse_right
def SourcePressureSignPulse
theorem sourcePressureSignPulse_of_localIsland
theorem sourcePressurePulse_iff_signPulse
```

Interpretation:

```text
left edge:
  margin_jprev <= 0
  margin_jprev + netDrop_jprev > 0

right edge:
  margin_j > 0
  margin_j + netDrop_j <= 0
```

This fixes the local island as a named pulse:

```text
nonpositive -> positive -> nonpositive
```

but expressed through the integer net-drop balance sheet rather than by
claiming any global monotone pressure profile.

## Python observation changes

Updated:

```text
python/Collatz/PetalBridge/pressure_sign_pattern_scan.py
```

Added row fields:

```text
local_pressure_pulse_positions
local_pressure_pulse_count
local_island_to_pulse_failure_count
```

Added summary fields:

```text
rows_with_local_pressure_pulse
rows_with_local_island_to_pulse_failure
```

Generated:

```text
python/Collatz/PetalBridge/results/pressure_sign_pattern_scan_140_16383_k64_d12.csv
python/Collatz/PetalBridge/results/pressure_sign_pattern_scan_140_16383_k64_d12.md
```

Main observed summary:

```text
rows: 8192
rows with positive pressure depths: 4421
rows with local islands: 252
rows with sign-change-up positions: 404
rows_with_sign_change_down: 4421
rows_with_local_pressure_pulse: 252
rows_with_local_island_to_pulse_failure: 0
rows_with_local_island_right_fall_failure: 0
rows_with_sign_change_up_iff_crossing_failure: 0
rows_with_sign_change_down_iff_falling_failure: 0
```

The scan agrees with the Lean direction:

```text
SourcePressureLocalIsland -> SourcePressurePulse
```

and found no counterexample in the checkpoint-140 window.

## Inference

`SourcePressurePulse` is now the right unit of negotiation for the next layer.
It is more precise than a raw local island because it exposes the two adjacent
net-drop edges, and it is safer than a block theorem because it remains local.

This suggests two next directions:

1. Define a positive-run / interval-pulse vocabulary for longer blocks.
2. Split the pressure-decay material into a smaller file, for example
   `DkMath.Collatz.PetalBridge.PressureDecay`, if `PressureFrontier.lean`
   continues to grow.

The first direction is mathematically more useful.  The second is engineering
cleanup and can wait unless the next checkpoint needs many more decay lemmas.

## Verification

Commands run:

```text
python3 -m py_compile python/Collatz/PetalBridge/pressure_sign_pattern_scan.py
lake build DkMath.Collatz.PetalBridge.PressureFrontier
lake build DkMath.Collatz.PetalBridge
python3 python/Collatz/PetalBridge/pressure_sign_pattern_scan.py --max-n 16383 --steps 64 --r-start 2 --depth-len 12 --name-suffix _140_16383_k64_d12
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

Add the thin interval vocabulary that generalizes a pulse from a singleton
island to a positive pressure run:

```lean
def SourcePressureRun
def SourcePressureRunHasLeftCrossing
def SourcePressureRunHasRightFall
```

Keep it local to pressure-depth indices and continue avoiding any unconditional
pressure-prefix claim.
