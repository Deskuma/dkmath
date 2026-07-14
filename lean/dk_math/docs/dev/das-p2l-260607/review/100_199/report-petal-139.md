# Report Petal 139

## Scope

Checkpoint 139 added the right-edge fall side of a local source-pressure
island.

The result is still local to adjacent pressure-depth edges.  It does not claim
that selected pressure depths are prefix-shaped and does not introduce a full
pressure grid.

## Lean Changes

Updated:

```text
lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
```

Added the downward sign-change predicate:

```lean
def SourcePressureSignChangeDown
```

Added the local-island right-edge bridge:

```lean
theorem sourcePressureSignChangeDown_of_localIsland
```

Added the falling form of the zero-crossing theorem:

```lean
theorem sourcePressureSignChangeDown_iff_margin_pos_and_netDrop_falls
```

Added local-island right-edge falling extraction:

```lean
theorem sourcePressureFalls_of_localIsland_right
```

Added the pulse packaging theorem:

```lean
theorem sourcePressureLocalIsland_gives_crossing_pulse
```

The local island now has both edges available:

```text
left edge:
  current margin <= 0
  and current margin + net drop > 0

right edge:
  current margin > 0
  and current margin + net drop <= 0
```

This closes the immediate up/down local pulse shape without asserting anything
about deeper global pressure structure.

## Python Changes

Updated:

```text
python/Collatz/PetalBridge/pressure_sign_pattern_scan.py
```

Added row-level fields:

```text
sign_change_down_positions
sign_change_down_count
falling_matches_sign_change_down
local_island_right_fall_failure_count
sign_change_down_iff_falling_failure_count
```

Added summary fields:

```text
rows_with_sign_change_down
rows_with_local_island_right_fall_failure
rows_with_sign_change_down_iff_falling_failure
```

These mirror the Lean right-edge falling theorem at scan level.

## Experiment

Command:

```bash
python3 python/Collatz/PetalBridge/pressure_sign_pattern_scan.py \
  --max-n 16383 --steps 64 --r-start 2 --depth-len 12 \
  --name-suffix _139_16383_k64_d12
```

Generated:

```text
python/Collatz/PetalBridge/results/pressure_sign_pattern_scan_139_16383_k64_d12.csv
python/Collatz/PetalBridge/results/pressure_sign_pattern_scan_139_16383_k64_d12.md
```

Observed summary:

```text
rows: 8192
rows with positive pressure depths: 4421
rows with local islands: 252
rows with sign-change-up positions: 404
max positive depth count: 11
max local island count: 1
max sign-change-up count: 1
largest margin jump: 12
largest retention drop: 20
largest continuation drop: 13
largest retention drop minus 2 continuation drop: 10
rows_with_margin_step_identity_failure: 0
rows_with_net_drop_positive: 8089
rows_with_margin_jump: 8089
rows_with_margin_jump_iff_net_drop_failure: 0
rows_with_crossing_identity_failure: 0
rows_with_sign_change_up_iff_crossing_failure: 0
rows_with_sign_change_down: 4421
rows_with_local_island_right_fall_failure: 0
rows_with_sign_change_down_iff_falling_failure: 0
sign-change cause counts: retention_drop_dominant:404
```

The finite scan agrees with the Lean right-edge theorem:

```text
local island right edge -> sign-change-down
sign-change-down iff current margin > 0 and current margin + net drop <= 0
```

## Inference

The local pulse vocabulary is now justified:

```text
SourcePressureLocalIsland
  -> left zero-crossing up
  -> right fall down
```

This gives a compact local obstruction shape for the larger Collatz/Petal
pressure story.  The observed pressure is not a monotone carrier; it is a sign
profile with local pulses.

## Suggested Next Checkpoint

There are two good next moves:

1. Engineering split:

```text
DkMath.Collatz.PetalBridge.PressureDecay
```

The pressure-decay block now includes integer drops, margin step identity,
up/down crossing, local island pulse, and packaging theorems.  It is coherent
enough to extract without changing theorem statements.

2. Thin vocabulary:

```lean
def SourcePressurePulse
```

This could package the two local pulse edge conditions into one predicate.  If
the next checkpoint keeps theorem work going, this is the smaller step.

## Verification

Passed:

```text
python3 -m py_compile python/Collatz/PetalBridge/pressure_sign_pattern_scan.py
lake build DkMath.Collatz.PetalBridge.PressureFrontier
lake build DkMath.Collatz.PetalBridge
rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
git diff --check
```

Notes:

- `rg sorry` returned no hits in `PressureFrontier.lean`.
- `lake build DkMath.Collatz.PetalBridge` still reports the pre-existing
  project warning that
  `DkMath.NumberTheory.ZsigmondyCyclotomicResearch` uses `sorry`; this
  checkpoint did not touch that file.
