# Report Petal 138

## Scope

Checkpoint 138 closed the local zero-crossing theorem for
`SourcePressureSignChangeUp`.

The theorem remains strictly local to one adjacent pressure-depth edge.  It
does not claim a global pressure prefix, does not introduce `Real.log`, and
does not define a full pressure grid.

## Lean Changes

Updated:

```text
lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
```

Added a named integer net-drop expression:

```lean
noncomputable def SourcePressureNetDropInt
```

`SourcePressureNetDropPositive` now reads through this expression:

```lean
def SourcePressureNetDropPositive
    (n : OddNat) (k r j : Nat) : Prop :=
  0 < SourcePressureNetDropInt n k r j
```

The old API name is preserved.  The definition is just cleaner for future
zero-crossing and right-edge work.

Added the additive margin theorem:

```lean
theorem sourcePressureMargin_next_eq_current_add_netDrop
```

Added the main zero-crossing theorem:

```lean
theorem sourcePressureSignChangeUp_iff_margin_nonpos_and_netDrop_crosses
```

This gives the local reading:

```text
sign-change-up
  iff
current margin <= 0
and
current margin + net drop > 0
```

Added local-island left-edge wrapper:

```lean
theorem sourcePressureCrosses_of_localIsland_left
```

## Python Changes

Updated:

```text
python/Collatz/PetalBridge/pressure_sign_pattern_scan.py
```

Added scan fields:

```text
current_margin
net_drop
current_margin_plus_net_drop
next_margin
crossing_matches_sign_change_up
crossing_identity_failure_count
sign_change_up_iff_crossing_failure_count
```

Added summary fields:

```text
rows_with_crossing_identity_failure
rows_with_sign_change_up_iff_crossing_failure
```

These mirror the Lean zero-crossing theorem at scan level.

## Experiment

Command:

```bash
python3 python/Collatz/PetalBridge/pressure_sign_pattern_scan.py \
  --max-n 16383 --steps 64 --r-start 2 --depth-len 12 \
  --name-suffix _138_16383_k64_d12
```

Generated:

```text
python/Collatz/PetalBridge/results/pressure_sign_pattern_scan_138_16383_k64_d12.csv
python/Collatz/PetalBridge/results/pressure_sign_pattern_scan_138_16383_k64_d12.md
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
sign-change cause counts: retention_drop_dominant:404
```

The finite scan agrees with the new Lean zero-crossing theorem:

```text
current_margin + net_drop = next_margin
sign-change-up iff current_margin <= 0 and current_margin + net_drop > 0
```

## Inference

The local pressure story is now a three-step chain:

```text
integer balance:
  next margin = current margin + net drop

jump reading:
  margin jump iff net drop is positive

zero-crossing reading:
  sign-change-up iff current nonpositive margin crosses above zero
```

This is a cleaner interface than using the Python classification label
`retention_drop_dominant` directly.  The Lean-facing term is
`SourcePressureNetDropInt`, and the Lean-facing predicate is
`SourcePressureNetDropPositive`.

## Suggested Next Checkpoint

Two natural next moves remain:

1. Add `SourcePressureSignChangeDown` and the local-island right-edge fall.
   This would complete the local island as left crossing up plus right crossing
   down.

2. Split the pressure-decay material into:

```text
DkMath.Collatz.PetalBridge.PressureDecay
```

The file is now carrying pressure margin, integer-drop accounting, zero
crossing, frontier, island, and prefix helpers.  The split is not urgent, but
the pressure-decay block has become cohesive enough to extract cleanly.

If continuing theorem work first, the right-edge fall is the more mathematical
next step.  If preparing for longer maintenance, the split is the cleaner
engineering step.

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
