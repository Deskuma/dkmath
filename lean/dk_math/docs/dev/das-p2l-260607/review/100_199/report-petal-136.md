# Report Petal 136

## Scope

Checkpoint 136 fixed the integer accounting layer for the Collatz pressure
frontier work.

The main result is local and adjacent-depth only:

```text
margin_next - margin_current =
  retention_drop - 2 * continuation_drop
```

No global pressure-prefix theorem, no `Real.log`, no full grid, and no named
`RetentionDropDominant` predicate were introduced.

## Lean Changes

Updated:

```text
lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
```

Added integer-valued drop definitions:

```lean
noncomputable def SourceRetentionDropInt
noncomputable def SourceContinuationDropInt
```

Both use the same sign convention:

```text
drop = current_depth_mass - next_depth_mass
```

Added the adjacent margin-step identity:

```lean
theorem sourcePressureMarginStepDiff_eq
```

Added the bridge from a strict margin comparison to a positive integer step:

```lean
theorem sourcePressureMarginJumpUp_iff_stepDiff_pos
```

Added a safe local net-drop predicate:

```lean
def SourcePressureNetDropPositive
```

and the first theorem using the balance sheet:

```lean
theorem sourcePressureMarginJumpUp_of_netDropPositive
```

The comments in source code now spell out that this is an adjacent-edge
balance sheet, not a global selected-pressure shape theorem.

## Python Changes

Updated:

```text
python/Collatz/PetalBridge/pressure_sign_pattern_scan.py
```

Added scan fields:

```text
margin_step_diff
retention_drop_minus_2_continuation_drop
margin_step_matches_net_drop
margin_step_identity_failure_count
```

Added summary field:

```text
rows_with_margin_step_identity_failure
```

This gives an external sanity check for the same identity now proved in Lean.

## Experiment

Command:

```bash
python3 python/Collatz/PetalBridge/pressure_sign_pattern_scan.py \
  --max-n 16383 --steps 64 --r-start 2 --depth-len 12 \
  --name-suffix _136_16383_k64_d12
```

Generated:

```text
python/Collatz/PetalBridge/results/pressure_sign_pattern_scan_136_16383_k64_d12.csv
python/Collatz/PetalBridge/results/pressure_sign_pattern_scan_136_16383_k64_d12.md
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
sign-change cause counts: retention_drop_dominant:404
```

The Python scan and the Lean theorem now agree on the exact local accounting
identity.  The scan still sees all sign-change-up rows in this finite window as
`retention_drop_dominant`, but that remains experimental classification only.

## Inference

The balance sheet changes the next design question.

Before checkpoint 136, a margin jump and the two decay observations were only
packaged together.  After checkpoint 136, a margin jump can be read exactly as
positive net drop:

```text
retention_drop - 2 * continuation_drop > 0
```

This suggests that the next Lean layer should avoid global claims and instead
build local equivalences around `SourcePressureNetDropPositive`.

Possible next theorem surface:

```lean
theorem sourcePressureNetDropPositive_of_marginJumpUp
theorem sourcePressureMarginJumpUp_iff_netDropPositive
theorem sourcePressureJumpWithDecay_of_netDropPositive_of_decay
```

The first two are likely thin consequences of
`sourcePressureMarginStepDiff_eq` and
`sourcePressureMarginJumpUp_iff_stepDiff_pos`.

## Suggested Next Checkpoint

Checkpoint 137 should consider closing the equivalence:

```text
SourcePressureMarginJumpUp n k r j
  iff
SourcePressureNetDropPositive n k r j
```

Then, if useful, add wrappers connecting:

```text
sign-change-up
local-island-left-edge
net-drop-positive
jump-with-decay
```

Keep `RetentionDropDominant` out of Lean until the exact predicate and its
intended use are unavoidable.

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
