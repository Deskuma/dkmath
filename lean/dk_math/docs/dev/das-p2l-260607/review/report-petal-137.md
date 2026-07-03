# Report Petal 137

## Scope

Checkpoint 137 closed the local equivalence between an adjacent source-pressure
margin jump and positive net integer pressure drop.

This remains a local adjacent-depth theorem.  It does not introduce a pressure
prefix theorem, a full grid, `Real.log`, or a named `RetentionDropDominant`
predicate.

## Lean Changes

Updated:

```text
lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
```

Added the reverse implication:

```lean
theorem sourcePressureNetDropPositive_of_marginJumpUp
```

Closed the local equivalence:

```lean
theorem sourcePressureMarginJumpUp_iff_netDropPositive
```

Added sign-change and local-island bridges:

```lean
theorem sourcePressureNetDropPositive_of_signChangeUp
theorem sourcePressureNetDropPositive_of_localIsland_left
```

Added a packaging theorem from positive net drop plus the two decay predicates:

```lean
theorem sourcePressureJumpWithDecay_of_netDropPositive_of_decay
```

The stable local API is now:

```text
SourcePressureMarginJumpUp n k r j
  iff
SourcePressureNetDropPositive n k r j
```

where `SourcePressureNetDropPositive` is the exact integer balance quantity
from checkpoint 136:

```text
0 < retention_drop - 2 * continuation_drop
```

## Python Changes

Updated:

```text
python/Collatz/PetalBridge/pressure_sign_pattern_scan.py
```

Added row-level counts:

```text
net_drop_positive_count
margin_jump_count
margin_jump_iff_net_drop_failure_count
```

Added summary fields:

```text
rows_with_net_drop_positive
rows_with_margin_jump
rows_with_margin_jump_iff_net_drop_failure
```

This mirrors the Lean equivalence at scan level.

## Experiment

Command:

```bash
python3 python/Collatz/PetalBridge/pressure_sign_pattern_scan.py \
  --max-n 16383 --steps 64 --r-start 2 --depth-len 12 \
  --name-suffix _137_16383_k64_d12
```

Generated:

```text
python/Collatz/PetalBridge/results/pressure_sign_pattern_scan_137_16383_k64_d12.csv
python/Collatz/PetalBridge/results/pressure_sign_pattern_scan_137_16383_k64_d12.md
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
sign-change cause counts: retention_drop_dominant:404
```

The scan-level equality of row counts agrees with the Lean theorem:

```text
rows_with_net_drop_positive = rows_with_margin_jump
rows_with_margin_jump_iff_net_drop_failure = 0
```

## Inference

The pressure-decay layer now has an exact local algebraic surface:

```text
margin jump
  <-> positive step difference
  <-> positive net pressure drop
```

This means later proofs should not reason directly from the Python
`retention_drop_dominant` label.  The Lean-facing object is now
`SourcePressureNetDropPositive`.

The next natural theorem is the zero-crossing statement mentioned by the
review file:

```text
signChangeUp iff current margin is nonpositive
  and current margin + net drop is positive
```

This would connect the local algebraic balance sheet to the sign-profile
frontier/island vocabulary without asserting any global prefix shape.

## Suggested Next Checkpoint

Consider proving a theorem of the form:

```lean
sourcePressureSignChangeUp_iff_margin_nonpos_and_netDrop_crosses
```

The expected shape is:

```text
SourcePressureSignChangeUp n k r j
  iff
SourcePressureMarginInt n k (r + j) <= 0
  and
0 < SourcePressureMarginInt n k (r + j)
      + (SourceRetentionDropInt n k r j
          - 2 * SourceContinuationDropInt n k r j)
```

This should be treated as another local adjacent-edge theorem.

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
