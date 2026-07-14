# Report Petal 135

## Scope

Checkpoint 135 continued the thin `PressureDecayProfile` layer in
`DkMath.Collatz.PetalBridge.PressureFrontier`.

The Lean side still avoids quantitative dominance.  The new API only packages
already available observations across the same adjacent pressure-depth edge:

- margin jump upward,
- retention mass strictly drops,
- continuation mass weakly drops.

This keeps the proof surface ready for the next integer-drop identity without
claiming `RetentionDropDominant` in Lean yet.

## Lean Changes

Updated:

```text
lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
```

Added thin predicate:

```lean
def SourcePressureJumpWithDecay
    (n : OddNat) (k r j : Nat) : Prop :=
  SourcePressureMarginJumpUp n k r j ∧
    SourceRetentionDropsAcross n k r j ∧
      SourceContinuationWeaklyDropsAcross n k r j
```

Added wrapper theorems:

```lean
sourcePressureJumpWithRetentionDrop_of_parts
sourcePressureJumpWithRetentionDrop_of_signChangeUp_of_retentionDrop
sourcePressureJumpWithRetentionDrop_of_localIsland_left_of_retentionDrop
sourcePressureJumpWithDecay_of_parts
sourcePressureJumpWithDecay_of_signChangeUp_of_decay
```

The source comments now explicitly mark the next refinement point:

```text
margin_next - margin_current =
  retention_drop - 2 * continuation_drop
```

with the convention that the future integer drops should be read as
`current - next`.

## Python Changes

Updated:

```text
python/Collatz/PetalBridge/pressure_sign_pattern_scan.py
```

Added a numeric scan field:

```text
max_retention_drop_minus_2_continuation_drop
```

and included per sign-change detail:

```text
retention_drop_minus_2_continuation_drop
```

The PressureDecay sections now emit all observed rows:

- all sign-change-up rows with pressure-decay details,
- all local-island rows with left-edge decay details.

## Experiment

Command:

```bash
python3 python/Collatz/PetalBridge/pressure_sign_pattern_scan.py \
  --max-n 16383 --steps 64 --r-start 2 --depth-len 12 \
  --name-suffix _135_16383_k64_d12
```

Generated:

```text
python/Collatz/PetalBridge/results/pressure_sign_pattern_scan_135_16383_k64_d12.csv
python/Collatz/PetalBridge/results/pressure_sign_pattern_scan_135_16383_k64_d12.md
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
sign-change cause counts: retention_drop_dominant:404
```

The large scan again shows that every sign-change-up row in this window is
classified by the experimental rule as `retention_drop_dominant`.  This is
still observational Python data, not a Lean theorem.

## Inference

The useful next move is not a dominance predicate yet.  The stronger and more
structural target is the integer accounting identity:

```text
margin_next - margin_current =
  retention_drop - 2 * continuation_drop
```

Given

```text
margin_j = 2 * continuation_j - retention_j
retention_drop = retention_j - retention_next
continuation_drop = continuation_j - continuation_next
```

the identity is algebraic:

```text
(2 * continuation_next - retention_next)
  - (2 * continuation_j - retention_j)
= retention_drop - 2 * continuation_drop
```

That identity should become the checkpoint-136 bridge.  It converts the
current order-only predicates into an exact integer balance sheet and explains
why the Python `retention_drop_minus_2_continuation_drop` field numerically
matches the observed margin jump.

## Suggested Next Checkpoint

Introduce integer-valued drop definitions, probably in the same
`PressureFrontier` file unless the layer grows large enough to split:

```lean
def SourceRetentionDropInt
def SourceContinuationDropInt
```

Then prove the local adjacent-depth identity for `SourcePressureMarginInt`.

Only after that identity is in Lean should the project decide whether to name a
dominance predicate such as `RetentionDropDominant`.

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
