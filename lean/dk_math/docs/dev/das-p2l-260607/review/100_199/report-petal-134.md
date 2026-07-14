# Report Petal 134

## Scope

Checkpoint 134 starts the thin `PressureDecayProfile` layer after the
`DkMath.Collatz.PetalBridge` refactor.

No package docs were synchronized.  The durable explanation was placed in Lean
docstrings and source comments, following the current rule that source comments
are the active synchronization surface.

## Lean Changes

File:

```text
lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
```

Added named margin-jump vocabulary:

```lean
def SourcePressureMarginJumpUp
```

Added weak pressure-decay predicates:

```lean
def SourceRetentionDropsAcross
def SourceContinuationWeaklyDropsAcross
```

These avoid natural-number subtraction.  They are comparison predicates over
adjacent pressure depths:

```text
retention_next < retention_current
continuation_next <= continuation_current
```

Added a combined observation predicate:

```lean
def SourcePressureJumpWithRetentionDrop
```

The name deliberately avoids `Dominant`.  The Python scan uses a quantitative
cause label, but this Lean predicate only packages:

```text
margin jumps up
retention strictly drops
```

Added bridge theorems:

```lean
theorem sourcePressureMarginJumpUp_of_signChangeUp
theorem sourcePressureMarginJumpUp_of_localIsland_left
```

The existing theorem

```lean
sourcePressureMargin_lt_of_localIsland_left
```

remains the raw inequality form.  The new theorem is only the named predicate
version for future pressure-decay work.

## Python Changes

File:

```text
python/Collatz/PetalBridge/pressure_sign_pattern_scan.py
```

Added two CSV fields:

```text
sign_change_pressure_decay_details
local_island_pressure_decay_details
```

Added a `PressureDecay` summary section:

```text
PressureDecay: Sign-Change-Up Rows
PressureDecay: Local-Island Rows
```

The sign-change rows now expose:

```text
j
margin_j
margin_next
margin_jump
retention_j
retention_next
retention_drop
continuation_j
continuation_next
continuation_drop
cause
```

The local-island rows now expose:

```text
n
island_depth
left_edge_j
margin_left
margin_island
margin_right
retention_left
retention_island
retention_right
continuation_left
continuation_island
continuation_right
```

This keeps the time axis and pressure-depth axis separate.  It does not assert
that a local island is caused by any single global condition.

## Experiment

Generated a checkpoint-specific scan:

```text
python3 python/Collatz/PetalBridge/pressure_sign_pattern_scan.py \
  --max-n 8191 --steps 64 --r-start 2 --depth-len 10 \
  --name-suffix _134_8191_k64
```

Outputs:

```text
python/Collatz/PetalBridge/results/pressure_sign_pattern_scan_134_8191_k64.csv
python/Collatz/PetalBridge/results/pressure_sign_pattern_scan_134_8191_k64.md
```

Summary:

```text
rows: 4096
rows with positive pressure depths: 2170
rows with local islands: 91
rows with sign-change-up positions: 137
max positive depth count: 10
max local island count: 1
max sign-change-up count: 1
sign-change cause counts: retention_drop_dominant:137
```

Representative sign-change pressure-decay row:

```text
n=6247:
  j=4
  margin_j=0
  margin_next=2
  margin_jump=2
  retention_j=12
  retention_next=6
  retention_drop=6
  continuation_j=6
  continuation_next=4
  continuation_drop=2
  cause=retention_drop_dominant
```

Representative local-island pressure-decay row:

```text
n=1567:
  island_depth=3
  left_edge_j=2
  margin_left=-2
  margin_island=1
  margin_right=0
  retention_left=8
  retention_island=3
  retention_right=2
  continuation_left=3
  continuation_island=2
  continuation_right=1
```

## Inference

The new Lean vocabulary matches the current experimental resolution:

```text
sign-change-up -> margin jump
local island -> left-edge margin jump
```

The retention/continuation observations are now visible in Python, but Lean
does not yet formalize the quantitative dominance inequality

```text
retention_drop > 2 * continuation_drop
```

That restraint is intentional.  The next useful step is to decide whether the
dominance relation should be formalized as an integer inequality or kept as a
computed classification layer for a few more checkpoints.

## Verification

Commands run:

```text
lake build DkMath.Collatz.PetalBridge.PressureFrontier
lake build DkMath.Collatz.PetalBridge
python3 -m py_compile python/Collatz/PetalBridge/pressure_sign_pattern_scan.py
git diff --check
```

No new `sorry` was found in:

```text
lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
```

## Next Candidate

Checkpoint 135 has two clean options.

Route A:

```text
Add theorem wrappers that turn a strict retention drop plus a suitable
continuation weak drop into a named pressure-decay observation.
```

This remains thin and avoids dominance.

Route B:

```text
Introduce an integer-valued retention/continuation drop expression, then define
SourcePressureRetentionDropDominatesContinuationDrop only when the exact
inequality is ready.
```

Route B is more expressive, but it should not be started unless the reviewer
wants the quantitative cause label moved from Python into Lean.
