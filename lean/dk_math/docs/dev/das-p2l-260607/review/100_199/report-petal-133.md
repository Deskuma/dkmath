# Report Petal 133

## Scope

Checkpoint 133 was executed after the `DkMath.Collatz.PetalBridge`
refactor.  The package is now split under
`DkMath/Collatz/PetalBridge/*.lean`, so this checkpoint placed each new theorem
at the layer where its imports are already available.

Per the current source-of-truth rule, no package docs were synchronized in this
checkpoint.  Explanatory synchronization was written into Lean docstrings and
comments.  This report is the only new markdown artifact for the checkpoint.

## Lean Changes

### `DkMath.Collatz.PetalBridge.Profiles`

Added the thin residual all-ones profile predicates:

```lean
def WindowHasResidualAllOnesDepthAtLeast
def WindowHasDeepResidualAllOnesExcursion
```

and constructors / threshold-lowering helpers:

```lean
theorem windowHasResidualAllOnesDepthAtLeast_of_lt
theorem windowHasResidualAllOnesDepthAtLeast_of_le
theorem windowHasDeepResidualAllOnesExcursion_of_lt
theorem windowHasDeepResidualAllOnesExcursion_of_le
```

These deliberately remain on the time-profile axis.  They do not mention
pressure depth, do not assert a pressure-prefix theorem, and do not define a
full `ShapePressureGrid`.

### `DkMath.Collatz.PetalBridge.TailGrammar`

Added the shifted-label bridge:

```lean
theorem orbitWindowResidualAllOnesDepth_eq_nextLabel
theorem orbitWindowResidualAllOnesDepthSeq_get?_eq_some_nextLabel
```

These were not placed in `Profiles` because the refactored import order places
`orbitWindowResidualShape_eq_oddOrbitLabel_succ` in `TailGrammar`.  The code
comment records this explicitly, so future work does not try to rebuild the
import graph just to read the residual all-ones depth as a shifted label.

### `DkMath.Collatz.PetalBridge.PressureFrontier`

Added the optional local-island margin bridge:

```lean
theorem sourcePressureMargin_lt_of_localIsland_left
```

This is a margin-only theorem.  It does not claim the cause decomposition by
itself, but it gives a clean interface for a future `PressureDecayProfile`.

## Python Experiment

The scan script was extended with:

```text
--name-suffix
```

and additional aggregate tables:

```text
positive_block_length by count_all_ones_depth_ge_4
positive_block_length by count_all_ones_depth_ge_5
positive_block_length by count_all_ones_depth_ge_6
frontier_depth by count_all_ones_depth_ge_4
local_island_count by count_all_ones_depth_ge_4
sign_change_up_count by count_all_ones_depth_ge_4
```

This lets the next reviewer decide whether the signal comes from a single deep
excursion or from repeated medium-depth excursions.

## Robustness Runs

### `--max-n 8191 --steps 64 --r-start 2 --depth-len 10`

Output:

```text
python/Collatz/PetalBridge/results/pressure_sign_pattern_scan_8191_k64.csv
python/Collatz/PetalBridge/results/pressure_sign_pattern_scan_8191_k64.md
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
all-ones depth mode counts: 1:4096
sign-change cause counts: retention_drop_dominant:137
positive block length counts:
  1:1521; 2:251; 3:114; 4:146; 5:76; 6:24;
  7:11; 8:21; 9:1; 10:5
all-ones depth max counts:
  1:104; 2:453; 3:889; 4:455; 5:253; 6:1557;
  7:205; 8:125; 9:21; 10:9; 11:20; 12:1; 13:4
```

### `--max-n 8191 --steps 128 --r-start 2 --depth-len 10`

Output:

```text
python/Collatz/PetalBridge/results/pressure_sign_pattern_scan_8191_k128.csv
python/Collatz/PetalBridge/results/pressure_sign_pattern_scan_8191_k128.md
```

Summary:

```text
rows: 4096
rows with positive pressure depths: 2170
rows with local islands: 93
rows with sign-change-up positions: 137
max positive depth count: 10
max local island count: 1
max sign-change-up count: 1
all-ones depth mode counts: 1:4096
sign-change cause counts: retention_drop_dominant:137
positive block length counts:
  1:1524; 2:249; 3:113; 4:146; 5:76; 6:24;
  7:11; 8:21; 9:1; 10:5
all-ones depth max counts:
  1:104; 2:453; 3:889; 4:455; 5:252; 6:1558;
  7:205; 8:125; 9:21; 10:9; 11:20; 12:1; 13:4
```

The 64-step and 128-step runs are almost identical at this range.  This
suggests the decisive all-ones excursions are already captured by the 64-step
window for odd `n <= 8191`.

### `--max-n 16383 --steps 64 --r-start 2 --depth-len 12`

Output:

```text
python/Collatz/PetalBridge/results/pressure_sign_pattern_scan_16383_k64_d12.csv
python/Collatz/PetalBridge/results/pressure_sign_pattern_scan_16383_k64_d12.md
```

Summary:

```text
rows: 8192
rows with positive pressure depths: 4421
rows with local islands: 252
rows with sign-change-up positions: 404
max positive depth count: 11
max local island count: 1
max sign-change-up count: 1
all-ones depth mode counts: 1:8192
sign-change cause counts: retention_drop_dominant:404
positive block length counts:
  1:2966; 2:570; 3:262; 4:322; 5:143; 6:67;
  7:26; 8:42; 9:3; 10:19; 11:1
all-ones depth max counts:
  1:147; 2:782; 3:1692; 4:1004; 5:580; 6:3099;
  7:462; 8:275; 9:65; 10:25; 11:40; 12:2; 13:19
top row:
  n = 16383, positive block = 2-12, max block = 11,
  all-ones max = 13
```

## Interpretation

The checkpoint-132 hypothesis survived the larger scans:

```text
long positive pressure blocks track the maximum residual all-ones depth
more strongly than the first residual or the mode residual.
```

The mode remains completely uninformative in these runs:

```text
all-ones depth mode = 1 for every scanned row.
```

The max signal remains strong, but it should still be treated as a profile
witness, not as a direct pressure theorem.  A deep all-ones excursion supplies
continuation support; retention mass can still obstruct or shorten the visible
positive block.

The sign-change-up rows are stable:

```text
8191, 64 steps:  retention_drop_dominant:137
8191, 128 steps: retention_drop_dominant:137
16383, 64 steps: retention_drop_dominant:404
```

Thus the local island phenomenon is better read as a pressure-depth decay
imbalance than as a pure all-ones-carrier phenomenon.

## Verification

Commands run:

```text
python3 -m py_compile python/Collatz/PetalBridge/pressure_sign_pattern_scan.py
lake build DkMath.Collatz.PetalBridge.Profiles
lake build DkMath.Collatz.PetalBridge.TailGrammar
lake build DkMath.Collatz.PetalBridge.PressureFrontier
lake build DkMath.Collatz.PetalBridge
```

No new `sorry` was found in:

```text
DkMath/Collatz/PetalBridge/Profiles.lean
DkMath/Collatz/PetalBridge/TailGrammar.lean
DkMath/Collatz/PetalBridge/PressureFrontier.lean
```

## Next Candidate

Checkpoint 134 can now choose between two thin routes.

Route A:

```text
Add count-level residual all-ones predicates.
Example: WindowHasAtLeastResidualAllOnesDepthCount n k d c.
```

This would match the new Python threshold-count tables without touching
pressure semantics.

Route B:

```text
Start a thin PressureDecayProfile layer.
First target: name retention-drop and continuation-drop comparison predicates,
then connect sign-change-up/local-island observations to those predicates.
```

Route B is the better next step if the goal is to explain local islands.
Route A is the safer next step if the goal is to continue validating the
positive-block/all-ones-depth relation before introducing mass-drop vocabulary.
