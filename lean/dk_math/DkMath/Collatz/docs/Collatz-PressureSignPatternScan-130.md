# Collatz Pressure Sign Pattern Scan - Checkpoint 130

Checkpoint 130 returns from Route A list helpers to Route B pressure
observation.

The new scan keeps the two axes separate:

```text
time index i:
  height_i
  residual_i
  first_failed_i

pressure depth j:
  margin_j
  positive_j
  frontier_j
  local_island_j
  sign_change_up_j
```

## Files

```text
python/Collatz/PetalBridge/pressure_sign_pattern_scan.py
python/Collatz/PetalBridge/results/pressure_sign_pattern_scan.csv
python/Collatz/PetalBridge/results/pressure_sign_pattern_scan.md
```

## Default Scan Used

```text
odd n <= 2047
steps = 64
r_start = 2
depth_len = 10
depths = 2..11
```

The scan records:

```text
height_seq
residual_shape_seq
first_failed_depth_seq
residual_mod_8_seq
residual_mod_16_seq
residual_mod_32_seq
positive_depths
positive_blocks
first_frontier_depth
frontier_margin
local_islands
sign_change_up_positions
first_sign_change_pair
margin_jump
retention_drop
continuation_drop
```

## Observed Summary

```text
rows: 1024
rows with positive pressure depths: 511
rows with local islands: 3
rows with sign-change-up positions: 4
rows with positive blocks length >= 1: 511
rows with positive blocks length >= 2: 131
rows with positive blocks length >= 4: 60
max positive depth count: 8
max local island count: 1
max sign-change-up count: 1
```

Representative local-island rows:

```text
n = 1567, island depth 3, first failure pair 2 -> 3
n = 1639, island depth 5, first failure pair 4 -> 5
n = 1775, island depth 5, first failure pair 4 -> 5
```

These rows are the important obstruction witnesses.  They show again that
pressure is not simply carrier nesting and does not support an unconditional
prefix theorem.

Checkpoint 131 refines this scan:

```text
first_sign_change_pair:
  adjacent nonpositive -> positive pressure margin pair

positive block:
  maximal consecutive positive-depth run, length >= 1
```

It also adds aggregate tables by residual residue class.  The strongest visible
pattern in the current scan is:

```text
frontier depth:
  almost always depth 2

long positive blocks:
  concentrated in high all-ones-like residual classes,
  especially residual 15 mod 16 and 31 mod 32

sign-change-up:
  rare, observed at depths 2 and 4
```

## Lean Surface Added

Checkpoint 130 adds only thin predicates and margin bridges:

```lean
SourcePressurePositiveBlock
sourcePressurePositiveBlock_iff_margin
ExistsSourcePressureLocalIslandBelow
existsSourcePressureLocalIslandBelow_iff_margin
ExistsSourcePressureFrontierBelow
existsSourcePressureFrontierBelow_iff_margin
```

These are classification handles for scan output.

They do not assert maximality, uniqueness, global prefix behavior, or a heavy
`ShapePressureGrid`.

## Inference

Positive blocks are common, but islands and sign-change-up rows exist.  The next
step should therefore avoid any unconditional monotonicity theorem.

The useful direction is conditional classification:

```text
positive block if every depth in an interval has positive margin
local island if positive margin is surrounded by nonpositive margins
frontier below if first positive margin appears before a bound
```

This keeps the future `ShapePressureGrid` honest: time features and depth signs
must remain separate axes until a real correlation is observed.

## Suggested Next Work

Checkpoint 131 should either:

```text
1. extend the scan summary with aggregate correlations between
   residual_mod_16/residual_mod_32 and first_frontier_depth
```

or:

```text
2. add one small Lean theorem using the new predicates,
   such as a local-island-below constructor from a concrete island witness.
```

The scan route is preferred.
