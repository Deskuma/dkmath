# Collatz Pressure Correlation Scan - Checkpoint 131

Checkpoint 131 refines the checkpoint-130 scan and adds aggregate correlation
tables.

## Terminology Fix

The Python column formerly named `first_failure_pair` was too broad.  It is now
named:

```text
first_sign_change_pair
```

Meaning:

```text
adjacent nonpositive -> positive pressure margin pair
```

This is narrower than Lean's general `SourcePressurePrefixFailure`, which can
compare any shallow nonselected depth with any deeper selected depth.

The positive block convention is now explicit:

```text
positive block:
  maximal consecutive positive-depth run, length >= 1
```

Rows with block length at least `2` and at least `4` are counted separately.

## Aggregate Scan

The scan still uses:

```text
odd n <= 2047
steps = 64
r_start = 2
depth_len = 10
depths = 2..11
```

New per-row fields:

```text
residual_mod_16_first
residual_mod_16_last
residual_mod_16_mode
residual_mod_32_first
residual_mod_32_last
residual_mod_32_mode
max_positive_block_length
```

New summary tables:

```text
frontier_depth by residual_mod_16_first/mode
frontier_depth by residual_mod_32_first/mode
positive_block_length by residual_mod_16_first
positive_block_length by residual_mod_32_first
local_island rows by residual_mod_16_first
sign-change-up rows by residual_mod_16_first
sign-change-up depth counts
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
positive block length counts:
  1:380; 2:48; 3:23; 4:33; 5:20; 6:3; 7:1; 8:3
sign-change-up depth counts:
  2:2; 4:2
```

## Reading

The frontier is almost always depth `2`; only two rows in this scan have first
frontier depth `3`.

Long positive blocks are not uniform over residues.  The visible concentration
is in high all-ones-like residual classes:

```text
residual 15 mod 16:
  many rows with block length 2..8

residual 31 mod 32:
  no zero-block rows in this scan,
  many rows with block length 2..8
```

Local islands remain rare:

```text
n = 1567, island depth 3, sign-change pair 2 -> 3
n = 1639, island depth 5, sign-change pair 4 -> 5
n = 1775, island depth 5, sign-change pair 4 -> 5
```

This supports the current interpretation:

```text
pressure usually behaves block-like,
but retention/continuation decay can produce genuine local sign changes.
```

## Lean Surface Added

Checkpoint 131 adds small theorem-level handles:

```lean
sourcePressureMargin_lt_of_signChangeUp
sourcePressurePositiveBlock_singleton
sourcePressurePositiveBlock_of_forall_margin_pos
existsSourcePressureLocalIslandBelow_of_lt
existsSourcePressureFrontierBelow_of_lt
sourcePressureSignChangeUp_of_localIsland
```

These do not introduce a heavy grid.  They only connect the checkpoint-130
predicates to the sign-change and bounded-witness readings used by the scan.

## Next Work

Checkpoint 132 can now choose one of two routes.

Preferred scan route:

```text
explain long positive blocks by all-ones residual classes
```

Candidate tables:

```text
block length by residual all-ones depth
frontier depth by count of residual all-ones prefixes
island depth by retention drop vs continuation drop
```

Lean route:

```lean
def SourcePressureMarginJumpUp
def SourcePressureSignChangeUpWithJump
```

The Lean route is light, but the scan route is more informative.
