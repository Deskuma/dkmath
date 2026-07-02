# Collatz Pressure All-Ones Correlation Scan - Checkpoint 132

Checkpoint 132 tests the hypothesis left by checkpoint 131:

```text
long positive pressure blocks are explained by residual all-ones depth
```

Checkpoint 131 only used proxy residue features such as `15 mod 16` and
`31 mod 32`.  Checkpoint 132 measures the feature directly.

## Observable

The Python scan now records:

```text
all_ones_depth(x) = v2 (x + 1)
```

This is the low-bit all-ones suffix length:

```text
1  -> 1 mod 2
3  -> 2
7  -> 3
15 -> 4
31 -> 5
```

New row fields:

```text
residual_all_ones_depth_seq
residual_all_ones_depth_first
residual_all_ones_depth_last
residual_all_ones_depth_mode
residual_all_ones_depth_max
count_all_ones_depth_ge_4
count_all_ones_depth_ge_5
count_all_ones_depth_ge_6
sign_change_cause_labels
sign_change_drop_details
```

## Scan

Command:

```text
python3 python/Collatz/PetalBridge/pressure_sign_pattern_scan.py \
  --max-n 2047 --steps 64 --r-start 2 --depth-len 10
```

Generated:

```text
python/Collatz/PetalBridge/results/pressure_sign_pattern_scan.csv
python/Collatz/PetalBridge/results/pressure_sign_pattern_scan.md
```

## Summary

The global counts remain stable:

```text
rows: 1024
rows with positive pressure depths: 511
rows with local islands: 3
rows with sign-change-up positions: 4
positive block length counts:
  1:380; 2:48; 3:23; 4:33; 5:20; 6:3; 7:1; 8:3
sign-change-up depth counts:
  2:2; 4:2
```

The new all-ones-depth counts are:

```text
all-ones depth first counts:
  1:513; 2:256; 3:128; 4:64; 5:32; 6:16; 7:8; 8:4; 9:2; 10:1

all-ones depth mode counts:
  1:1024

all-ones depth max counts:
  1:54; 2:156; 3:240; 4:83; 5:36; 6:391; 7:34; 8:25; 9:2; 10:1; 11:2
```

## Main Pattern

The strongest table is `positive_block_length by residual_all_ones_depth_max`:

```text
max depth 1:
  block length 0 only

max depth 2:
  block length 0 only

max depth 3:
  almost all block length 0, only a few length 1

max depth 6:
  mostly length 1, with some length 2-4

max depth 8:
  block length 4-6

max depth 10/11:
  block length 8
```

So the checkpoint-131 residue observation was not accidental.  The direct
feature is:

```text
deep max all-ones residual depth in the window
```

not merely the first residue or modal residue.

The mode is actually always shallow in this scan:

```text
all-ones depth mode counts:
  1:1024
```

This means the important signal is not the common state of the whole window.
It is the existence of a deep all-ones excursion inside the window.

## Sign-Change Cause

The scan also classifies upward pressure sign changes using adjacent retention
and continuation drops.

Observed:

```text
sign-change cause counts:
  retention_drop_dominant:4
```

This supports the two-component reading:

```text
global block behavior:
  explained by residual all-ones concentration

local island behavior:
  explained by retention/continuation adjacent decay imbalance
```

This is still observational.  It is not a global monotonicity theorem.

## Lean Surface

Checkpoint 132 adds only the thin profile skeleton:

```lean
ResidualAllOnesDepth
orbitWindowResidualAllOnesDepth
orbitWindowResidualAllOnesDepthSeq
orbitWindowResidualAllOnesDepthSeq_length
orbitWindowResidualAllOnesDepthSeq_get?_eq_some
orbitWindowResidualAllOnesDepthSeq_take_length
orbitWindowResidualAllOnesDepthSeq_take_get?_eq_some
```

The heavy bridge

```text
d <= ResidualAllOnesDepth x
  -> x % 2^d = 2^d - 1
```

is deliberately postponed.  The current checkpoint only fixes the observable
profile needed to read the scan data.

## Next Work

Checkpoint 133 should avoid a full `ShapePressureGrid` for now.

The next useful thin layers are:

```text
ResidualAllOnesProfile:
  profile-level predicates around max all-ones depth and threshold counts

PressureDecayProfile:
  adjacent retention/continuation drop predicates around sign-change-up rows
```

Candidate Lean names:

```lean
def WindowHasResidualAllOnesDepthAtLeast
def SourcePressureRetentionDrop
def SourcePressureContinuationDrop
def SourcePressureSignChangeUpWithDrop
```

The scan route suggests that positive pressure blocks and local pressure
islands should be treated as two related but distinct phenomena.
