# Report Petal 132

## Summary

Checkpoint 132 continues the scan route from checkpoint 131.

Primary question:

```text
Can long positive pressure blocks be explained by residual all-ones depth?
```

Result:

```text
Yes, observationally.
```

The prior `15 mod 16` / `31 mod 32` signal was a proxy.  The clearer feature is
the maximum all-ones depth seen inside the residual-shape window:

```text
all_ones_depth(residual) = v2(residual + 1)
```

## Python Changes

Updated:

```text
python/Collatz/PetalBridge/pressure_sign_pattern_scan.py
```

Regenerated:

```text
python/Collatz/PetalBridge/results/pressure_sign_pattern_scan.csv
python/Collatz/PetalBridge/results/pressure_sign_pattern_scan.md
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

The scan also classifies upward pressure sign changes using adjacent retention
and continuation drops.

## Observed Results

Run:

```text
python3 python/Collatz/PetalBridge/pressure_sign_pattern_scan.py \
  --max-n 2047 --steps 64 --r-start 2 --depth-len 10
```

Summary:

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

All-ones-depth counts:

```text
all-ones depth first counts:
  1:513; 2:256; 3:128; 4:64; 5:32; 6:16; 7:8; 8:4; 9:2; 10:1

all-ones depth mode counts:
  1:1024

all-ones depth max counts:
  1:54; 2:156; 3:240; 4:83; 5:36; 6:391; 7:34; 8:25; 9:2; 10:1; 11:2
```

Sign-change cause counts:

```text
retention_drop_dominant:4
```

## Main Inference

The useful feature is not the first residual and not the modal residual.

The mode is always shallow:

```text
all-ones depth mode = 1 for all 1024 rows
```

But the maximum all-ones depth strongly tracks positive block length:

```text
max all-ones depth 1-2:
  block length 0 only

max all-ones depth 3:
  almost all block length 0

max all-ones depth 8:
  block length 4-6

max all-ones depth 10/11:
  block length 8
```

So the pressure block signal is an excursion signal:

```text
the window contains a deep all-ones residual carrier
```

not:

```text
the whole window is all-ones-like
```

This is an important correction before building a larger grid.

## Lean Surface

Added to `DkMath.Collatz.PetalBridge`:

```lean
ResidualAllOnesDepth
orbitWindowResidualAllOnesDepth
orbitWindowResidualAllOnesDepthSeq
orbitWindowResidualAllOnesDepthSeq_length
orbitWindowResidualAllOnesDepthSeq_get?_eq_some
orbitWindowResidualAllOnesDepthSeq_take_length
orbitWindowResidualAllOnesDepthSeq_take_get?_eq_some
```

This is intentionally only a skeleton.  It fixes the observation profile used
by the Python scan without proving the heavier all-ones modulo bridge yet.

## Documentation Updates

Updated:

```text
lean/dk_math/DkMath/Collatz/README.md
lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
```

Added:

```text
lean/dk_math/DkMath/Collatz/docs/Collatz-PressureAllOnesCorrelationScan-132.md
```

## Suggested Checkpoint 133

Do not jump directly to a full `ShapePressureGrid`.

The cleaner next split is:

```text
ResidualAllOnesProfile
PressureDecayProfile
```

Candidate Lean work:

```lean
def WindowHasResidualAllOnesDepthAtLeast
def SourcePressureRetentionDrop
def SourcePressureContinuationDrop
def SourcePressureSignChangeUpWithDrop
```

Candidate Python work:

```text
compare max all-ones depth with max positive block length at larger max_n
separate rows by max-depth threshold counts ge4/ge5/ge6
classify sign-change-up rows by exact retention/continuation drop pair
```

## Verification

Commands:

```text
python3 python/Collatz/PetalBridge/pressure_sign_pattern_scan.py --max-n 2047 --steps 64 --r-start 2 --depth-len 10
python3 -m py_compile python/Collatz/PetalBridge/pressure_sign_pattern_scan.py
lake build DkMath.Collatz.PetalBridge
```

Result:

```text
Python scan: passed
Python py_compile: passed
PetalBridge build: passed
```

The build still reports the existing unrelated warning:

```text
DkMath.NumberTheory.ZsigmondyCyclotomicResearch.lean:152:6:
declaration uses `sorry`
```

No new Collatz-side `sorry` was introduced.
