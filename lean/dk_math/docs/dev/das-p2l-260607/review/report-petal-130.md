# Report Petal 130

## Summary

Checkpoint 130 returns to Route B: pressure sign-pattern observation.

The checkpoint adds a Python scan that records both axes:

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

The scan found that positive pressure depths often form blocks, but local
islands and sign-change-up rows also occur.  Therefore the pressure surface
must remain a margin-sign profile; it should not be collapsed into an
unconditional prefix theorem.

## Python Scan

Added:

```text
python/Collatz/PetalBridge/pressure_sign_pattern_scan.py
```

Generated:

```text
python/Collatz/PetalBridge/results/pressure_sign_pattern_scan.csv
python/Collatz/PetalBridge/results/pressure_sign_pattern_scan.md
```

Run used:

```text
python3 python/Collatz/PetalBridge/pressure_sign_pattern_scan.py \
  --max-n 2047 --steps 64 --r-start 2 --depth-len 10
```

Observed:

```text
rows: 1024
rows with positive pressure depths: 511
rows with local islands: 3
rows with sign-change-up positions: 4
rows with positive blocks: 132
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

These are obstruction witnesses against a naive pressure-prefix theorem.

## Lean Surface

Added thin classification handles:

```lean
SourcePressurePositiveBlock
sourcePressurePositiveBlock_iff_margin
ExistsSourcePressureLocalIslandBelow
existsSourcePressureLocalIslandBelow_iff_margin
ExistsSourcePressureFrontierBelow
existsSourcePressureFrontierBelow_iff_margin
```

These are intentionally light.  They classify observed sign patterns; they do
not assert maximality, uniqueness, global prefix behavior, or a heavy
`ShapePressureGrid`.

## Documentation Updates

Updated:

```text
lean/dk_math/DkMath/Collatz/README.md
lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
```

Added:

```text
lean/dk_math/DkMath/Collatz/docs/Collatz-PressureSignPatternScan-130.md
```

## Added Inference

The pressure surface now has three useful finite readings:

```text
positive block:
  every depth in an interval has positive margin

local island:
  positive margin surrounded by nonpositive margins

frontier below:
  the first positive margin appears before a finite bound
```

The scan shows all three are useful handles, but the next step should still be
data-driven.  The strongest next scan would aggregate correlations between:

```text
residual_mod_16 / residual_mod_32
first_frontier_depth
positive block length
local island depth
```

This is the next realistic approach toward a later `ShapePressureGrid`.

## Suggested Checkpoint 131

Recommended:

```text
extend the pressure scan with aggregate correlation tables
```

Candidate summaries:

```text
frontier_depth by residual_mod_16
positive_block_length by residual_mod_16
local_island_depth by residual_mod_16
sign_change_up_depth by residual_mod_16
```

If Lean-only work is requested, keep it small: add constructor-style theorems
for the new bounded predicates from explicit witnesses.

## Verification

Commands:

```text
python3 python/Collatz/PetalBridge/pressure_sign_pattern_scan.py --max-n 2047 --steps 64 --r-start 2 --depth-len 10
lake build DkMath.Collatz.PetalBridge
lake build DkMath.Collatz.Collatz2K26
rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/GnomonEvaluation.lean lean/dk_math/DkMath/Collatz/PetalBridge.lean
git diff --check
```

Initial result:

```text
Python scan: passed
PetalBridge build: passed
Collatz2K26 build: passed
local Collatz sorry scan: passed, no hits in GnomonEvaluation/PetalBridge
diff whitespace check: passed
Python py_compile: passed
```

The `Collatz2K26` build still reports the existing unrelated warning:

```text
DkMath.NumberTheory.ZsigmondyCyclotomicResearch.lean:152:6:
declaration uses `sorry`
```

No new Collatz-side `sorry` was introduced.
