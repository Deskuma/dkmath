# Report Petal 131

## Summary

Checkpoint 131 refines the pressure sign-pattern scan from checkpoint 130.

Main changes:

```text
first_failure_pair -> first_sign_change_pair
positive block definition fixed as length >= 1 consecutive positive-depth run
aggregate correlation tables added
island/sign-change rows clarified as adjacent sign-change witnesses
```

The scan now reports frontier depth and block length by residual residue class.
The most visible pattern is that long positive blocks concentrate near
all-ones-like residual classes such as `15 mod 16` and `31 mod 32`, while
sign-change-up rows remain rare.

## Python Scan Changes

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
first_sign_change_pair
residual_mod_16_first
residual_mod_16_last
residual_mod_16_mode
residual_mod_32_first
residual_mod_32_last
residual_mod_32_mode
max_positive_block_length
```

New aggregate tables:

```text
frontier_depth by residual_mod_16_first/mode
frontier_depth by residual_mod_32_first/mode
positive_block_length by residual_mod_16_first
positive_block_length by residual_mod_32_first
local_island rows by residual_mod_16_first
sign-change-up rows by residual_mod_16_first
sign-change-up depth counts
```

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
rows with positive blocks length >= 1: 511
rows with positive blocks length >= 2: 131
rows with positive blocks length >= 4: 60
positive block length counts:
  1:380; 2:48; 3:23; 4:33; 5:20; 6:3; 7:1; 8:3
sign-change-up depth counts:
  2:2; 4:2
```

Important reading:

```text
frontier depth:
  almost always depth 2

long positive blocks:
  concentrated around high all-ones-like residual classes

local islands:
  rare but real
```

## Lean Surface

Added:

```lean
sourcePressureMargin_lt_of_signChangeUp
sourcePressurePositiveBlock_singleton
sourcePressurePositiveBlock_of_forall_margin_pos
existsSourcePressureLocalIslandBelow_of_lt
existsSourcePressureFrontierBelow_of_lt
sourcePressureSignChangeUp_of_localIsland
```

These are small API helpers for the checkpoint-130 predicates.  They do not
introduce a global grid or monotonicity theorem.

## Documentation Updates

Updated:

```text
lean/dk_math/DkMath/Collatz/README.md
lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
lean/dk_math/DkMath/Collatz/docs/Collatz-PressureSignPatternScan-130.md
```

Added:

```text
lean/dk_math/DkMath/Collatz/docs/Collatz-PressureCorrelationScan-131.md
```

## Added Inference

The scan suggests a more specific hypothesis:

```text
long positive pressure blocks track all-ones-like residual classes.
```

This is more promising than a generic pressure-prefix theorem.  The frontier is
usually shallow, while the block length appears to encode deeper residue
structure.

The local-island rows still matter because they show the obstruction mechanism:

```text
retention can drop faster than continuation,
causing an adjacent nonpositive -> positive margin sign change.
```

## Suggested Checkpoint 132

Preferred next scan:

```text
block length by residual all-ones depth
frontier depth by count of residual all-ones prefixes
island depth by retention drop vs continuation drop
```

Lean-only fallback:

```lean
def SourcePressureMarginJumpUp
def SourcePressureSignChangeUpWithJump
```

The scan route is stronger because it can identify which residue-depth feature
should become a Lean predicate.

## Verification

Commands:

```text
python3 python/Collatz/PetalBridge/pressure_sign_pattern_scan.py --max-n 2047 --steps 64 --r-start 2 --depth-len 10
lake build DkMath.Collatz.PetalBridge
lake build DkMath.Collatz.Collatz2K26
python3 -m py_compile python/Collatz/PetalBridge/pressure_sign_pattern_scan.py
rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/GnomonEvaluation.lean lean/dk_math/DkMath/Collatz/PetalBridge.lean
git diff --check
```

Initial result:

```text
Python scan: passed
PetalBridge build: passed
Collatz2K26 build: passed
Python py_compile: passed
local Collatz sorry scan: passed, no hits in GnomonEvaluation/PetalBridge
diff whitespace check: passed
```

The `Collatz2K26` build still reports the existing unrelated warning:

```text
DkMath.NumberTheory.ZsigmondyCyclotomicResearch.lean:152:6:
declaration uses `sorry`
```

No new Collatz-side `sorry` was introduced.
