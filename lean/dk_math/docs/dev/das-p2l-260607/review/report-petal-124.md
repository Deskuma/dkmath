# Report Petal 124

## Goal

Checkpoint 124 asked whether a deeper selected source pressure depth forces
shallower selected source pressure.

The planned path was:

```text
1. prove retention nesting
2. express pressure by an integer margin
3. test the pressure-prefix theorem carefully
```

## Lean Result

Implemented in:

```text
lean/dk_math/DkMath/Collatz/PetalBridge.lean
```

Retention pointwise theorem:

```lean
retention_allOnes_mod_pow_two_of_le
```

Retention count anti-monotonicity:

```lean
sourceRetentionMass_anti_mono_depth
tailRetentionMass_anti_mono_depth
```

Pressure margin API:

```lean
SourcePressureMarginInt
isSourcePressureDepth_iff_margin_pos
```

Prefix API:

```lean
SelectedPressurePrefix
selectedPressurePrefix_zero
selectedPressurePrefix_le_len
isSourcePressureDepth_of_selectedPressurePrefix
selectedPressurePrefix_of_pressureOnRange
```

The Lean result deliberately does not claim unconditional pressure-prefix
monotonicity.

## Experiment

Added:

```text
python/Collatz/PetalBridge/selected_pressure_prefix_scan.py
```

Generated:

```text
python/Collatz/PetalBridge/results/selected_pressure_prefix_scan.csv
python/Collatz/PetalBridge/results/selected_pressure_prefix_scan.md
```

Scan:

```text
odd n <= 9999
steps = 128
r_start = 2
depth_len = 10
```

Result:

```text
rows: 5000
nonempty selected rows: 2681
nonempty prefix rows: 2492 / 2681
prefix failure rows: 189
max selected count: 10
max selected depth: 11
max frontier depth: 12
```

First observed failure:

```text
n = 1567
selected depths: 3
missing selected depth: 2
margin profile:
2:-2; 3:1; 4:0; 5:-1; 6:0; 7:0; 8:0; 9:0; 10:0; 11:0
```

This means:

```text
IsSourcePressureDepth at depth 3 is true
IsSourcePressureDepth at depth 2 is false
```

in that finite observation window.

## Interpretation

Checkpoint 123 proved continuation carrier nesting.

Checkpoint 124 proves retention carrier nesting.

But pressure is a ratio:

```text
retention < 2 * continuation
```

So carrier nesting alone does not imply selected-pressure prefix behavior.
The wider Python scan shows concrete finite-window failures of the naive prefix
hypothesis.

## Next Implementation Candidate

The next checkpoint should avoid the unconditional theorem:

```text
deep selected pressure -> shallow selected pressure
```

Better targets:

```lean
def SourcePressureFrontier ...
def SourcePressureMarginDropControlled ...
```

or obstruction-facing theorems:

```text
positive deep margin and nonpositive shallow margin
  -> pressure-prefix obstruction
```

The immediate Lean-friendly next step is probably a thin obstruction predicate:

```lean
def SourcePressurePrefixFailure
    (n : OddNat) (k r j1 j2 : ℕ) : Prop :=
  j1 < j2 ∧
    ¬ IsSourcePressureDepth n k r j1 ∧
    IsSourcePressureDepth n k r j2
```

Then connect it to margins:

```text
SourcePressurePrefixFailure
  <-> shallow margin <= 0 and deep margin > 0
```

This would turn the failed prefix theorem into a useful diagnostic surface.

## Verification

Passed:

```text
lake build DkMath.Collatz.PetalBridge
lake build DkMath.Collatz.Collatz2K26
rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge.lean  # no output
git diff --check -- touched files
```
