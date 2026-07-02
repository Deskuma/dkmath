# Report Petal 121

## Summary

Checkpoint 121 connects the selected pressure witness layer to the first
delayed-budget surface.

Implemented:

```text
pressure count / outruns-heavy
  -> tower-entry witness alias

depth-two one-range pressure
  -> positive continuation mass
  -> delayed budget with tail 7 mod 8 remainder
```

Also added a Python orbit-window scan for pressure witnesses and L1..L5
remainders.

## Lean Changes

File:

```text
lean/dk_math/DkMath/Collatz/PetalBridge.lean
```

### Tower-Entry Aliases

Added:

```lean
exists_towerEntryDepth_of_pressureDepthCount_pos
exists_towerEntryDepth_of_outrunsMoreThanHalf
```

These are caller-facing wrappers over the checkpoint 120 existence theorems:

```lean
exists_positive_sourceContinuationMass_of_pressureDepthCount_pos
exists_positive_sourceContinuationMass_of_outrunsMoreThanHalf
```

Reading:

```text
positive pressure-depth count
  -> selected local tower-entry opportunity
```

and:

```text
SourceOutrunsMoreThanHalfOnDepthRange
  -> selected local tower-entry opportunity
```

The theorem only provides one selected positive source continuation mass.  It
does not assert independence between several selected depths.

### Depth-Two Positive Budget Pair

Added:

```lean
depthTwoPressureRange_positive_and_budget
exists_depth_two_budget_of_pressureOnRange_two_one
```

Meaning:

```text
SourceContinuationPressureOnRange n k 2 1
  -> 0 < orbitWindowContinuationSiblingMassPow2 n k 2
  -> (k + 1) + orbitWindowContinuationSiblingMassPow2 n k 2
       <= sumS n ((k + 1) + 1)
          + orbitWindowResidueCountMod8EqSevenTail n k
```

This is the direct selected-witness-to-budget bridge requested by the review.

## Python Experiment

New script:

```text
python/Collatz/PetalBridge/orbit_pressure_remainder_scan.py
```

Generated:

```text
python/Collatz/PetalBridge/results/orbit_pressure_remainder_scan.csv
python/Collatz/PetalBridge/results/orbit_pressure_remainder_scan.md
```

Command:

```text
python3 python/Collatz/PetalBridge/orbit_pressure_remainder_scan.py \
  --max-n 999 --steps 64 --r-start 2 --depth-len 8
```

The table records:

```text
n
steps
sumS
pressure_depth_count
first_pressure_depth
continuation_mass_at_first_pressure
retention_mass_at_first_pressure
L1..L5 delayed remainders
L1..L5 falling colors
```

Observed summary:

```text
rows: 500
rows with pressure witness: 237
rows with L5 remainder: 18
max pressure depth count: 6
max L5 remainder: 3
```

Top pressure examples include:

```text
n=511: pressure count 6, first depth 2, continuation 8, retention 10
n=681: pressure count 6, first depth 2, continuation 8, retention 10
n=795: pressure count 5, first depth 2, continuation 14, retention 20
```

## Interpretation

The data suggests:

```text
pressure witnesses are common
deep all-ones remainder is much rarer
```

This is consistent with the current proof direction:

```text
one pressure witness
  -> one delayed budget opportunity
```

but it does not justify:

```text
many pressure witnesses
  -> many independent delayed budgets
```

That second statement still needs a no-overlap or address-separated condition.

## Documentation Updated

Updated:

```text
lean/dk_math/DkMath/Collatz/README.md
lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
```

Added:

```text
lean/dk_math/DkMath/Collatz/docs/Collatz-SelectedWitnessBudget-121.md
```

## Verification

Passed:

```text
python3 python/Collatz/PetalBridge/orbit_pressure_remainder_scan.py \
  --max-n 999 --steps 64 --r-start 2 --depth-len 8
lake build DkMath.Collatz.PetalBridge
lake build DkMath.Collatz.Collatz2K26
rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge.lean
git diff --check -- <touched checkpoint 121 files>
```

The `rg` no-sorry check returned no matches for `PetalBridge.lean`.

Known unrelated warning remains:

```text
DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:152:6:
declaration uses `sorry`
```

## Suggested Next Implementation

Next target:

```lean
theorem exists_two_sourcePressureDepths_of_two_le_pressureDepthCount
```

This should produce two distinct selected pressure depths only.

It must not claim independent budget accounting yet.

The next conceptual package should be one of:

```text
SelectedPressureDepths
SelectedDepthsAddressSeparated
DisjointTowerTargets
```

The safe route is:

```text
count >= 2
  -> two witnesses
  -> investigate whether their target residue channels overlap
```

Only after that should the project attempt a multi-budget sum theorem.
