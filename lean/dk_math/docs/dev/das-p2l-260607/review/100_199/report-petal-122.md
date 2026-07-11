# Report Petal 122

## Summary

Checkpoint 122 formalizes selected source pressure depths and proves the safe
two-witness theorem:

```text
2 <= sourceContinuationPressureDepthCount
  -> two distinct selected pressure depths exist
```

It deliberately does not sum delayed budgets.

The Python side now measures overlap between selected continuation-index sets.
The default scan found no disjoint selected-depth pair in the finite sample.

## Lean Changes

File:

```text
lean/dk_math/DkMath/Collatz/PetalBridge.lean
```

## Selected Pressure Predicate

Added:

```lean
def IsSourcePressureDepth
```

Meaning:

```text
IsSourcePressureDepth n k r j
```

is the local `MoreThanHalf` source continuation pressure at depth `r + j`.

Basic API:

```lean
isSourcePressureDepth_of_pressureOnRange
positive_sourceContinuationMass_of_isSourcePressureDepth
```

## Witness Extraction

Added:

```lean
exists_isSourcePressureDepth_of_pressureDepthCount_pos
exists_isSourcePressureDepth_with_positive_mass
```

These wrap the checkpoint 120 witness theorem in the new predicate vocabulary.

## Two Witnesses

Added:

```lean
exists_two_isSourcePressureDepths_of_two_le_pressureDepthCount
exists_two_sourcePressureDepths_of_two_le_pressureDepthCount
```

The first theorem returns two distinct packaged selected-depth witnesses.
The second theorem unpacks them into the original `MoreThanHalf` spelling.

No budget independence is asserted.

## Depth-Two Budget Predicate

Added:

```lean
def HasDepthTwoDelayedBudget
theorem hasDepthTwoDelayedBudget_of_pressureOnRange_two_one
```

This packages the checkpoint 121 depth-two positive budget pair as a reusable
proposition.

## Python Experiment

New script:

```text
python/Collatz/PetalBridge/selected_depth_overlap_scan.py
```

Generated:

```text
python/Collatz/PetalBridge/results/selected_depth_overlap_scan.csv
python/Collatz/PetalBridge/results/selected_depth_overlap_scan.md
```

Command:

```text
python3 python/Collatz/PetalBridge/selected_depth_overlap_scan.py \
  --max-n 999 --steps 64 --r-start 2 --depth-len 8
```

Observed summary:

```text
rows: 500
rows with at least two selected depths: 52
rows with a disjoint selected-depth pair: 0
rows where every selected-depth pair overlaps: 52
max selected depth count: 6
max pairwise overlap: 13
```

Top samples:

```text
n=511 selected depths 2;3;4;5;6;7
n=681 selected depths 2;3;4;5;6;7
n=255 selected depths 2;3;4;5;6
```

## Interpretation

The overlap scan is important.  In this finite observation, selected pressure
depths did not produce disjoint continuation-index sets.  This suggests that
selected depths should be treated as nested or overlapping unless a future
hypothesis proves otherwise.

The next formal object should probably not be:

```text
many witnesses -> many independent budgets
```

but rather one of:

```text
SelectedDepthOverlapControlled
NestedSelectedPressureDepths
DisjointTowerTargets under an explicit hypothesis
```

## Documentation Updated

Updated:

```text
lean/dk_math/DkMath/Collatz/README.md
lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
```

Added:

```text
lean/dk_math/DkMath/Collatz/docs/Collatz-SelectedPressureDepths-122.md
```

## Verification

Passed:

```text
python3 python/Collatz/PetalBridge/selected_depth_overlap_scan.py \
  --max-n 999 --steps 64 --r-start 2 --depth-len 8
lake build DkMath.Collatz.PetalBridge
lake build DkMath.Collatz.Collatz2K26
rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge.lean
git diff --check -- <touched checkpoint 122 files>
```

The `rg` no-sorry check returned no matches for `PetalBridge.lean`.

Known unrelated warning remains:

```text
DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:152:6:
declaration uses `sorry`
```

## Suggested Next Implementation

The next checkpoint should not sum budgets yet.

A safe next theorem family is:

```lean
def SelectedDepthContinuationIndices ...
def SelectedDepthsOverlap ...
def SelectedDepthsDisjoint ...
```

or a Lean-only thin predicate:

```lean
def SelectedSourcePressureDepthsPairwiseDisjoint
    (n : OddNat) (k r : ℕ) (js : Finset ℕ) : Prop := ...
```

Then prove only introductory facts:

```text
disjointness is symmetric
disjoint selected depths have no shared index
two-witness theorem plus disjointness hypothesis gives two non-overlapping
carrier sets
```

Only after that should a summed delayed-budget theorem be attempted.
