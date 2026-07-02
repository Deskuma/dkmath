# Collatz Selected Pressure Depths 122

Checkpoint 122 turns "selected pressure depth" into an explicit Lean concept
and proves the safe two-witness theorem.

The key point is negative discipline:

```text
two selected witnesses exist
  does not mean
two independent delayed budgets exist
```

## Selected Pressure Predicate

New predicate:

```lean
IsSourcePressureDepth
```

Definition reading:

```text
j is selected when source continuation at depth r+j occupies
more than half of source retention at that depth.
```

Basic bridge:

```lean
isSourcePressureDepth_of_pressureOnRange
positive_sourceContinuationMass_of_isSourcePressureDepth
```

Meaning:

```text
range pressure + j < len
  -> IsSourcePressureDepth n k r j
  -> positive source continuation mass at depth r+j
```

## Witness Extraction

Positive count now has predicate-facing witnesses:

```lean
exists_isSourcePressureDepth_of_pressureDepthCount_pos
exists_isSourcePressureDepth_with_positive_mass
```

The first theorem packages the selected local pressure condition.
The second carries the positive mass together with it.

## Two Witnesses

New safe theorem:

```lean
exists_two_isSourcePressureDepths_of_two_le_pressureDepthCount
```

Caller-facing unpacked spelling:

```lean
exists_two_sourcePressureDepths_of_two_le_pressureDepthCount
```

Reading:

```text
2 <= sourceContinuationPressureDepthCount n k r len
  -> two distinct selected pressure depths exist
```

No budget addition is claimed.

## Depth-Two Budget Predicate

Checkpoint 121 had:

```lean
depthTwoPressureRange_positive_and_budget
```

Checkpoint 122 packages this as:

```lean
HasDepthTwoDelayedBudget
hasDepthTwoDelayedBudget_of_pressureOnRange_two_one
```

This gives later accounting the short proposition:

```text
HasDepthTwoDelayedBudget n k
```

instead of carrying the whole positive-mass and inequality pair by hand.

## Python Overlap Scan

New script:

```text
python/Collatz/PetalBridge/selected_depth_overlap_scan.py
```

Generated:

```text
python/Collatz/PetalBridge/results/selected_depth_overlap_scan.csv
python/Collatz/PetalBridge/results/selected_depth_overlap_scan.md
```

Default command:

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

## Interpretation

The finite observation strongly suggests that selected depths often form nested
or overlapping continuation-index sets.

This means the next multi-budget theorem should not start from:

```text
selected depths are automatically independent
```

The safer next vocabulary is:

```text
SelectedDepthOverlapControlled
NestedSelectedPressureDepths
DisjointTowerTargets, only under an explicit disjointness hypothesis
```

## Next Work

The next checkpoint should choose one of two routes:

```text
1. prove a thin overlap predicate API
2. keep one-witness delayed budget and search for an iterative obstruction
```

The Python scan currently favors route 1: overlap/nesting is visible and should
be named before any budget summation theorem is attempted.
