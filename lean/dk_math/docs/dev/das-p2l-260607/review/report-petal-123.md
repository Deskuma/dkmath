# Report Petal 123

## Goal

Checkpoint 123 asked for a Lean explanation of the selected-depth overlap seen
in checkpoint 122.

The target was:

```text
deep all-ones continuation residue
  -> shallow all-ones continuation residue
```

and then the corresponding finite-window count monotonicity.

## Lean Result

Implemented in:

```text
lean/dk_math/DkMath/Collatz/PetalBridge.lean
```

New pointwise theorem:

```lean
allOnes_mod_pow_two_of_allOnes_mod_pow_two_of_le
```

New count theorems:

```lean
sourceContinuationMass_anti_mono_depth
tailContinuationMass_anti_mono_depth
```

New selected-depth wrappers:

```lean
selectedContinuationMass_nested_of_lt
selectedContinuationMass_overlap_of_lt_of_deeper_pos
```

Meaning:

```text
j1 < j2
  -> mass at r+j2 <= mass at r+j1

positive mass at the deeper selected depth
  -> positive mass at the shallower selected depth
```

This closes the formal explanation that selected-depth carriers overlap because
they are nested all-ones residue cylinders.

## Python Experiment

Updated:

```text
python/Collatz/PetalBridge/selected_depth_overlap_scan.py
```

Regenerated:

```text
python/Collatz/PetalBridge/results/selected_depth_overlap_scan.csv
python/Collatz/PetalBridge/results/selected_depth_overlap_scan.md
```

New fields:

```text
selected_depths_are_prefix
selected_depths_are_consecutive
max_selected_depth
missing_selected_depths
```

Default scan result:

```text
rows: 500
rows with at least two selected depths: 52
rows with a disjoint selected-depth pair: 0
rows where every selected-depth pair overlaps: 52
rows whose selected depths are a prefix from r_start: 500
nonempty prefix rows: 237 / 237
rows whose selected depths are consecutive: 500
nonempty consecutive rows: 237 / 237
max selected depth count: 6
max selected depth: 7
max pairwise overlap: 13
```

The prefix/consecutive observation is experimental.  It should not yet be
promoted to a theorem without a proof of pressure monotonicity or a precise
counterexample search.

## Documentation

Added:

```text
lean/dk_math/DkMath/Collatz/docs/Collatz-ContinuationNesting-123.md
```

Updated:

```text
lean/dk_math/DkMath/Collatz/README.md
lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
```

## Verification

Passed:

```text
lake build DkMath.Collatz.PetalBridge
lake build DkMath.Collatz.Collatz2K26
```

## Next Implementation Candidate

The natural next checkpoint is to decide whether the experimental prefix
behavior can be formalized.

Candidate thin predicates:

```lean
def SelectedPressurePrefix ...
def HasDeepestSelectedSourcePressureDepth ...
```

Safer first theorem:

```text
if selected depth e is positive and d <= e,
then the continuation mass at d is positive
```

This is already nearly available from checkpoint 123.  What remains is to
connect it back to the pressure predicate itself.  That connection may be true
only under additional monotonicity assumptions, because pressure compares
continuation mass against retention mass, not continuation mass alone.
