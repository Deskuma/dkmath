# Collatz Continuation Nesting - Checkpoint 123

Checkpoint 123 closes the first formal explanation of the selected-depth
overlap observed at checkpoint 122.

The key point is simple:

```text
deep all-ones residue
  -> shallow all-ones residue
```

If a label is `-1` modulo a large power of two, then the same label is `-1`
modulo every smaller visible power-of-two layer.

## Lean Surface

The pointwise theorem is:

```lean
allOnes_mod_pow_two_of_allOnes_mod_pow_two_of_le
```

It has the shape:

```lean
q % (2 ^ (e + 1)) = 2 ^ (e + 1) - 1
  -> d <= e
  -> q % (2 ^ (d + 1)) = 2 ^ (d + 1) - 1
```

The proof uses the existing modulus bridge:

```lean
mod_eq_mod_of_dvd_modulus
```

and the divisibility:

```text
2^(d+1) divides 2^(e+1)
```

## Count Consequences

The count-level source theorem is:

```lean
sourceContinuationMass_anti_mono_depth
```

The shifted-tail counterpart is:

```lean
tailContinuationMass_anti_mono_depth
```

Both say that continuation mass is anti-monotone in depth:

```text
deeper continuation mass <= shallower continuation mass
```

This is not a probabilistic statement.  It is a finite-window subset statement
expressed through counts.

## Selected Depth Wrappers

For selected pressure-depth indices, checkpoint 123 adds:

```lean
selectedContinuationMass_nested_of_lt
selectedContinuationMass_overlap_of_lt_of_deeper_pos
```

The first theorem says that for `j1 < j2`, the continuation mass at `r + j2`
is bounded by the continuation mass at `r + j1`.

The second theorem packages the positive-mass consequence:

```text
positive deeper mass
  -> positive shallower mass
```

This is the formal "overlap is automatic" reading.  The deeper all-ones
continuation hits are already shallow all-ones continuation hits.

## Experimental Prefix Scan

The Python overlap scan was extended:

```text
python/Collatz/PetalBridge/selected_depth_overlap_scan.py
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

Default scan:

```text
odd n <= 999
steps = 64
r_start = 2
depth_len = 8
```

Observed summary:

```text
rows: 500
rows with at least two selected depths: 52
rows with a disjoint selected-depth pair: 0
rows where every selected-depth pair overlaps: 52
nonempty selected rows: 237
nonempty prefix rows: 237 / 237
nonempty consecutive rows: 237 / 237
max selected depth count: 6
max selected depth: 7
```

## Interpretation

Checkpoint 123 separates two facts:

```text
proved:
  continuation carriers are nested by depth

observed:
  pressure-selected depths often form a prefix
```

The first fact is now Lean-fixed.  The second is still an experiment.

This suggests the next useful concept is a prefix/tower predicate, for example:

```text
SelectedPressurePrefix
DeepestSelectedSourcePressureDepth
```

Such a predicate should not sum selected depths as independent budgets.  The
natural accounting object is the deepest selected continuation core together
with the prefix of shallower carriers that contain it.
