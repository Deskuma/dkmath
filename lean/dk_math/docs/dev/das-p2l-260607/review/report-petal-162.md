# Report Petal 162

## Checkpoint

Checkpoint 162 stayed on the main Collatz/PetalBridge root and gave the
overlap branch a first-class obstruction predicate.

Modified implementation file:

- `DkMath/Collatz/PetalBridge/PressureAccounting.lean`

No `OneCycle`, `ValuationFlowBridge`, `ABC`, or `NumberTheory` files were
modified.

## Overlap Symmetry

Overlap symmetry was added at all three intended layers.

```lean
theorem NatIntervalsOverlap.symm
theorem SourcePressureIntervalPulseAddressOverlap.symm
theorem SourcePressureLocalIslandWitnessOverlap.symm
```

These are purely local symmetry facts for two supplied intervals, addresses,
or witnesses.

## Before-Exclusion Diagnostics

Address-level diagnostics were added:

```lean
theorem SourcePressureIntervalPulseAddressOverlap.not_before
theorem SourcePressureIntervalPulseAddressOverlap.not_reverseBefore
```

Witness-level diagnostics were added:

```lean
theorem SourcePressureLocalIslandWitnessOverlap.not_before
theorem SourcePressureLocalIslandWitnessOverlap.not_reverseBefore
```

These make the intended obstruction reading explicit:

```text
overlap
  -> not forward before
  -> not reverse before
```

Therefore overlap cannot be repaired by simply swapping the pair.

## Overlap Obstruction Predicate

The first-class pair obstruction predicate was added.

```lean
def SourcePressureLocalIslandWitnessPairOverlapObstruction
```

It packages exactly:

```text
SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2]
and
SourcePressureLocalIslandWitnessOverlap W1 W2
```

Constructor and projections:

```lean
theorem SourcePressureLocalIslandWitnessPairOverlapObstruction.mk_of_failure_overlap
theorem SourcePressureLocalIslandWitnessPairOverlapObstruction.failure
theorem SourcePressureLocalIslandWitnessPairOverlapObstruction.overlap
```

Additional diagnostics:

```lean
theorem SourcePressureLocalIslandWitnessPairOverlapObstruction.not_before
theorem SourcePressureLocalIslandWitnessPairOverlapObstruction.not_reverseBefore
theorem SourcePressureLocalIslandWitnessPairOverlapObstruction.not_recoverable_by_swap
```

The last theorem is the important distinction from the reverse branch:

```text
reverse branch:
  swapping recovers sorted accounting

overlap branch:
  swapping cannot recover sortedness
```

## Recovered-or-Obstruction Split

The recovered-or-obstruction theorem was added.

```lean
theorem sourcePressureLocalIslandWitnessPair_failure_recovered_or_overlapObstruction
```

It refines the previous recovered-or-overlap split by wrapping the overlap
branch as a named obstruction:

```text
pair failure
  -> reversed recovered accounting with sum <= -2
  or overlap obstruction
```

## Boundary Notes

Overlap remains unmerged and unhandled.

This checkpoint does not:

- merge intervals,
- split intervals,
- construct a merged family,
- prove union accounting,
- prove coverage,
- assert maximality,
- assert uniqueness,
- assert prefix behavior,
- assert Collatz convergence.

All statements remain local to explicitly supplied witness pairs.

## Verification

The following command was run during implementation:

```bash
lake build DkMath.Collatz.PetalBridge.PressureAccounting
```

It passed.

Final verification gate:

```bash
lake build DkMath.Collatz.PetalBridge.PressureAccounting
lake build DkMath.Collatz.PetalBridge.PressureFrontier
lake build DkMath.Collatz.PetalBridge
rg -n "\\bsorry\\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
rg -n "\\bsorry\\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
git diff --check
```

Result:

```text
PASS lake build DkMath.Collatz.PetalBridge.PressureAccounting
PASS lake build DkMath.Collatz.PetalBridge.PressureFrontier
PASS lake build DkMath.Collatz.PetalBridge
PASS no sorry in PressureAccounting.lean
PASS no sorry in PressureFrontier.lean
PASS git diff --check
```

The `PetalBridge` build still reports the existing unrelated warning from
`DkMath.NumberTheory.ZsigmondyCyclotomicResearch`; this checkpoint did not touch
that file.

## Next Inference

The pair failure split is now structurally clear:

```text
recoverable reversed branch
unrecoverable overlap obstruction branch
```

The next safe direction is not union accounting.  A better next step is to add
small API around the obstruction branch, such as projections from obstruction
to both list failures:

```text
[W1, W2] not sorted
[W2, W1] not sorted
```

This would keep overlap obstruction isolated while making it easier for later
merge/split experiments to consume.
