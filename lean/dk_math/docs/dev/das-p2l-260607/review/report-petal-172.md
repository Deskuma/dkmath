# Report Petal 172

## Checkpoint

`cp: 172`

Main root only: list-level adjacent diagnosis carrier.

## Implemented

### Adjacent pair address predicate

Added:

```lean
def SourcePressureLocalIslandWitnessAdjacentPairInList
```

This predicate recognizes only ordered neighboring pairs in an explicitly
supplied witness list.  It is intentionally weaker than arbitrary pair
membership and does not sort, merge, classify, or claim uniqueness.

### Constructors

Added:

```lean
theorem SourcePressureLocalIslandWitnessAdjacentPairInList.head
theorem SourcePressureLocalIslandWitnessAdjacentPairInList.tail
```

These give the two intended address moves:

- the head pair is adjacent;
- an adjacent pair in the tail remains adjacent after a new head is added.

### Short-list negative facts

Added:

```lean
theorem SourcePressureLocalIslandWitnessAdjacentPairInList.nil_false
theorem SourcePressureLocalIslandWitnessAdjacentPairInList.singleton_false
```

These fix the boundary condition that empty and singleton witness lists have no
adjacent pair.

### List-level adjacent diagnosis carrier

Added:

```lean
def SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis
theorem SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_adjacent
```

This packages:

```text
some adjacent pair in this explicit list
+ an adjacent diagnosis attached to that pair
```

Recovered budget evidence remains attached to the adjacent pair that produced
it.  Overlap evidence remains an obstruction on the enclosing list.

### Short-list no-diagnosis facts

Added:

```lean
theorem SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.nil_false
theorem SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.singleton_false
```

These follow by projecting the adjacent-pair address and using the short-list
negative facts.

### Bounded wrappers

Added:

```lean
theorem sourcePressureLocalIslandWitnessList_failure_three_hasAdjacentDiagnosis
theorem sourcePressureLocalIslandWitnessList_failure_four_hasAdjacentDiagnosis
```

These wrap the already available bounded three- and four-witness diagnosis
carriers into the new list-level carrier.

## Boundary

This checkpoint does not introduce:

- arbitrary-length failure to adjacent diagnosis;
- a recursive classifier;
- sorting;
- coverage;
- maximality;
- uniqueness;
- union accounting;
- Collatz convergence.

The new layer is only an address carrier over explicit bounded witness lists.

## Verification

Builds completed:

```text
lake build DkMath.Collatz.PetalBridge.PressureAccounting
lake build DkMath.Collatz.PetalBridge.PressureFrontier
lake build DkMath.Collatz.PetalBridge
```

No-sorry checks completed for:

```text
lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
```

Whitespace check completed:

```text
git diff --check
```

The build still reports the existing unrelated warning:

```text
DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:152:6:
declaration uses `sorry`
```

## Next Inference

The new carrier creates a cleaner public surface for bounded diagnostics:
future callers can consume `SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis`
without destructuring whether the evidence came from the head pair or a tail
pair.  The next natural step, if requested, is still bounded: add small
projection/elimination helpers for this list-level carrier, not a general
classifier.
