# Report Petal 164

## Checkpoint

Checkpoint 164 stayed on the main Collatz/PetalBridge root and lifted the
pair-level overlap obstruction to a minimal adjacent-list API.

Modified implementation file:

- `DkMath/Collatz/PetalBridge/PressureAccounting.lean`

No `OneCycle`, `ValuationFlowBridge`, `ABC`, or `NumberTheory` files were
modified.

## Adjacent Overlap Obstruction

The adjacent-list predicate was added:

```lean
def SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
```

It is recursive over neighboring witness pairs:

```text
[]
  -> false
[W]
  -> false
W1 :: W2 :: rest
  -> overlap obstruction at W1 W2
  or adjacent overlap obstruction in W2 :: rest
```

This is adjacent-only.  It does not quantify over arbitrary pairs in the list
and does not define an overlap cluster.

## Pair API

The pair equivalence was added:

```lean
theorem SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction_pair_iff
```

Constructors were added:

```lean
theorem SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.cons_of_head
theorem SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.cons_of_tail
```

Pair symmetry through the adjacent predicate was added:

```lean
theorem SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction_pair_symm
```

This reuses the pair obstruction symmetry from checkpoint 163.

## Sorted-Before Failure

The full-list implication was proved:

```lean
theorem SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.hasSortedBeforeFailure
```

This means:

```text
adjacent overlap obstruction in an explicit witness list
  -> ordinary adjacent sorted-before failure for that same explicit list
```

The pair specialization was also added:

```lean
theorem SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction_pair_hasSortedBeforeFailure
```

The full-list version was not deferred; the existing recursive sorted-before
failure predicate was compatible with the adjacent obstruction recursion.

## Boundary Notes

Overlap remains unmerged and unhandled.

This checkpoint does not:

- merge intervals,
- split intervals,
- construct merged interval families,
- define overlap clusters,
- quantify over arbitrary non-adjacent list pairs,
- prove union accounting,
- prove coverage,
- assert maximality,
- assert uniqueness,
- assert prefix behavior,
- assert Collatz convergence.

All statements remain local to explicitly supplied witness lists.

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

The next safe target is a head-pair failure reason theorem:

```text
head pair sorted-before failure
  -> reverse-recovered budget
  or overlap obstruction
```

This should still stay at the head-pair level before any attempt at list-wide
algorithmic processing.  It can reuse:

```lean
sourcePressureLocalIslandWitnessPair_failure_recovered_or_overlapObstruction
```

The expected next theorem can package the first adjacent failure in a list
without merging intervals or asserting coverage.
