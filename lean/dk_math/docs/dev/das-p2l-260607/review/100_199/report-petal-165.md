# Report Petal 165

## Checkpoint

Checkpoint 165 stayed on the main Collatz/PetalBridge root and added a
head-pair failure-reason API for explicit local-island witness lists.

Modified implementation file:

- `DkMath/Collatz/PetalBridge/PressureAccounting.lean`

No `OneCycle`, `ValuationFlowBridge`, `ABC`, or `NumberTheory` files were
modified.

## Head-Pair Recovered-Or-Overlap

The head-pair naming bridge was added:

```lean
theorem
  sourcePressureLocalIslandWitnessList_headPair_failure_recovered_or_overlapObstruction
```

This is a thin alias over the existing pair theorem:

```lean
sourcePressureLocalIslandWitnessPair_failure_recovered_or_overlapObstruction
```

It remains pair-local.  It does not inspect or sort a list tail.

## Head Obstruction Embedding

The head-pair overlap obstruction embedding was added:

```lean
theorem
  SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.of_headPairObstruction
```

This embeds:

```text
PairOverlapObstruction W1 W2
  -> AdjacentOverlapObstruction (W1 :: W2 :: rest)
```

The tail is only carried as part of the explicit list.  No arbitrary-pair search
or cluster construction is introduced.

## Head Obstruction To List Failure

The direct sorted-before failure wrapper was added:

```lean
theorem
  SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.of_headPairOverlapObstruction
```

This uses the adjacent obstruction predicate and the existing implication:

```lean
SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.hasSortedBeforeFailure
```

## Recovered-Or-Adjacent-Obstruction

The main list-facing split was added:

```lean
theorem
  sourcePressureLocalIslandWitnessList_headPair_failure_recovered_or_adjacentOverlapObstruction
```

Meaning:

```text
failed first adjacent pair
  -> recovered reversed-pair budget
  or adjacent overlap obstruction at the list head
```

This is head-pair only.  It does not classify failures deeper in the list and
does not perform list-wide sorting.

## Recovered-Or-List-Failure

The optional weakened branch theorem was also added:

```lean
theorem
  sourcePressureLocalIslandWitnessList_headPair_failure_recovered_or_listFailure
```

Meaning:

```text
failed first adjacent pair
  -> recovered reversed-pair budget
  or ordinary sorted-before failure for the explicit list
```

This is useful for callers that do not need to inspect the overlap obstruction
itself.

## Boundary Notes

Overlap remains unmerged and unhandled.

This checkpoint does not:

- implement a list-wide sorting algorithm,
- classify arbitrary list failures,
- search for non-adjacent overlap pairs,
- define overlap clusters,
- merge intervals,
- split intervals,
- construct merged interval families,
- prove union accounting,
- prove coverage,
- assert maximality,
- assert uniqueness,
- assert prefix behavior,
- assert Collatz convergence.

All statements remain local to explicitly supplied witness lists and their head
pair.

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

The next safe target is tail failure propagation.

Current checkpoint handles the head pair:

```text
W1 :: W2 :: rest
```

The next checkpoint can add constructors showing that if a tail already has a
recovered-or-adjacent-obstruction split, then consing a new head preserves the
adjacent obstruction branch.  This still should not become a full sorting
algorithm.
