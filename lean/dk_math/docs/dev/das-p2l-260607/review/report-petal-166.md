# Report Petal 166

## Checkpoint

Checkpoint 166 stayed on the main Collatz/PetalBridge root and exposed small
constructor/projection API for propagating tail failure and tail adjacent
overlap obstruction through a new list head.

Modified implementation file:

- `DkMath/Collatz/PetalBridge/PressureAccounting.lean`

No `OneCycle`, `ValuationFlowBridge`, `ABC`, or `NumberTheory` files were
modified.

## Sorted-Before Failure Constructors

The head not-before constructor was added:

```lean
theorem
  SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.cons_of_head_not_before
```

Meaning:

```text
not (W1 before W2)
  -> failure for W1 :: W2 :: rest
```

The tail failure constructor was added:

```lean
theorem
  SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.cons_of_tail
```

Meaning:

```text
failure for W2 :: rest
  -> failure for W1 :: W2 :: rest
```

The optional unification theorem was also added:

```lean
theorem
  SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.cons_of_head_or_tail
```

This is just a case split over the two recursive failure branches.

## Adjacent Overlap Tail Propagation

A readable alias for adjacent-overlap tail propagation was added:

```lean
theorem
  SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.of_tail
```

This aliases the existing `cons_of_tail` constructor.

## Tail Adjacent Obstruction To List Failure

The tail adjacent-overlap obstruction to full-list failure theorem was added:

```lean
theorem
  SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.of_tailAdjacentOverlapObstruction
```

Meaning:

```text
adjacent overlap obstruction in W2 :: rest
  -> sorted-before failure in W1 :: W2 :: rest
```

This is propagation only.  It does not inspect or repair the tail obstruction.

## Boundary Notes

This checkpoint is constructor API only.

Overlap remains unmerged and unhandled.

This checkpoint does not:

- implement sorting,
- classify arbitrary list failures,
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

The next safe target is the inverse direction:

```lean
theorem SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.head_or_tail
```

Expected shape:

```text
failure for W1 :: W2 :: rest
  -> not (W1 before W2)
  or failure for W2 :: rest
```

This would let callers peel one adjacent failure layer at a time.  It should
still remain a decomposition theorem, not a sorting algorithm.
