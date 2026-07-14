# Report Petal 163

## Checkpoint

Checkpoint 163 stayed on the main Collatz/PetalBridge root and strengthened the
pair overlap-obstruction API.

Modified implementation file:

- `DkMath/Collatz/PetalBridge/PressureAccounting.lean`

No `OneCycle`, `ValuationFlowBridge`, `ABC`, or `NumberTheory` files were
modified.

## Swapped-List Failure

The swapped failure projection was added:

```lean
theorem SourcePressureLocalIslandWitnessPairOverlapObstruction.swap_failure
```

Meaning:

```text
overlap obstruction for [W1, W2]
  -> sorted-before failure for [W2, W1]
```

This fixes the expected diagnostic: overlap blocks both directions, unlike the
reverse-order branch which can be recovered by swapping.

## Not-Sorted Diagnostics

The direct not-sorted diagnostics were added:

```lean
theorem SourcePressureLocalIslandWitnessPairOverlapObstruction.not_sorted
theorem SourcePressureLocalIslandWitnessPairOverlapObstruction.not_sorted_swap
```

These are consumer-facing wrappers:

```text
obstruction -> not sorted [W1, W2]
obstruction -> not sorted [W2, W1]
```

The swapped version aliases the existing `not_recoverable_by_swap` theorem.

## Obstruction Symmetry

The obstruction predicate is now symmetric:

```lean
theorem SourcePressureLocalIslandWitnessPairOverlapObstruction.symm
theorem SourcePressureLocalIslandWitnessPairOverlapObstruction.symm_iff
```

This makes the overlap-obstruction reading order-independent:

```text
OverlapObstruction W1 W2
  iff
OverlapObstruction W2 W1
```

The proof uses:

- swapped sorted-before failure,
- symmetric witness overlap.

## Boundary Notes

Overlap remains unmerged and unhandled.

This checkpoint does not:

- merge intervals,
- split intervals,
- construct merged interval families,
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

The pair obstruction API is now stable enough for a list-level entrance.

The next safe target is an adjacent-pair predicate, not a global pair search:

```lean
def SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
```

The intended next theorem shape is:

```text
list sorted-before failure
  -> adjacent reverse recoverable
  or adjacent overlap obstruction
```

This would lift the pair obstruction one level upward while still avoiding
merge/split/union accounting.
