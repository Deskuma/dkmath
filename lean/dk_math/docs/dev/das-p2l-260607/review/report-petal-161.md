# Report Petal 161

## Checkpoint

Checkpoint 161 stayed on the main Collatz/PetalBridge root and implemented
reverse-branch recovery for a failed explicit local-island witness pair.

Modified implementation file:

- `DkMath/Collatz/PetalBridge/PressureAccounting.lean`

No `OneCycle`, `ValuationFlowBridge`, `ABC`, or `NumberTheory` files were
modified.

## Reversed Pair Accounting Family

The recovered reversed-pair family alias was added.

```lean
def sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
```

It is defined by swapping the supplied pair and reusing the sorted pair
constructor:

```lean
sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessPair W2 W1 hrev
```

This is only a two-witness local recovery.  It is not a global sorting
algorithm, not a maximal-family construction, and not union accounting.

## Structure Theorems

The length theorem was added.

```lean
theorem sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_length
```

The items theorem was also added.

```lean
theorem sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_items
```

The recovered family lists the converted intervals in swapped order:

```text
W2 interval, then W1 interval
```

## Recovered Budget

The recovered two-witness budget theorem was added.

```lean
theorem sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_sum_le_neg_two
```

The strict negative theorem was also added.

```lean
theorem sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_sum_neg
```

Both are direct consequences of the existing sorted pair budget applied to the
swapped pair.

## Failure-Reversed Wrappers

The failure-use wrappers were added.

```lean
theorem sourcePressureLocalIslandWitnessPair_failure_reversed_sum_le_neg_two
theorem sourcePressureLocalIslandWitnessPair_failure_reversed_sum_neg
```

The failure hypothesis is intentionally unused in the proof.  It documents the
intended use case:

```text
[W1, W2] failed as ordered,
but the reason is W2 before W1,
so the swapped pair recovers the sorted two-interval budget.
```

## Extra: Recovered-or-Overlap Split

The suggested next-step theorem also closed cleanly, so it was added.

```lean
theorem sourcePressureLocalIslandWitnessPair_failure_recovered_or_overlap
```

It states that a failed pair, with positive converted lengths, is either:

```text
recoverable by a reversed sorted accounting family with sum ≤ -2
```

or:

```text
an overlap obstruction
```

This is the useful Core split:

```text
failure
  -> reverse branch: recover budget
  -> overlap branch: leave as obstruction
```

## Boundary Notes

The overlap branch remains unhandled.

This checkpoint does not merge intervals, split intervals, prove coverage, or
construct union accounting.  It only recovers the reversed two-witness branch.

This checkpoint does not introduce:

- maximality,
- uniqueness of pressure families,
- coverage,
- prefix behavior,
- union accounting,
- Collatz convergence.

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

See the final Codex response for the pass/fail status of the final gate.

## Next Inference

The reverse branch is now operationally closed at the two-witness level.

The next safe direction is to isolate the overlap branch further, for example
with a named obstruction predicate for:

```text
pair failure whose reason is overlap
```

That should still avoid merge/split or union accounting until the exact
interval hypotheses are available.
