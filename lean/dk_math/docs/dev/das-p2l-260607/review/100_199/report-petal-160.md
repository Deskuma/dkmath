# Report Petal 160

## Checkpoint

Checkpoint 160 stayed on the main Collatz/PetalBridge root and added local
trichotomy plus failure-reason split theorems for explicit intervals,
addresses, and local-island witnesses.

Modified implementation file:

- `DkMath/Collatz/PetalBridge/PressureAccounting.lean`

No `OneCycle`, `ValuationFlowBridge`, `ABC`, or `NumberTheory` files were
modified.

## Nat Interval Layer

The interval trichotomy theorem was added.

```lean
theorem NatIntervalsOverlap.before_or_reverseBefore_or_overlap
```

For two supplied half-open intervals, it returns:

```text
before A B
or before B A
or overlap A B
```

The failure-reason split was also added.

```lean
theorem NatIntervalsOverlap.reverseBefore_or_overlap_of_not_before
```

This theorem is the safe refinement of a failed ordered relation.  If `A` is
not before `B`, the reason is either reverse order or overlap.  A single failed
`before` relation is still not overlap evidence by itself.

## Address Layer

The address-level trichotomy theorem was added.

```lean
theorem SourcePressureIntervalPulseAddressOverlap.before_or_reverseBefore_or_overlap
```

The address-level failure-reason split was added.

```lean
theorem SourcePressureIntervalPulseAddressOverlap.reverseBefore_or_overlap_of_not_before
```

These theorems read only the explicit `start` and `len` fields of the supplied
`SourcePressureIntervalPulseAddress` values.

## Witness Layer

The witness-level trichotomy theorem was added.

```lean
theorem SourcePressureLocalIslandWitnessOverlap.before_or_reverseBefore_or_overlap
```

The witness-level failure-reason split was added.

```lean
theorem SourcePressureLocalIslandWitnessOverlap.reverseBefore_or_overlap_of_not_before
```

These wrappers operate through the converted interval-pulse addresses:

```lean
sourcePressureIntervalPulseAddress_of_localIslandWitness W
```

The length-positivity hypotheses remain explicit:

```lean
0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W1).len
0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len
```

## Pair Failure Refinement

The pair failure theorem was refined into a local reason split.

```lean
theorem sourcePressureLocalIslandWitnessPair_failure_reverseBefore_or_overlap
```

If `[W1, W2]` has a sorted-before failure, then with positive converted
lengths the failure is either:

```text
W2 before W1
or W1 overlaps W2
```

This is the desired diagnostic split:

- reverse order can be handled by reordering,
- overlap remains a real obstruction and is not solved here.

## Extra Reverse Recovery

The suggested next-step helper was also added because it closed cleanly.

```lean
theorem sourcePressureLocalIslandWitnessPair_sorted_swap_of_reverseBefore
```

If the pair failure is explained by reverse order, then the swapped list is
sorted:

```text
W2 before W1
----------------
[W2, W1] sorted
```

This is still only a two-witness local recovery theorem.  It does not create a
global sorting algorithm or a union-accounting family.

## Boundary Notes

`not before` alone is still not overlap evidence.

The safe failure interpretation is:

```text
not before
-------------------------
reverse before or overlap
```

with explicit positivity hypotheses for the interval lengths.

This checkpoint does not introduce:

- maximality,
- uniqueness of pressure families,
- coverage,
- prefix behavior,
- union accounting,
- Collatz convergence.

All statements remain local to explicitly supplied intervals, addresses, or
witnesses.

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

The next safe direction is to expose a recovery constructor:

```text
pair failure
reverse-before branch
--------------------------------
build the swapped sorted pair accounting family
```

The theorem already added in this checkpoint proves the sorted swapped list.
The next checkpoint can connect it to:

```lean
sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessPair W2 W1 hrev
```

and recover the existing two-interval budget for the reversed pair.  The
overlap branch should remain separate and should not be converted into union
accounting without new interval-merge hypotheses.
