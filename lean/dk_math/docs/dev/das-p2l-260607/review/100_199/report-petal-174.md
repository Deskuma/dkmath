# Report Petal 174

## Checkpoint

`cp: 174`

Main root only: sharp projection for list-level adjacent diagnosis, then
bounded length-five wrapper.

## Implemented

### Sharp recovered-or-overlap projection

Added:

```lean
theorem SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.exists_recovered_or_overlap
```

This projects a list-level adjacent diagnosis into exactly one of:

```text
some addressed adjacent pair with pair-local recovered budget
or
the sharp adjacent-overlap obstruction on the enclosing list
```

Unlike `exists_recovered_or_listFailure`, this theorem does not weaken the
overlap branch into ordinary sorted-before failure.  The overlap obstruction
remains unmerged and unhandled.

### Bounded length-five wrapper

Added:

```lean
theorem sourcePressureLocalIslandWitnessList_failure_five_hasAdjacentDiagnosis
```

The proof is bounded and follows the existing pattern:

```text
one-step head/tail diagnosis
  head: package the head-pair diagnosis
  tail: use the length-four wrapper and lift by of_tail
```

This extends the explicit witness-list surface to five witnesses without
introducing a general recursive classifier.

## Boundary

Recovered budgets remain attached to the adjacent pair that produced them.

Overlap remains an adjacent obstruction on the enclosing list.  No interval
merge, repair step, or union accounting was added.

This checkpoint did not introduce:

- arbitrary-length failure to adjacent diagnosis;
- a fuel-indexed classifier;
- sorting;
- coverage;
- maximality;
- uniqueness;
- prefix behavior;
- union accounting;
- Collatz convergence.

## Refactor Observation

`PressureAccounting.lean` is now about 3773 lines.  The next structural task
should not be a broad rewrite.  A gradual split should start with the bounded
adjacent-diagnosis surface around:

```text
SourcePressureLocalIslandWitnessAdjacentDiagnosis
SourcePressureLocalIslandWitnessAdjacentPairInList
SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis
```

The current checkpoint intentionally avoided moving declarations, so the
review diff stays small and theorem names remain stable.

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

Length five confirms the bounded pattern.  The next checkpoint should either
design the type shape for a bounded-recursion helper, or begin a gradual file
split for the adjacent-diagnosis API.  It should still avoid arbitrary list
classification until the type boundary is reviewed.
