# Report Petal 173

## Checkpoint

`cp: 173`

Main root only: projection and propagation helpers for list-level adjacent
diagnosis.

## Implemented

### Adjacent-pair decomposition

Added:

```lean
theorem SourcePressureLocalIslandWitnessAdjacentPairInList.head_or_tail
theorem SourcePressureLocalIslandWitnessAdjacentPairInList.cons_iff_head_or_tail
```

These expose the definitional split of an adjacent-pair address in a cons list:

```text
head pair, or adjacent pair in the tail
```

The theorem is address plumbing only.  It does not turn adjacent-pair evidence
into arbitrary pair membership.

### List-level carrier eliminator

Added:

```lean
theorem SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.elim
```

This exposes the addressed pair and its local adjacent diagnosis to downstream
callers.

### Head and tail constructors

Added:

```lean
theorem SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_head
theorem SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_tail
```

`of_head` packages a diagnosis on the head pair.  `of_tail` propagates a
diagnosis through a newly supplied head by lifting the adjacent-pair address and
using `SourcePressureLocalIslandWitnessAdjacentDiagnosis.lift_tail`.

Recovered budget evidence remains attached to the same adjacent pair.  Only the
enclosing-list overlap branch is transported to the larger list.

### Bounded tail propagation helpers

Added:

```lean
theorem SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_tail_tail
theorem SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_tail_tail_tail
```

These are named two-step and three-step compositions of `of_tail`.  They are
bounded helper API, not a general recursive classifier.

### Recovered-or-list-failure projection

Added:

```lean
theorem SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.exists_recovered_or_listFailure
```

This projects a list-level adjacent diagnosis into:

```text
some addressed adjacent pair with pair-local recovered budget
or
ordinary sorted-before failure of the enclosing list
```

It is a wrapper around
`SourcePressureLocalIslandWitnessAdjacentDiagnosis.recovered_or_listFailure`.

## Boundary

This checkpoint introduced helper API only.

It did not introduce:

- arbitrary-length failure to adjacent diagnosis;
- a fuel-indexed classifier;
- sorting;
- coverage;
- maximality;
- uniqueness;
- prefix behavior;
- union accounting;
- interval merging;
- Collatz convergence.

Overlap remains unmerged and unresolved as an enclosing-list obstruction.

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

The API now has enough projection and propagation helpers for bounded
diagnostic consumers.  The next useful step should still remain bounded:
either build a small length-five wrapper from the existing four-witness carrier
and `of_tail`, or add eliminators that separate recovered evidence from overlap
without introducing a general recursive classifier.
