# Report: petal-261

## Goal

Package the forward box comparison branch into a named predicate and expose
named split wrappers.

Desired surface:

```text
S/R/B + sorted(L)
  -> ForwardBoxComparisonState or PairOverlapObstruction
```

## Implemented

Added in `DkMath.Collatz.PetalBridge.PressureState`:

```lean
def SourcePressureForwardBoxComparisonState
```

The state packages:

```lean
SourcePressureOrientedNeighborBoxState L W W'
W.val < W'.val
not SourcePressureOrientedNeighborBoxState L W' W
```

Projection lemmas:

```lean
theorem SourcePressureForwardBoxComparisonState.box
theorem SourcePressureForwardBoxComparisonState.val_lt
theorem SourcePressureForwardBoxComparisonState.not_reverse_box
```

Constructor:

```lean
theorem SourcePressureOrientedNeighborBoxState.to_forwardComparisonState_of_sorted
```

Named split wrappers:

```lean
theorem sourcePressureFailureResolutionState_to_forwardBoxComparisonState_or_pairOverlap
theorem sourcePressureSortedFailureState_to_forwardBoxComparisonState_or_pairOverlap
theorem sourcePressureBeamSeedState_to_forwardBoxComparisonState_or_pairOverlap
```

## Meaning

The forward comparison branch no longer has to be passed around as a raw nested
conjunction.  It now has a stable state name:

```lean
SourcePressureForwardBoxComparisonState L W W'
```

This makes the next pair-comparison layer cleaner.  It can consume one named
state for the forward branch and leave the pair-overlap branch as the explicit
obstruction branch.

## Guardrails

The new state is only a packaging layer.  It does not add a new global
mathematical claim.

In particular, it does not:

* select a canonical pair;
* assert global coverage;
* repair overlaps;
* propagate local diagnostics;
* prove convergence.

The constructor from an oriented box still requires sortedness explicitly.

## Verification

Commands run from `lean/dk_math`:

```text
lake build DkMath.Collatz.PetalBridge.PressureState
lake build DkMath.Collatz.PetalBridge
```

Both builds completed successfully.

`git diff --check` is run as the final whitespace gate.

## Next Branch Prediction

The next layer can now define a pair-comparison theorem that consumes:

```lean
SourcePressureForwardBoxComparisonState L W W'
```

and keeps the obstruction side as:

```lean
SourcePressureLocalIslandWitnessPairOverlapObstruction A B
```

Candidate direction:

```text
ForwardBoxComparisonState
  -> pair-comparison-facing local order facts

PairOverlapObstruction
  -> obstruction-facing branch
```

The named state should reduce theorem signatures in the next checkpoint.
