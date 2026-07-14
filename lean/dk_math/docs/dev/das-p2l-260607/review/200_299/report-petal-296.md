# Petal implementation report cp-296

## Semantic collapse of the pair state

The apparent three-layer pair payload has been reduced to the actual
diagnostic payload.

```text
OrientedNeighborBoxState
  <-> OrientedNeighborDiagnosticState
  <-> AdjacentDiagnosis       (under ordered adjacency)
```

The first equivalence is unconditional: the oriented diagnostic already
constructs both endpoint pulse boxes.  The second uses the existing forward
diagnostic producer and an explicit adjacent-pair hypothesis.

## Canonical state characterization

Under sortedness, ordered adjacency, and explicit internal window bounds:

```text
CanonicalFiniteWindowPackingState
  <-> OrientedNeighborBoxState
  <-> AdjacentDiagnosis
```

Thus the canonical separator is not an additional independent phenomenon. It
is the finite-window packaging of the adjacent diagnosis.

## Unresolved pair meaning

The unresolved internal family now has a direct sorted membership theorem:

```text
pair is unresolved
  <-> pair is in zip(L, L.tail)
   and both centers are in the window
   and the pair lacks AdjacentDiagnosis
```

The semantic alias `sourcePressureUndiagnosedInternalPairFamily` exposes this
meaning without changing the existing carrier or counting results.

The previous box-obstruction predicate remains for compatibility, but its
three apparent branches are not independent: a full oriented diagnostic
constructs both pulse boxes.  The true missing payload is
`¬ SourcePressureLocalIslandWitnessAdjacentDiagnosis`.

## Producer audit result

Existing BeamSeed / SortedFailure / FailureResolution constructors produce a
diagnosed existential pair and therefore eliminate the obstruction for that
selected pair. They do not yet provide a universal theorem for every internal
adjacent pair in an arbitrary list.

The exact missing producer statement is therefore:

```text
internal adjacent pair -> AdjacentDiagnosis
```

or a positive disjunction separating recovered diagnosis from an existing
positive overlap/budget obstruction. No genuine recovered/overlap split was
asserted without such positive data.

## Local-Big surface

The strongest decomposition remains:

```text
positiveWitnesses.card
  <= half-window capacity + 2 + undiagnosedInternalPairFamily.card

positiveWitnesses.card
  <= nonpositive-position capacity + 1
       + undiagnosedInternalPairFamily.card
```

Under internal coverage, the undiagnosed family is empty and the endpoint-
corrected bounds from cp-294 apply.

## Verification

Passed:

```text
lake build DkMath.Collatz.PetalBridge.PressureState.FiniteWindowPacking
lake build DkMath.Collatz.PetalBridge.PressureState
lake build DkMath.Collatz.PetalBridge
git diff --check
```

No new `sorry` or `axiom` was introduced.

## Next target

Construct a positive per-pair producer for `AdjacentDiagnosis`, or formalize
the smallest positive obstruction data distinguishing recovered, overlap, and
budget-missing branches.
