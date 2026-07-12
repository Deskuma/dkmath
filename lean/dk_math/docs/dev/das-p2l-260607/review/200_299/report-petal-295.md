# Petal implementation report cp-295

## State simplification

Added the equivalence between the duplicated
`SourcePressureForwardPairComparisonState` and its underlying
`SourcePressureForwardBoxComparisonState`.

Under sorted adjacency, the forward box state is equivalent to the oriented
neighbor box state.  With explicit internal window bounds, the canonical
finite-window packing state is also equivalent to the oriented neighbor box.

This makes the canonical construction readable as:

```text
internal bounds + sorted adjacency + oriented neighbor box
  <-> canonical packing state
```

## Exact unresolved-pair obstruction

Added `SourcePressureInternalPairBoxObstruction`:

```text
missing oriented diagnostic
or missing left pulse box
or missing right pulse box
```

Its negated-box equivalence is proved.  Every unresolved internal pair carries
this obstruction, and the unresolved pair Finset has a direct membership
equivalence in terms of `¬ SourcePressureOrientedNeighborBoxState`.

Therefore the remaining unresolved count is not an opaque numerical gap. It is
exactly the count of internal adjacent pairs for which at least one local box
component has not been constructed.

## Producer audit

The existing BeamSeed / SortedFailure / FailureResolution hierarchy constructs
an existential forward pair and can therefore eliminate the obstruction for
that selected pair. It does not yet eliminate the obstruction for every
internal adjacent pair in an arbitrary list. The missing producer theorem is a
per-pair construction of `SourcePressureOrientedNeighborBoxState`.

## Existing local-Big result

The strongest current decomposition remains:

```text
positiveWitnesses.card
  <= (hi - lo) / 2 + 2 + unresolvedInternalPairFamily.card

positiveWitnesses.card
  <= nonposPositions.card + 1 + unresolvedInternalPairFamily.card
```

Under internal coverage, the unresolved family is empty and the endpoint-
corrected bounds follow.

## Verification

Passed:

```text
lake build DkMath.Collatz.PetalBridge.PressureState.FiniteWindowPacking
```

The new code contains no `sorry` or `axiom`. One existing style warning notes
a line longer than 100 characters; it does not affect the build.

## Next target

Add a per-pair producer theorem, preferably a disjunction of the oriented box
state and the explicit `SourcePressureInternalPairBoxObstruction`. This is the
next point at which the unresolved correction can be reduced rather than merely
counted.
