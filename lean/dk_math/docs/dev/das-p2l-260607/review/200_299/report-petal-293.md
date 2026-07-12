# Petal implementation report cp-293

## Implemented

- Projection of `sourcePressureUnresolvedInternalPairFamily` to left
  endpoints is bounded by the pair-family cardinality.
- Added `sourcePressureFiniteWindowBoundaryWitnesses`, the unified boundary
  carrier for in-window positive witnesses with no in-window adjacent
  successor.
- Added its exact membership theorem.
- Proved the residue classification:

```text
positiveCoverageResidue
  subset unresolvedInternalLeftWitnesses union boundaryWitnesses
```

- The named canonical packing-unit family from cp-292 now has a cardinality
  bridge to the canonical pair family.

## What is established

The residue is no longer opaque. Every positive witness omitted from the
canonical-left family is classified by a concrete finite carrier:

```text
unresolved internal adjacent pair
or
no in-window adjacent successor
```

The first component has the bound
`unresolvedInternalLeftWitnesses.card <= unresolvedInternalPairFamily.card`.

## Remaining boundary theorem

The target

```text
boundaryWitnesses.card <= 1
```

was not asserted. The unified boundary definition is correct, but its proof
requires a reusable list-order theorem: in a sorted witness list, two distinct
in-window witnesses cannot both lack an in-window adjacent successor. The
current API has adjacent-pair order and head-value lemmas, but not yet the
needed direct “every non-last entry has its successor” or last-element
characterization.

Therefore the endpoint-corrected `+ 1` inequalities remain pending. The exact
remaining work is list endpoint infrastructure, not a pressure or arithmetic
obstruction.

## Verification

Passed:

```text
lake build DkMath.Collatz.PetalBridge.PressureState.FiniteWindowPacking
```

`git diff --check` and the no-new-`sorry` check remain clean. Existing
unrelated project warnings are unchanged.

## Next target

Add the minimal list theorem connecting an element with no adjacent successor
to the final list entry, then prove boundary cardinality at most one. This will
immediately yield the endpoint-corrected local-Big inequalities and their
internal-coverage specialization.
