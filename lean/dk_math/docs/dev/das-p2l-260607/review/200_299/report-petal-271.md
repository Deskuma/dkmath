# Report: petal-271

## Goal

Add compact index-level center separation surfaces from
`SourcePressureForwardPairComparisonState`.

Target surfaces:

```text
FPC
  -> r + W.val < r + W'.val
  -> r + W.val != r + W'.val
```

and, where useful:

```text
FPC
  -> left/right boundary signs
  -> r + W.val < r + W'.val
  -> r + W.val != r + W'.val
```

## Implemented

Added the following theorems in
`DkMath.Collatz.PetalBridge.PressureState`:

```lean
SourcePressureForwardPairComparisonState.indexed_center_separation_surface
SourcePressureForwardPairComparisonState.indexed_boundary_separation_surface
```

The first theorem bundles:

```lean
h.center_index_lt
h.center_index_ne
```

The second theorem extends:

```lean
h.indexed_boundary_pair_surface
```

with:

```lean
h.center_index_ne
```

## Meaning

The forward pair-comparison branch now has a compact separation surface at the
same index level used by `SourcePressureMarginInt`.

This matters for the next interference/overlap readings.  Those callers usually
need both:

- strict center-index order;
- center-index noncoincidence.

The optional boundary version keeps the local pulse windows and the separation
facts together, avoiding repeated unpacking in later pair-comparison lemmas.

## Guardrails

This checkpoint only repackages already proved local facts.

It does not assert:

- a gap of at least two;
- non-overlap of the full pulse windows;
- uniqueness of positive centers;
- absence of other centers;
- global coverage;
- Collatz convergence.

The pair-overlap obstruction branch remains separate.

## Verification

Passed:

```text
lake build DkMath.Collatz.PetalBridge.PressureState
```

The final gate for this checkpoint also runs:

```text
lake build DkMath.Collatz.PetalBridge
git diff --check
```

## Next Branch Prediction

The next useful branch is probably a first negative/interference theorem:

```text
indexed_boundary_separation_surface
  -> the two center indices do not coincide
```

That is already available directly through the new surface.  If callers need a
single named obstruction-facing statement, add a theorem that projects the
noncoincidence while retaining the boundary context.
