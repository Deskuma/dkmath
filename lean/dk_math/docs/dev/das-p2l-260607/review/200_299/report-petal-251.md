# Report: petal-251

## Goal

Project margin sign patterns from `SourcePressureOrientedNeighborDiagnosticState`.

## Implemented

Added in `DkMath.Collatz.PetalBridge.PressureState`:

```lean
theorem sourcePressureOrientedNeighborDiagnosticState_left_center_margin_signs
theorem sourcePressureOrientedNeighborDiagnosticState_right_center_margin_signs
```

Both theorems expose the centered three-margin pattern from state `D`:

```text
previous margin <= 0
center margin   >  0
addressed depth target
next margin     <= 0
```

The left theorem projects this pattern for `W`; the right theorem projects the
same pattern for `W'`.

## Proof Shape

Each proof reads only already-stored local state evidence:

- local-island witness property for the previous-margin nonpositivity,
- entry mass-balance comparison at `val - 1` for center positivity,
- addressed depth target from the oriented diagnostic state,
- exit mass-balance comparison at `val` for next-margin nonpositivity.

The index step

```text
r + (val - 1) + 1 = r + val
```

is discharged by `omega`.

## Automaton Reading

State `D` now has direct diagnostic projections:

```text
D(W,W') -> signs(W)
D(W,W') -> signs(W')
```

This makes the oriented neighbor state usable without manually unpacking all
mass-balance fields at call sites.

## Guardrails

These are projection theorems only.  They do not add:

- transport or propagation,
- list-wide coverage,
- canonical witness selection,
- overlap repair,
- aggregation,
- convergence or Collatz termination.

## Verification

Passed:

```text
lake build DkMath.Collatz.PetalBridge.PressureState
lake build DkMath.Collatz.PetalBridge
git diff --check
```

