# Report: petal-224

## Checkpoint

`petal-224` asked whether the local pulse-shape package from cp223 should be
consumed by a downstream diagnostic or obstruction-facing layer.

The implemented answer is a small consumer layer in `PressureBeam.lean`.
No downstream diagnostic module was modified.

## What was inspected

The inspected modules were:

- `DkMath.Collatz.PetalBridge.PressureBeam`
- `DkMath.Collatz.PetalBridge.PressureLocalWitnessObstruction`
- `DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis`
- `DkMath.Collatz.PetalBridge.PressureDiagnosticDecomposition`
- `DkMath.Collatz.PetalBridge.PressureAutomaton`

The downstream diagnostic files are focused on explicit witness-list order
failure, adjacent pair recovery, and overlap obstruction.  They do not yet need
to own Beam entry/exit vocabulary directly.  Importing Beam facts back into
those lower layers would blur the current module split:

```text
PressureAutomaton
  <- PressureBeam
```

So the consumer theorem surface was added in `PressureBeam`, above the
diagnostic modules.

## Implemented theorem surface

Added:

```lean
sourcePressureBeamPulse_diagnostic_massBalance_of_intervalPulseAddress
sourcePressureBeamPulse_witness_singleton_depth_and_exit_massBalance
```

Both theorems deliberately consume the cp223 packaged shape.

For an interval pulse:

```lean
sourcePressureBeamPulse_edges_of_intervalPulseAddress A
```

is destructed into entry and exit edge targets, then projected to the paired
mass-balance comparison:

```text
entry:
  left < right

exit:
  right <= left
```

For a witness singleton:

```lean
sourcePressureBeamPulse_witness_singleton_shape hmem
```

is destructed into:

```text
entry crossing target
addressed depth target
exit falling target
```

and projected to the two diagnostic-facing facts:

```text
addressed depth at the singleton right/center edge
right <= left at the same exit edge
```

The membership hypothesis `W ∈ L` is still required for the addressed-depth
component because addressed targets are list-relative carriers.

## Why not edit the lower diagnostic files?

The obstruction and adjacent-diagnosis modules classify list order failure and
overlap.  They do not currently repeat entry/exit Beam reasoning.  Adding Beam
imports or Beam-specific predicates there would increase coupling without
reducing existing proof noise.

The new consumer layer gives future diagnostic callers a ready projection while
preserving the current dependency direction.

## Classification

- True Beam:
  The interval entry edge is consumed as `left < right`.

- DepthTarget:
  The witness singleton projection keeps the addressed depth target at the
  generated singleton right/center edge.

- Falling-or-Boundary:
  The exit edge is consumed as `right <= left`.

- Gap:
  No coverage, propagation, family aggregation, canonical target selection,
  overlap repair, arbitrary target transport, or Collatz convergence is claimed.

## File size / refactor note

`PressureBeam.lean` is now 1885 lines.  This is still below the 2000-line split
criterion, but close enough that the next few checkpoints should be careful.

If the next work adds another large section, the likely split point is the
edge/pulse vocabulary:

```text
PressureBeam.Edge
PressureBeam.Pulse
```

That split should be gradual and mechanical, not mixed with new theorem work.

## Verification

Completed:

```text
lake build DkMath.Collatz.PetalBridge.PressureBeam
lake build DkMath.Collatz.PetalBridge
rg -n "\bsorry\b|admit" over inspected pressure files
git diff --check
```

The inspected pressure files have no new `sorry` / `admit` matches.

Known unrelated project warning remains:

```text
DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:152:6:
declaration uses 'sorry'
```

## Next inference

The diagnostic consumer surface is now available without changing the lower
diagnostic modules.  The next natural step is either:

1. use these projections from a concrete downstream theorem, if a caller now
   needs the exact facts; or
2. start the gradual `PressureBeam` split before adding more large sections.

Given the file size, a split should be considered soon, but it does not need to
happen until a new checkpoint would push the file past the stated threshold.
