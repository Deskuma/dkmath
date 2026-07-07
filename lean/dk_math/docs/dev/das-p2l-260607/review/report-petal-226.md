# Report: petal-226

## Checkpoint

`petal-226` resumed mathematical work after the mechanical split and targeted
`DkMath.Collatz.PetalBridge.PressureBeam.Pulse`.

The goal was to decide whether an explicitly contained witness can expose a
single caller-facing local diagnostic package.

## Implemented Theorem

Added in `PressureBeam/Pulse.lean`:

```lean
sourcePressureBeamPulse_witness_singleton_full_diagnostic
```

The theorem starts from one explicit list membership:

```lean
W ∈ L
```

and packages the three local facts:

```text
entry:
  left < right

center/right:
  SourcePressureBeamAddressedDepthTarget L ...

exit:
  right <= left
```

This remains one witness / one explicit list membership.  It does not claim
coverage of a list, family aggregation, canonical target selection, overlap
repair, propagation, or convergence.

## Existing API Consumed

The new theorem consumes existing `Pulse` API:

```lean
sourcePressureBeamPulse_witness_singleton_massBalance_edges
sourcePressureBeamPulse_witness_singleton_depth_and_exit_massBalance
```

The proof deliberately avoids rebuilding the edge facts directly.  It only
bundles the caller-facing pieces already proved by the smaller projections.

## Why Add It?

The existing API was mathematically sufficient, but a downstream caller would
otherwise need to call two separate theorems and manually combine:

- entry mass-balance;
- addressed depth;
- exit mass-balance.

The new theorem reduces that proof noise while preserving the local-only
contract.

## cp225 Compatibility

No public names from cp225 were renamed or removed.

The post-split module layout remains:

```text
PressureBeam.Core
  -> PressureBeam.Edge
  -> PressureBeam.Pulse
  -> PressureBeam
```

## Line Counts

Touched file:

```text
213  DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean
```

The small `Pulse` file remains well below the refactor threshold.

## Verification

Completed:

```text
lake build DkMath.Collatz.PetalBridge.PressureBeam.Pulse
lake build DkMath.Collatz.PetalBridge.PressureBeam
lake build DkMath.Collatz.PetalBridge
rg -n "\bsorry\b|admit" over PressureBeam split files
git diff --check
```

The inspected pressure files have no new `sorry` / `admit` matches.

Known unrelated project warning remains:

```text
DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:152:6:
declaration uses 'sorry'
```

## Next Inference

The Pulse-level witness singleton diagnostic is now caller-friendly.  The next
safe step is to use it from a higher diagnostic/automaton layer only when a
concrete caller needs the bundled entry-depth-exit shape.

Avoid turning this into list-wide coverage or witness-family aggregation until
exact list membership, non-overlap, and coverage hypotheses are explicitly
available.
