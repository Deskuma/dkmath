# Report: petal-225

## Checkpoint

`petal-225` was a mechanical refactor checkpoint for
`DkMath.Collatz.PetalBridge.PressureBeam`.

No new mathematical theorem content was added.

## Split Performed

The former monolithic file was split into:

```text
DkMath.Collatz.PetalBridge.PressureBeam
  public aggregator

DkMath.Collatz.PetalBridge.PressureBeam.Core
  seed, addressed-depth, margin transition, and mass-balance core

DkMath.Collatz.PetalBridge.PressureBeam.Edge
  crossing-edge target, falling-edge target, edge-local classifiers,
  interval-pulse left/right edge bridges

DkMath.Collatz.PetalBridge.PressureBeam.Pulse
  local pulse-shape packaging and diagnostic-facing projections
```

The public `PressureBeam.lean` now imports `PressureBeam.Pulse`, which imports
`PressureBeam.Edge`, which imports `PressureBeam.Core`.

## Dependency Direction

The dependency direction remains clean:

```text
PressureAutomaton
  <- PressureBeam.Core
  <- PressureBeam.Edge
  <- PressureBeam.Pulse
  <- PressureBeam
```

No lower diagnostic module was changed to import a higher Beam module.  No
circular import was introduced.

## Public Names

Public theorem and definition names were not renamed.  The refactor moved the
existing declarations into submodules and kept `PressureBeam.lean` as the
public import surface.

Only file-identification comments and the aggregator comment were updated.

## Line Counts

Final line counts:

```text
27    DkMath/Collatz/PetalBridge/PressureBeam.lean
1437  DkMath/Collatz/PetalBridge/PressureBeam/Core.lean
303   DkMath/Collatz/PetalBridge/PressureBeam/Edge.lean
175   DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean
```

This removes the immediate pressure from the 2000-line split criterion and
leaves the newer edge/pulse vocabulary in small files.

## Verification

Completed:

```text
lake build DkMath.Collatz.PetalBridge.PressureBeam.Core
lake build DkMath.Collatz.PetalBridge.PressureBeam.Edge
lake build DkMath.Collatz.PetalBridge.PressureBeam.Pulse
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

## Scope

This checkpoint is purely mechanical.  It does not add:

- coverage;
- propagation;
- aggregation;
- overlap repair;
- canonical target selection;
- arbitrary target transport;
- Collatz convergence.

## Next Inference

With `PressureBeam` split, future checkpoints can choose a smaller target:

- `Core` for seed/addressed-depth/mass-balance algebra;
- `Edge` for exact entry/exit edge vocabulary;
- `Pulse` for local pulse packaging and diagnostic projections.

The next mathematical work should start in the smallest file that owns the
needed vocabulary, instead of rebuilding the monolithic file.
