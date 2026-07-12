# report-petal-200

## Checkpoint

`petal-200` is an audit-only checkpoint.

No Lean theorem was added.  No import change was needed.  The purpose of this
checkpoint is to decide where the next Beam-facing pressure propagation layer
should live after `PressureAutomaton`.

## Current Pressure Chain

The lower drift/accounting chain is:

```text
DriftBudget
  <- PressureDecay
    <- PressureFrontier
      <- PressureAccounting
```

The current diagnostic/automaton chain is:

```text
PressureFrontier
  <- PressureAccounting
    <- PressureLocalWitnessObstruction
      <- PressureAdjacentDiagnosis
        <- PressureDiagnosticDecomposition
          <- PressureAutomaton
```

So the effective stack for the pressure series is:

```text
DriftBudget
  <- PressureDecay
    <- PressureFrontier
      <- PressureAccounting
        <- PressureLocalWitnessObstruction
          <- PressureAdjacentDiagnosis
            <- PressureDiagnosticDecomposition
              <- PressureAutomaton
```

## Ownership Map

### Local pressure drift / net-drop propagation

Owner: `DkMath.Collatz.PetalBridge.PressureDecay`

This module owns the local margin and net-drop vocabulary:

- `SourcePressureMarginInt`
- `SourceRetentionDropInt`
- `SourceContinuationDropInt`
- `SourcePressureNetDropInt`
- local transition theorems such as
  `sourcePressureMarginStepDiff_eq` and
  `sourcePressureMargin_next_eq_current_add_netDrop`
- local sign-change and pulse predicates:
  `SourcePressureSignChangeUp`,
  `SourcePressureSignChangeDown`,
  `SourcePressurePulse`,
  `SourcePressureSignPulse`

`DriftBudget` supplies lower residue/tail-count drift budgets, but the
pressure-margin transition language itself starts in `PressureDecay`.

### Interval pulse production

Owner: `DkMath.Collatz.PetalBridge.PressureFrontier`

This module owns the frontier and local-island producers:

- `SourcePressureFrontier`
- `SourcePressureLocalIsland`
- `ExistsSourcePressureLocalIslandBelow`
- `SourcePressureIntervalPulse`
- `SourcePressureIntervalPulseAddress`
- local-island-to-pulse/address constructors such as
  `sourcePressureIntervalPulse_singleton_of_localIsland` and
  `sourcePressureIntervalPulseAddress_of_localIsland`

This is the right level for producing a pulse from a local pressure event.  It
does not own witness-list accounting or diagnostic decomposition.

### Explicit witness-list accounting

Owner: `DkMath.Collatz.PetalBridge.PressureAccounting`

This module owns explicit carrier/list accounting:

- `SourcePressureIntervalNetDrop`
- `SourcePressureAccountedInterval`
- `SourcePressureAccountedIntervalFamily`
- sorted-before/failure carriers for accounted interval lists
- `SourcePressureLocalIslandWitness`
- conversion from local-island witnesses to pulse-address families
- singleton and sorted-list accounting theorems

This is the Core/local accounting layer.  It is intentionally witness-local:
it accounts for explicitly supplied witnesses and does not claim global
coverage, maximality, uniqueness, or convergence.

### Failure resolution automaton

Owner: `DkMath.Collatz.PetalBridge.PressureAutomaton`

This module currently names the already-proved diagnostic state:

```text
sorted-before failure
  -> recovered adjacent pair diagnostic
     or adjacent overlap obstruction
```

It also exposes the no-overlap consumer:

```text
sorted-before failure + no-adjacent-overlap
  -> recovered adjacent pair diagnostic
```

This is not a propagation layer.  It is a state-resolution API above
`PressureDiagnosticDecomposition`.

## Core / Automaton / Beam Split

### Core/local accounting

Core/local accounting is the finite arithmetic layer:

- pressure margin and net-drop arithmetic;
- pulse and local-island production;
- explicit interval accounting;
- explicit witness-list accounting.

This layer only speaks about data it is given.  It must not silently become a
global coverage theorem.

### Automaton/failure resolution

The automaton layer is a named control state over explicit witness lists.
It does not advance time, build a Beam, or repair overlap.  Its role is to say
what a local sorted-before failure means:

```text
recover a pair-local diagnostic, or expose overlap as the obstruction.
```

This is the current role of `PressureAutomaton`.

### Beam/propagation

Beam-facing propagation is the next conceptual layer.  It should consume
`SourcePressureFailureResolution` and decide how local states are transported
along a Beam/time/orbit direction.

That layer should not be inserted into `PressureDecay`, `PressureFrontier`, or
`PressureAccounting`, because those files are lower-level producers and
accountants.  It should also not be inserted into
`PressureDiagnosticDecomposition`, because that file should remain the local
branch split, not a propagation controller.

## Recommendation

Create a new upper module above `PressureAutomaton` when the first real
Beam-facing statement is ready.

Recommended name:

```text
DkMath.Collatz.PetalBridge.PressureBeam
```

Reason:

- `PressureBeam` names the intended mathematical subject directly.
- `PressurePropagation` is accurate but too broad; it could also describe
  lower margin-transition facts already owned by `PressureDecay`.
- `PressureAutomatonBeam` over-couples the future layer to the implementation
  detail that the previous layer is called `PressureAutomaton`.

Suggested future import direction:

```lean
import DkMath.Collatz.PetalBridge.PressureAutomaton
```

The first `PressureBeam` checkpoint should stay thin: define Beam-facing
predicates or wrappers only after a concrete downstream theorem needs them.

## Guardrails Confirmed

This checkpoint did not add:

- a propagation theorem;
- a convergence theorem;
- an aggregation theorem;
- an overlap repair theorem;
- arbitrary-list recursive decomposition;
- canonical first diagnosis;
- enumeration of all diagnostics;
- interval union accounting;
- coverage, maximality, uniqueness, or sorting theorems.

## Verification

Executed commands:

```text
lake build DkMath.Collatz.PetalBridge.PressureAutomaton
lake build DkMath.Collatz.PetalBridge
rg -n "\bsorry\b|admit" \
  DkMath/Collatz/PetalBridge/PressureAutomaton.lean \
  DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean \
  DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean \
  DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean \
  DkMath/Collatz/PetalBridge/PressureAccounting.lean \
  DkMath/Collatz/PetalBridge/PressureFrontier.lean \
  DkMath/Collatz/PetalBridge/PressureDecay.lean \
  DkMath/Collatz/PetalBridge/DriftBudget.lean
git diff --check
```

Result:

- `lake build DkMath.Collatz.PetalBridge.PressureAutomaton`: passed.
- `lake build DkMath.Collatz.PetalBridge`: passed.
- no-sorry check over the pressure files listed above: no matches.
- `git diff --check`: passed.

The builds still replay the known unrelated warning in
`DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean` about an existing
`sorry`.  This checkpoint did not touch that file.

## Next Checkpoint

If the next step is still Beam-facing, add:

```text
DkMath.Collatz.PetalBridge.PressureBeam
```

as a new upper module importing `PressureAutomaton`.  Keep it as a thin
interface until there is a precise theorem that transports a local
`SourcePressureFailureResolution` state along a concrete Beam index.
