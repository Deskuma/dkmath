# report-petal-233

## Checkpoint

`petal-233`

## Goal

Move upward from the completed Pulse diagnostic API and inspect whether a
concrete higher-level caller now needs those diagnostics.

## Branch Taken

Branch D was taken: current API is sufficient and no concrete higher-level
caller exists.

No Lean theorem was added in this checkpoint.

## Modules Inspected

Inspected caller and boundary modules:

```text
DkMath/Collatz/PetalBridge/PressureAutomaton.lean
DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean
DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean
DkMath/Collatz/PetalBridge/PressureBeam/Core.lean
```

Also searched the wider `DkMath.Collatz.PetalBridge` tree for current uses of:

```text
SourcePressureFailureResolution
SourcePressureBeamSeed
exists_sourcePressureBeamPulse...
AdjacentPairInList
AdjacentOverlapObstruction
PairOverlapObstruction
```

## Finding

No caller currently has:

```text
SourcePressureFailureResolution L
```

and then struggles to obtain an anonymous Pulse diagnostic.  The existing
theorem is already available:

```lean
exists_sourcePressureBeamPulse_witness_singleton_full_diagnostic_of_failureResolution
```

No caller currently needs branch-kind-preserving Beam diagnostics either.
`SourcePressureFailureResolution` itself is the branch-kind classifier, and the
recommended use remains:

```text
SourcePressureFailureResolution:
  inspect recovered vs overlap branch

PressureBeam.Pulse:
  extract singleton Beam diagnostics after a branch or anonymous witness is
  chosen
```

## Current Use Paths

Anonymous path:

```text
SourcePressureFailureResolution L
  -> ∃ W, W ∈ L ∧ full singleton diagnostic for W
```

Recovered pair path:

```text
AdjacentPairInList L A B
  -> full diagnostic for A
  -> full diagnostic for B
```

Overlap precise path:

```text
overlap obstruction
  -> ∃ A B,
       AdjacentPairInList L A B
       ∧ PairOverlapObstruction A B
       ∧ full diagnostic for A
```

Overlap anonymous path:

```text
overlap obstruction
  -> ∃ W, W ∈ L ∧ full singleton diagnostic for W
```

Seed/depth path in `PressureBeam.Core`:

```text
SourcePressureBeamSeed L
  -> ∃ j, SourcePressureBeamSeedContainsDepth L j
  -> ∃ j, SourcePressureBeamDepthTarget n k r j
```

This is a depth/target path, not a Pulse diagnostic path.  It should not force
a new theorem unless a caller needs to combine target extraction and full
singleton diagnostic in one statement.

## Branches Inspected But Not Taken

Branch A:

- Not taken.
- The anonymous failure-resolution diagnostic theorem already exists.
- No higher caller was found that would become simpler from another wrapper.

Branch B:

- Not taken.
- Branch-kind preservation remains available at `SourcePressureFailureResolution`.
- No caller currently needs a larger Beam theorem that mirrors both branches.

Branch C:

- Not taken.
- No concrete caller needs overlap right endpoint or both-endpoint diagnostics.

Branch E:

- Not taken.
- No missing relation was found in current callers.

## Classification

True Beam:

- No new theorem added.
- Existing Pulse diagnostic surfaces are sufficient for visible callers.

Boundary:

- `PressureAutomaton` owns branch-kind classification.
- `PressureBeam.Core` owns seed/depth target extraction.
- `PressureBeam.Pulse` owns singleton Beam diagnostics.

False Beam:

- None added.

Gap:

- If a future theorem needs a single bundled theorem combining seed/depth
  target and full Pulse diagnostic, that will be a new caller-driven bridge.
- If a future theorem needs branch-kind-preserving Beam diagnostics, it should
  be designed from that caller, not added generically now.

## Dependency Direction

No dependency inversion was introduced.

No Lean code changed in this checkpoint.  Lower diagnostic modules still do not
import Beam.

## Guardrails

No theorem claims:

- list-wide coverage;
- witness-family aggregation;
- arbitrary witness selection;
- canonical target selection;
- arbitrary target transport;
- overlap repair;
- disjointness;
- propagation;
- Collatz convergence.

## Verification

No Lean code changed for cp233.

Workspace hygiene check:

```text
git diff --check
```

completed successfully.

## Next Branch To Attack

The Pulse diagnostic API can remain closed for now.

The next useful work should move to a concrete upstream or downstream caller,
most likely one of:

```text
1. target/depth transport from SourcePressureBeamSeed;
2. a caller that combines Beam depth target and Pulse diagnostic;
3. a branch-kind-preserving theorem only after a caller demands it.
```

Until then, avoid adding right-endpoint, both-endpoint, or branch-kind Beam
wrappers for symmetry alone.
