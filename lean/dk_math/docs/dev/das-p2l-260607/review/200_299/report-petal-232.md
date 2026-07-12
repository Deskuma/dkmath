# report-petal-232

## Checkpoint

`petal-232`

## Goal

Audit the current Beam Pulse diagnostic surfaces and decide whether to add a
higher-level failure-resolution classifier theorem.

## Branch Taken

Branch B was taken: the current API is sufficient.

No Lean theorem was added in this checkpoint.

## Reason

`SourcePressureFailureResolution L` is already the branch-kind classifier:

```lean
def SourcePressureFailureResolution
    (L : List (SourcePressureLocalIslandWitness n k r)) : Prop :=
  (∃ A B,
    SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
      SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic
        A B) ∨
    SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L
```

The Beam Pulse layer already has:

```lean
SourcePressureFailureResolution L
  -> ∃ W, W ∈ L ∧ full singleton diagnostic for W
```

Adding a new branch-kind-preserving Beam theorem is possible, but the statement
would be large and no concrete caller currently needs it.  The better public
surface for now is:

```text
use SourcePressureFailureResolution for branch-kind inspection;
use Pulse theorems only after choosing a branch or when an anonymous diagnostic
is enough.
```

## Current Diagnostic API Map

Explicit witness:

```lean
sourcePressureBeamPulse_witness_singleton_full_diagnostic
```

Use when the caller already has:

```text
W ∈ L
```

Beam seed:

```lean
exists_sourcePressureBeamPulse_witness_singleton_full_diagnostic_of_seed
```

Use when the caller has:

```text
SourcePressureBeamSeed L
```

Failure resolution:

```lean
exists_sourcePressureBeamPulse_witness_singleton_full_diagnostic_of_failureResolution
```

Use when the caller has:

```text
SourcePressureFailureResolution L
```

and does not care which branch produced the witness.

Recovered adjacent pair:

```lean
sourcePressureBeamPulse_witness_singleton_full_diagnostic_of_adjacentPairInList_left
sourcePressureBeamPulse_witness_singleton_full_diagnostic_of_adjacentPairInList_right
```

Use when the caller already has an addressed adjacent pair:

```text
SourcePressureLocalIslandWitnessAdjacentPairInList L A B
```

Overlap, pair-preserving:

```lean
exists_sourcePressureBeamPulse_leftWitness_full_diagnostic_of_adjacentOverlapObstruction
```

Use when the caller needs to keep:

```text
A, B,
AdjacentPairInList L A B,
PairOverlapObstruction A B
```

and attach the full singleton diagnostic to the left endpoint `A`.

Overlap, anonymous:

```lean
exists_sourcePressureBeamPulse_witness_full_diagnostic_of_adjacentOverlapObstruction
```

Use when the caller only needs:

```text
∃ W, W ∈ L ∧ full singleton diagnostic for W
```

from an adjacent-overlap obstruction.

## Branches Inspected But Not Taken

Branch A:

- Not taken.
- A branch-kind-preserving Beam classifier can be constructed by splitting
  `SourcePressureFailureResolution`.
- It would duplicate the existing classifier plus current Pulse surfaces, and
  no caller currently needs the larger theorem.

Branch C:

- Not taken.
- No concrete caller needs the right endpoint of an overlap pair.

Branch D:

- Not taken.
- No concrete caller needs both endpoints of an overlap pair.

Branch E:

- Mild duplication exists:

```text
SourcePressureBeamSeed L
```

is currently a Beam-facing name for:

```text
SourcePressureFailureResolution L
```

The duplicated seed/failure-resolution Pulse theorems are intentional for API
readability and should not be removed yet.

## Classification

True Beam:

- No new theorem added.
- The existing Pulse API is coherent and covers the currently visible caller
  shapes.

Boundary:

- Branch-kind inspection should happen at `SourcePressureFailureResolution`.
- Pulse should stay as the local diagnostic extraction layer.

False Beam:

- None added.

Gap:

- A branch-kind-preserving Beam classifier remains possible if a caller needs
  it.
- Right-endpoint and both-endpoint overlap wrappers remain possible but should
  remain caller-driven.

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

No Lean code changed for cp232.

Workspace hygiene check:

```text
git diff --check
```

completed successfully.

The prior cp231 build gate already verified the current Pulse surface:

```text
lake build DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis
lake build DkMath.Collatz.PetalBridge.PressureBeam.Pulse
lake build DkMath.Collatz.PetalBridge.PressureBeam
lake build DkMath.Collatz.PetalBridge
```

## Next Branch To Attack

Move upward only when a concrete caller appears.

Natural next candidates:

```text
1. branch-kind-preserving Beam classifier
2. right-endpoint overlap diagnostic
3. both-endpoint overlap diagnostic
```

Until then, keep the current split:

```text
Automaton layer:
  choose recovered vs overlap

Pulse layer:
  extract local singleton Beam diagnostics
```
