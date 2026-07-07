# Report: petal-244

## Branch

Implemented the first mnemonic state-management layer for the source-pressure
proof automaton.

The goal was not to build an executable global automaton.  The goal was to
name the current proof states and make the local state transitions readable.

## Implemented File

New file:

```text
lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
```

Public import updated:

```text
lean/dk_math/DkMath/Collatz/PetalBridge.lean
```

## State Names

Added a small mnemonic enum:

```lean
inductive SourcePressureStateName where
  | sortedFailure
  | failureResolution
  | recoveredAdjacent
  | adjacentOverlap
  | beamSeed
  | centeredPulseBox
  | neighborCandidate
  | orientedNeighborDiagnostic
```

This is only a name table.  The real states are still `Prop` aliases over the
existing proof surfaces.

## Prop State Aliases

Added:

```lean
def SourcePressureSortedFailureState L : Prop
def SourcePressureFailureResolutionState L : Prop
def SourcePressureRecoveredAdjacentState L : Prop
def SourcePressureAdjacentOverlapState L : Prop
def SourcePressureBeamSeedState L : Prop
def SourcePressureCenteredPulseBoxState L W : Prop
def SourcePressureNeighborCandidateState L W W' : Prop
def SourcePressureOrientedNeighborDiagnosticState L W W' : Prop
def SourcePressureStateTransition (S T : Prop) : Prop := S → T
```

The intended mnemonic bits are recorded in source comments:

```text
F : sorted-before failure
R : failure resolution
S : Beam seed
P : centered pulse box
N : explicit neighbor candidate
D : oriented adjacent diagnosis
```

## Transitions

Added thin transition theorems:

```lean
theorem sourcePressureSortedFailureState_to_failureResolutionState
theorem sourcePressureFailureResolutionState_to_beamSeedState
theorem sourcePressureBeamSeedState_to_failureResolutionState
theorem sourcePressureSortedFailureState_to_beamSeedState
theorem sourcePressureRecoveredAdjacentState_to_failureResolutionState
theorem sourcePressureAdjacentOverlapState_to_failureResolutionState
theorem sourcePressureFailureResolutionState_cases
theorem sourcePressureCenteredPulseBoxState_signs_of_neighborCandidateState
theorem sourcePressureNeighborCandidateState_right_center_full_diagnostic
theorem sourcePressureOrientedNeighborDiagnosticState_of_forward
```

## Important Negative Design Point

The source code explicitly records that this false transition is not provided:

```text
CenteredPulseBoxState L W -> BeamSeedState L
```

A pulse box is downstream evidence.  It does not construct the upstream seed
state.  This is important for the future mnemonic table because it prevents a
common but invalid reversal of the proof flow.

## Current Automaton Reading

The current proof-flow can now be read as:

```text
SortedFailure
  -> FailureResolution
  -> BeamSeed
  -> CenteredPulseBox
  + NeighborCandidate
  -> endpoint signs / centered diagnostics
  + oriented adjacency
  -> OrientedNeighborDiagnostic
```

This is still local and witness/list-relative.

## Guardrails Preserved

No theorem added:

- global coverage;
- canonical witness selection;
- canonical adjacent pair selection;
- overlap repair;
- propagation;
- arbitrary transport;
- aggregation;
- monotone trend;
- Collatz convergence.

## Next Branch Prediction

The next useful branch is the actual mnemonic bit table.

Candidate light design:

```lean
structure SourcePressureStateBits where
  hasFailure : Bool
  hasResolution : Bool
  hasBeamSeed : Bool
  hasPulseBox : Bool
  hasNeighbor : Bool
  hasOrientedDiagnostic : Bool
```

But this should remain a human-readable naming table unless a caller needs
Boolean computation.  The proof-carrying states are currently more useful than
raw `Bool` states.

An immediate theorem branch, if needed, is a small exclusion/absence layer for
known false transitions:

```text
PulseBox alone does not produce BeamSeed
NeighborCandidate alone does not produce orientation
NeighborCandidate alone does not produce oriented diagnosis
```

Those are better kept as source comments until a concrete caller needs them as
formal negation theorems.

## Verification

Commands run from:

```text
lean/dk_math
```

Passed:

```text
lake build DkMath.Collatz.PetalBridge.PressureState
lake build DkMath.Collatz.PetalBridge
```

No-sorry check:

```text
rg -n "sorry|admit" \
  PressureState.lean \
  PressureAutomaton.lean \
  PressureBeam/Pulse.lean
```

Result: no matches.

Whitespace check:

```text
git diff --check
```

Result: passed.
