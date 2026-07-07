# report-petal-228

## Checkpoint

`petal-228`

## Goal

Refine the cp227 existential diagnostic by checking whether
`SourcePressureFailureResolution L` can preserve branch-specific witness
identity.

cp227 already had:

```text
SourcePressureFailureResolution L
  -> exists W in L
       such that W's singleton pulse has the full local diagnostic
```

cp228 asks whether the branch source can be kept visible.

## Branch Taken

Branch A was taken.

The recovered branch exposes:

```lean
∃ A B,
  SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
    SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic A B
```

The useful identity carrier is the adjacent-pair address:

```lean
SourcePressureLocalIslandWitnessAdjacentPairInList L A B
```

It preserves the names `A` and `B`.  From that address, the Pulse layer can
recover both memberships:

```lean
A ∈ L
B ∈ L
```

and then apply:

```lean
sourcePressureBeamPulse_witness_singleton_full_diagnostic
```

## Added Theorems

Added in `DkMath.Collatz.PetalBridge.PressureBeam.Pulse`:

```lean
theorem sourcePressureBeamPulse_witness_singleton_full_diagnostic_of_adjacentPairInList_left
```

This preserves the left recovered-pair witness identity:

```text
AdjacentPairInList L A B
  -> full local singleton diagnostic for A
```

Also added:

```lean
theorem sourcePressureBeamPulse_witness_singleton_full_diagnostic_of_adjacentPairInList_right
```

This preserves the right recovered-pair witness identity:

```text
AdjacentPairInList L A B
  -> full local singleton diagnostic for B
```

Both theorems are local address consumers.  They do not use the recovered
budget diagnostic itself; they use the adjacent-pair address carried by that
branch.  This keeps the proof surface small and avoids duplicating recovered
diagnostic data.

## Branches Inspected But Not Taken

Branch B:

- The overlap obstruction branch is recursive over neighboring pairs.
- It can produce existence through the existing seed/failure-resolution route,
  but preserving a specific overlap-side witness identity would require a
  branch-specific overlap-address projection.
- That projection was not added here because cp228 already used its two-theorem
  budget on the clearer recovered-pair left/right identities.

Branch C:

- Both branches can eventually expose witnesses existentially.
- Only the recovered adjacent-pair branch currently exposes clean named
  identities `A` and `B` at the theorem surface.

Branch D:

- Not taken for the recovered branch: identity is not hidden there.
- Partially applies to overlap: the current overlap predicate exposes a
  recursive obstruction, but not a named public `W ∈ L` projection in the Beam
  Pulse layer.

Branch E:

- No obstruction or contradiction was found.  Both `A` and `B` can feed the
  singleton diagnostic once membership is extracted.

## Classification

True Beam:

- Recovered adjacent-pair left witness identity is preserved.
- Recovered adjacent-pair right witness identity is preserved.
- Both sides feed the same full local singleton diagnostic without canonical
  selection.

Boundary:

- These theorems are address-local.  They only consume one supplied
  `AdjacentPairInList L A B`.

False Beam:

- None added.  No negative theorem was needed.

Gap:

- Overlap obstruction still lacks a compact Beam-facing branch-specific
  membership projection.
- A future theorem could target:

```text
SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L
  -> exists W in L
       such that W is one side of the obstructing adjacent pair
       and W has the full singleton diagnostic
```

This should stay existential unless a caller needs left/right overlap identity.

## Guardrails

No theorem claims:

- list-wide coverage;
- witness-family aggregation;
- arbitrary witness selection;
- canonical target selection;
- arbitrary target transport;
- overlap repair;
- propagation;
- Collatz convergence.

## Dependency Direction

No dependency inversion was introduced.

The new theorems were placed in:

```text
DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean
```

No lower diagnostic or automaton module imports `PressureBeam`.

## Verification

Commands run from `lean/dk_math`:

```text
lake build DkMath.Collatz.PetalBridge.PressureBeam.Pulse
lake build DkMath.Collatz.PetalBridge.PressureBeam
lake build DkMath.Collatz.PetalBridge
```

All builds completed successfully.

Additional checks from repository root:

```text
rg -n "sorry|admit" lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam \
  lean/dk_math/DkMath/Collatz/PetalBridge/PressureAutomaton.lean \
  lean/dk_math/DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean \
  lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean \
  lean/dk_math/DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean
```

No matches were found.

Known unrelated warning observed during builds:

```text
DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:152:6:
declaration uses `sorry`
```

## Next Branch To Attack

The next natural branch is the overlap obstruction witness projection:

```text
overlap obstruction
  -> exists adjacent obstructing pair
  -> choose one named side locally
  -> full singleton diagnostic for that side
```

The safest version is existential.  A left/right-specific overlap API should
wait until a caller needs that exact identity.
