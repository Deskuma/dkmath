# report-petal-231

## Checkpoint

`petal-231`

## Goal

Decide whether to add the next overlap-diagnostic surface after cp230.

The key rule was: do not add symmetric or anonymous wrappers mechanically.
Inspect actual caller shape first.

## Caller Inspection

The right-endpoint theorem:

```lean
sourcePressureBeamPulse_witness_singleton_full_diagnostic_of_adjacentPairInList_right
```

exists, but no current higher-level caller was found that specifically needs
the right endpoint `B` of an overlap pair.

However, `PressureBeam/Core.lean` already has an anonymous overlap-to-depth
surface:

```lean
exists_sourcePressureBeamSeedContainsDepth_of_adjacentOverlapObstruction
```

That theorem intentionally forgets the exact pair identity and returns an
existential listed witness depth.  The matching Pulse-level caller surface is:

```text
adjacent overlap obstruction
  -> exists W in L with full singleton Beam diagnostic
```

So Branch B was taken.

## Added Theorem

Added in `DkMath.Collatz.PetalBridge.PressureBeam.Pulse`:

```lean
theorem exists_sourcePressureBeamPulse_witness_full_diagnostic_of_adjacentOverlapObstruction
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (hobs :
      SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L) :
    ∃ W : SourcePressureLocalIslandWitness n k r,
      W ∈ L ∧
        ... full singleton Beam diagnostic for W ...
```

It consumes the stronger cp230 theorem:

```lean
exists_sourcePressureBeamPulse_leftWitness_full_diagnostic_of_adjacentOverlapObstruction
```

and projects `A ∈ L` via:

```lean
sourcePressureLocalIslandWitnessAdjacentPairInList_left_mem
```

The theorem does not re-run the overlap recursion.  It only weakens the
pair-preserving surface when a caller does not need `A`, `B`, or the explicit
pair-overlap obstruction.

## Branches Inspected But Not Taken

Branch A:

- Not taken.
- No caller currently required the right endpoint `B` specifically.
- The existing cp228 right endpoint theorem remains available if that need
  appears later.

Branch C:

- Not taken.
- No caller needed both endpoint diagnostics simultaneously.

Branch D:

- Not taken.
- cp230 was strong enough, but the anonymous overlap-to-depth style already
  exists in `PressureBeam/Core.lean`; the new Pulse theorem is the matching
  full-diagnostic surface.

Branch E:

- Not taken.
- The caller bridge is available: overlap obstruction is already a direct
  hypothesis in the new theorem.

## Classification

True Beam:

- Adjacent overlap obstruction now has an anonymous full singleton diagnostic
  surface.

Boundary:

- The theorem deliberately forgets pair identity.
- It should be used only when preserving pair identity would be caller noise.
- The witness is not canonical; it is obtained by weakening the cp230 left
  endpoint theorem.

False Beam:

- None added.

Gap:

- Right endpoint overlap wrapper remains unadded.
- Both-endpoint overlap diagnostic remains unadded.
- These should be added only when actual callers need them.

## Dependency Direction

No dependency inversion was introduced.

Only `PressureBeam/Pulse.lean` changed.  Lower diagnostic modules still do not
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

Commands run from `lean/dk_math`:

```text
lake build DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis
lake build DkMath.Collatz.PetalBridge.PressureBeam.Pulse
lake build DkMath.Collatz.PetalBridge.PressureBeam
lake build DkMath.Collatz.PetalBridge
```

All builds completed successfully.

No-sorry/admit scan over the inspected pressure files returned no matches:

```text
rg -n "sorry|admit" lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam lean/dk_math/DkMath/Collatz/PetalBridge/PressureAutomaton.lean lean/dk_math/DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean lean/dk_math/DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean
```

`git diff --check` completed successfully.

Known unrelated warning observed during builds:

```text
DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:152:6:
declaration uses `sorry`
```

## Next Branch To Attack

Next useful branch should remain caller-driven.

If downstream work needs the right side of the obstructing pair, add:

```text
overlap obstruction
  -> exists A B, addressed pair, pair-overlap obstruction,
     and full diagnostic for B
```

If downstream work needs both endpoints, add one paired theorem rather than
two independent wrappers.

Otherwise, keep cp230 plus cp231 as the public overlap Beam surface:

```text
pair-preserving surface for precise callers
anonymous witness surface for callers that only need one pulse diagnostic
```
