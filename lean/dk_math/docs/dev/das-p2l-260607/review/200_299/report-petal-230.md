# report-petal-230

## Checkpoint

`petal-230`

## Goal

Close the overlap-address Gap left by cp229:

```text
adjacent overlap obstruction
  -> addressed adjacent obstructing pair
```

Then, if the lower projection is clean, add one thin Beam-facing wrapper.

## Branch Taken

Branch A was taken, with the recursive tail handling from Branch B.

The obstruction predicate:

```lean
SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L
```

is recursive over neighboring pairs.  The head case exposes the pair-local
predicate:

```lean
SourcePressureLocalIslandWitnessPairOverlapObstruction W1 W2
```

and the tail case preserves the same addressed pair through:

```lean
SourcePressureLocalIslandWitnessAdjacentPairInList.tail
```

No new cons-lift helper was needed because cp229 already found the address
API in `PressureAdjacentDiagnosis.lean`.

## Added Lower Projection

Added in `DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis`:

```lean
theorem exists_adjacentPairInList_pairOverlapObstruction_of_overlapObstruction
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (hobs :
      SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L) :
    ∃ A B,
      SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
        SourcePressureLocalIslandWitnessPairOverlapObstruction A B
```

This belongs below Beam because it only relates:

- explicit witness-list overlap obstruction;
- adjacent-pair address;
- pair-local overlap obstruction.

It imports no Beam vocabulary and does not mention mass balance.

## Added Beam Wrapper

Added in `DkMath.Collatz.PetalBridge.PressureBeam.Pulse`:

```lean
theorem
    exists_sourcePressureBeamPulse_leftWitness_full_diagnostic_of_adjacentOverlapObstruction
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (hobs :
      SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L) :
    ∃ A B,
      SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
        SourcePressureLocalIslandWitnessPairOverlapObstruction A B ∧
          ... full singleton Beam diagnostic for A ...
```

This wrapper consumes:

```lean
exists_adjacentPairInList_pairOverlapObstruction_of_overlapObstruction
```

and then applies:

```lean
sourcePressureBeamPulse_witness_singleton_full_diagnostic_of_adjacentPairInList_left
```

The result keeps `A`, `B`, the address predicate, and the overlap obstruction
visible.  It does not collapse the branch into an anonymous witness unless a
caller chooses to do so later.

## Branches Inspected But Not Taken

Branch B:

- Tail recursion was needed, but the required address lift already existed as
  `SourcePressureLocalIslandWitnessAdjacentPairInList.tail`.
- No new helper was added.

Branch C:

- Not taken.  The overlap predicate did preserve stable pair identity through
  the recursive definition.

Branch D:

- Not taken.  cp227's generic `failureResolution -> exists full diagnostic`
  remains valid, but cp230 now provides overlap-specific identity.

Branch E:

- Not taken.  A compact pair-level predicate already exists:
  `SourcePressureLocalIslandWitnessPairOverlapObstruction`.

Branch F:

- No contradiction was found.

## Classification

True Beam:

- Adjacent overlap obstruction now exposes an addressed pair with pair-local
  overlap obstruction.
- Beam Pulse can now attach the full singleton diagnostic to the left witness
  of that addressed obstructing pair.

Boundary:

- The theorem is still adjacent-pair local.
- The Beam wrapper chooses the left endpoint only as a named branch-specific
  surface, not as a canonical global target.

False Beam:

- None added.

Gap:

- There is no right-endpoint overlap Beam wrapper yet.
- There is no generic anonymous projection:

```text
overlap obstruction -> exists W in L with full diagnostic
```

This can now be derived, but adding it should wait until a caller needs the
weaker anonymous surface.

## Dependency Direction

No dependency inversion was introduced.

The lower projection is in:

```text
DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
```

The Beam-facing wrapper is in:

```text
DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean
```

No lower module imports Beam.

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

The next useful branch is optional and caller-driven.

If a caller wants the right endpoint of the overlap pair:

```text
overlap obstruction
  -> exists A B, addressed pair and full diagnostic for B
```

then add the symmetric Beam wrapper using:

```lean
sourcePressureBeamPulse_witness_singleton_full_diagnostic_of_adjacentPairInList_right
```

If a caller does not care about pair identity:

```text
overlap obstruction
  -> exists W, W in L and full diagnostic for W
```

can be added as a weaker public surface.  This should wait until it removes
real caller noise, because the current cp230 theorem preserves more useful
branch identity.
