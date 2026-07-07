# report-petal-229

## Checkpoint

`petal-229`

## Goal

Refine the cp228 branch-specific diagnostic work by investigating:

- reusable adjacent-pair membership projections;
- the overlap obstruction branch.

## Branch Taken

Branch 0 was taken.

The definition:

```lean
SourcePressureLocalIslandWitnessAdjacentPairInList L A B
```

is a pure list-address predicate.  It already preserves the names `A` and `B`,
but cp228 had to re-prove membership extraction locally in `PressureBeam/Pulse`.

The reusable projection layer belongs in the lower module that defines the
address predicate, because it uses no Beam vocabulary.

## Added Theorems

Added in `DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis`:

```lean
theorem sourcePressureLocalIslandWitnessAdjacentPairInList_left_mem
```

Meaning:

```text
AdjacentPairInList L A B -> A in L
```

Also added:

```lean
theorem sourcePressureLocalIslandWitnessAdjacentPairInList_right_mem
```

Meaning:

```text
AdjacentPairInList L A B -> B in L
```

These are pure address projections.  They do not inspect pair diagnostics,
choose a canonical pair, enumerate pairs, or claim list coverage.

## Refactor

The cp228 Pulse theorems were mechanically shortened to use these helpers:

```lean
sourcePressureBeamPulse_witness_singleton_full_diagnostic_of_adjacentPairInList_left
sourcePressureBeamPulse_witness_singleton_full_diagnostic_of_adjacentPairInList_right
```

Their public theorem statements were not changed.

## Branches Inspected But Not Taken

Branch A:

- `SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L` is a
  recursive neighboring-pair obstruction.
- It can expose a head obstruction or recurse into the tail, but there is not
  yet a compact public projection that returns an addressed pair
  `AdjacentPairInList L A B`.
- Because the two-theorem budget was already used for reusable membership
  projections, no overlap theorem was added in this checkpoint.

Branch B:

- Left/right overlap identity was not added.  The overlap branch needs a public
  pair-address extraction first.

Branch C:

- This is the current state for overlap: recursive existence is visible in the
  definition, but branch-specific identity is not packaged as a reusable API.

Branch D:

- cp227 still covers the generic existential surface through
  failure-resolution/seed.
- cp229 does not duplicate that theorem.

Branch E:

- No contradiction was found.  The missing piece is API shape, not a false
  mathematical claim.

## Classification

True Beam:

- Adjacent-pair left membership is now a reusable theorem.
- Adjacent-pair right membership is now a reusable theorem.
- cp228 recovered-pair diagnostics now consume these projections.

Boundary:

- These helpers are list-address local.  They only say the addressed pair's
  two endpoints are members of the explicit list.

False Beam:

- None added.

Gap:

- Overlap obstruction needs a compact address projection such as:

```text
SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L
  -> exists A B,
       AdjacentPairInList L A B
       and PairOverlapObstruction A B
```

Once that exists, the left side can immediately feed:

```lean
sourcePressureBeamPulse_witness_singleton_full_diagnostic_of_adjacentPairInList_left
```

to obtain an existential overlap-side full diagnostic.

## Dependency Direction

No dependency inversion was introduced.

The helper projections were placed in:

```text
DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
```

They depend only on the adjacent-pair address predicate.  Beam-facing theorem
consumption remains in:

```text
DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean
```

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
rg -n "sorry|admit" lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam lean/dk_math/DkMath/Collatz/PetalBridge/PressureAutomaton.lean lean/dk_math/DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean lean/dk_math/DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean lean/dk_math/DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean
git diff --check
```

All builds completed successfully.

The no-sorry/admit scan returned no matches in the inspected pressure files.
`git diff --check` completed successfully.

Known unrelated warning observed during builds:

```text
DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:152:6:
declaration uses `sorry`
```

## Next Branch To Attack

Next checkpoint should target the overlap address projection:

```text
overlap obstruction
  -> exists adjacent obstructing pair with AdjacentPairInList
```

That theorem belongs in the lower obstruction/diagnosis layer and should not
mention Beam.  After it exists, the Beam-facing overlap diagnostic should be a
thin existential wrapper.
