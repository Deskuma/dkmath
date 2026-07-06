# report-petal-199

## Checkpoint

Checkpoint 199 added a thin upper-level pressure automaton surface.

The new file is:

```text
DkMath/Collatz/PetalBridge/PressureAutomaton.lean
```

This is not new mathematical strength.  It names the already proved
failure-resolution surface from `PressureDiagnosticDecomposition` in an
automaton-style vocabulary.

## Import Chain

The pressure stack now has the following upper-level shape:

```text
PressureFrontier
  <- PressureAccounting
    <- PressureLocalWitnessObstruction
      <- PressureAdjacentDiagnosis
        <- PressureDiagnosticDecomposition
          <- PressureAutomaton
```

`PressureAutomaton.lean` imports only:

```lean
import DkMath.Collatz.PetalBridge.PressureDiagnosticDecomposition
```

The public aggregator now imports it immediately after
`PressureDiagnosticDecomposition`:

```lean
import DkMath.Collatz.PetalBridge.PressureDiagnosticDecomposition
import DkMath.Collatz.PetalBridge.PressureAutomaton
```

Lower pressure modules were not modified.

## Added API

The new automaton-state predicate is:

```lean
def SourcePressureFailureResolution
    {n : OddNat} {k r : ℕ}
    (L : List (SourcePressureLocalIslandWitness n k r)) : Prop :=
  (∃ A B,
    SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
      SourcePressureLocalIslandWitnessPairHasRecoveredAccountedFamilyDiagnostic
        A B) ∨
    SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L
```

It has exactly two branches:

1. an adjacent pair has the named recovered diagnostic;
2. an adjacent overlap obstruction remains visible.

The entry theorem is:

```lean
theorem sourcePressureFailureResolution_of_sortedBeforeFailure
```

It is a wrapper around:

```lean
sourcePressureLocalIslandWitnessList_failure_exists_pairDiagnostic_or_adjacentOverlap
```

The no-overlap extraction theorem is:

```lean
theorem sourcePressureFailureResolution_recovered_of_noAdjacentOverlap
```

It is a wrapper around:

```lean
sourcePressureLocalIslandWitnessList_failure_exists_pairDiagnostic_of_noAdjacentOverlap
```

## Boundary

This module is deliberately above the diagnostic decomposition layer.  It is a
readable command table for the local pressure machine:

```text
sorted-before failure
  -> failure resolution

failure resolution + no-adjacent-overlap
  -> recovered adjacent pair diagnostic
```

Overlap is not repaired.  It remains an obstruction branch unless the caller
supplies no-overlap.

## Guardrails

No theorem was added for:

- arbitrary-list recursive decomposition,
- canonical first diagnosis,
- enumeration of all diagnostics,
- aggregation over multiple recovered diagnostics,
- interval union accounting,
- overlap repair,
- coverage,
- maximality,
- uniqueness,
- sorting theorem,
- disjointness between multiple recovered families,
- Collatz convergence.

## Line-Count Status

```text
    89 DkMath/Collatz/PetalBridge/PressureAutomaton.lean
  1130 DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
  1356 DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
  1391 DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean
  1896 DkMath/Collatz/PetalBridge/PressureAccounting.lean
  1517 DkMath/Collatz/PetalBridge/PressureFrontier.lean
  7379 total
```

All pressure files remain under the 2,000-line split threshold.

## Verification

Commands run from `lean/dk_math`:

```text
lake build DkMath.Collatz.PetalBridge.PressureAutomaton
lake build DkMath.Collatz.PetalBridge
```

Result: both builds passed.

No-sorry check:

```text
rg -n "\bsorry\b|admit" \
  DkMath/Collatz/PetalBridge/PressureAutomaton.lean \
  DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean \
  DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean \
  DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean \
  DkMath/Collatz/PetalBridge/PressureAccounting.lean \
  DkMath/Collatz/PetalBridge/PressureFrontier.lean
```

Result: no matches.

Known unrelated warning observed in local build logs:

```text
DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:152:6:
declaration uses `sorry`
```

This checkpoint did not touch that file.

## Next Inference

The local automaton surface is now named.  The next natural work should stay
above this layer: either a Beam-facing bridge that consumes
`SourcePressureFailureResolution`, or an audit checkpoint deciding which
future module should own propagation over time.  That should not be pushed
back into `PressureFrontier` or `PressureAccounting`.
