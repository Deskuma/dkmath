# report-petal-198

## Checkpoint

Checkpoint 198 revised was audit-only.

No Lean theorem was added.  The purpose of this checkpoint was to confirm the
import direction and API boundary around the arbitrary-list pressure diagnostic
surface.

## Import Chain

The current pressure stack flows upward as follows:

```text
PressureFrontier
  <- PressureAccounting
    <- PressureLocalWitnessObstruction
      <- PressureAdjacentDiagnosis
        <- PressureDiagnosticDecomposition
```

The concrete imports are:

```lean
-- PressureFrontier.lean
import DkMath.Collatz.PetalBridge.PressureDecay

-- PressureAccounting.lean
import DkMath.Collatz.PetalBridge.PressureFrontier

-- PressureLocalWitnessObstruction.lean
import DkMath.Collatz.PetalBridge.PressureAccounting

-- PressureAdjacentDiagnosis.lean
import DkMath.Collatz.PetalBridge.PressureLocalWitnessObstruction

-- PressureDiagnosticDecomposition.lean
import DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis
```

This means lower modules such as `PressureFrontier` and `PressureAccounting`
must not consume theorem names from `PressureDiagnosticDecomposition` unless a
separate refactor-only checkpoint deliberately changes the module structure.

## Diagnostic Surface Location

The branch split theorem lives only in:

```text
DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
```

The exact theorem is:

```lean
sourcePressureLocalIslandWitnessList_failure_exists_pairDiagnostic_or_adjacentOverlap
```

The no-overlap consumer theorem also lives only in:

```text
DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
```

The exact theorem is:

```lean
sourcePressureLocalIslandWitnessList_failure_exists_pairDiagnostic_of_noAdjacentOverlap
```

Search result:

```text
DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean:806
DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean:836
```

No lower pressure module defines or imports these names.

## Boundary Interpretation

`PressureFrontier` is a producer layer.  It talks about pressure depths, local
islands, interval pulses, and pulse addresses.  It is upstream of explicit
local-island witness lists and does not know about adjacent diagnostics.

`PressureAccounting` is a carrier layer.  It introduces explicit witness lists,
sorted-before predicates, sorted-before failure predicates, and finite
accounting wrappers.  It should not import diagnostic decomposition, because
that would pull a downstream consumer layer back into a foundational carrier
module.

`PressureDiagnosticDecomposition` is the correct location for the named
pair-diagnostic arbitrary-list API, because it already imports the adjacent
diagnosis layer and sits above the carrier modules.

## Two-Stage API Confirmed

The current two-stage API remains:

```text
sorted-before failure
  -> pairDiagnostic-or-adjacentOverlap

sorted-before failure + no-adjacent-overlap
  -> exists pairDiagnostic
```

In theorem names:

```lean
sourcePressureLocalIslandWitnessList_failure_exists_pairDiagnostic_or_adjacentOverlap
sourcePressureLocalIslandWitnessList_failure_exists_pairDiagnostic_of_noAdjacentOverlap
```

The first theorem keeps overlap visible as a branch.  The second theorem
extracts a recovered adjacent pair only after the caller supplies no-overlap.

## Guardrails

No theorem or import was added for:

- downstream imports from `PressureFrontier` or `PressureAccounting` to
  `PressureDiagnosticDecomposition`,
- arbitrary-list recursive decomposition,
- canonical first diagnosis,
- enumeration of all diagnostics,
- aggregation over multiple recovered diagnostics,
- list-wide interval union accounting,
- coverage,
- maximality,
- uniqueness,
- sorting theorem,
- overlap repair,
- disjointness between multiple recovered families,
- Collatz convergence.

## Line-Count Status

```text
  1130 DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
  1356 DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
  1391 DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean
  1896 DkMath/Collatz/PetalBridge/PressureAccounting.lean
  1517 DkMath/Collatz/PetalBridge/PressureFrontier.lean
  7290 total
```

All five files remain under the 2,000-line split threshold.

## Verification

Commands run from `lean/dk_math`:

```text
lake build DkMath.Collatz.PetalBridge.PressureDiagnosticDecomposition
lake build DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis
lake build DkMath.Collatz.PetalBridge.PressureLocalWitnessObstruction
lake build DkMath.Collatz.PetalBridge.PressureAccounting
lake build DkMath.Collatz.PetalBridge.PressureFrontier
lake build DkMath.Collatz.PetalBridge
```

Result: all builds passed.

No-sorry check over the five requested pressure files:

```text
rg -n "\bsorry\b|admit" \
  DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean \
  DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean \
  DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean \
  DkMath/Collatz/PetalBridge/PressureAccounting.lean \
  DkMath/Collatz/PetalBridge/PressureFrontier.lean
```

Result: no matches.

`git diff --check` passed.

Known unrelated warning observed in local build logs:

```text
DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:152:6:
declaration uses `sorry`
```

This checkpoint did not touch that file.
