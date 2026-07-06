# report-petal-198

## Checkpoint

Checkpoint 198 was audit-only.

No Lean theorem was added.  The downstream shape of the arbitrary-list
diagnostic API is already in the right module layer, and no clear consumer gap
was found in `PressureFrontier` or `PressureAccounting`.

## Files inspected

Primary file:

```text
DkMath/Collatz/PetalBridge/PressureFrontier.lean
```

Supporting files inspected:

```text
DkMath/Collatz/PetalBridge/PressureAccounting.lean
DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
```

## Theorems and definitions inspected

In `PressureFrontier.lean`, the relevant inspected surface was the frontier and
local-island producer layer:

```lean
SourcePressureLocalIsland
sourcePressureLocalIsland_iff_margin
sourcePressureIntervalPulse_of_localIsland
sourcePressureIntervalPulseAddress_of_localIsland
```

This file imports only:

```lean
import DkMath.Collatz.PetalBridge.PressureDecay
```

So it is intentionally upstream of accounting witnesses and diagnostic
decomposition.  Making `PressureFrontier` consume pair diagnostics would invert
the current dependency direction.

In `PressureAccounting.lean`, the relevant inspected surface was the explicit
witness-list and sorted-before carrier layer:

```lean
SourcePressureLocalIslandWitness
sourcePressureIntervalPulseAddress_of_localIslandWitness
sourcePressureIntervalPulseAddressFamily_of_localIslandWitnessList
SourcePressureLocalIslandWitnessListSortedBefore
SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
sourcePressureLocalIslandWitnessList_sorted_or_failure
```

This file imports:

```lean
import DkMath.Collatz.PetalBridge.PressureFrontier
```

It defines the explicit witness and sorted-before vocabulary, but it does not
import adjacent diagnosis or diagnostic decomposition.  Adding the requested
consumer here would pull a downstream diagnostic layer back into the carrier
layer.

In `PressureDiagnosticDecomposition.lean`, the already confirmed two-stage API
remains:

```lean
sourcePressureLocalIslandWitnessList_failure_exists_pairDiagnostic_or_adjacentOverlap
sourcePressureLocalIslandWitnessList_failure_exists_pairDiagnostic_of_noAdjacentOverlap
```

## Audit result

No downstream wrapper was added.

The current layering is:

```text
PressureFrontier
  -> pressure depths, local islands, interval pulses, pulse addresses

PressureAccounting
  -> explicit local-island witnesses and sorted/failure carrier vocabulary

PressureDiagnosticDecomposition
  -> named recovered diagnostics and no-overlap consumers
```

This is the intended separation.  The no-overlap pair diagnostic API should be
used from `PressureDiagnosticDecomposition` or later downstream modules, not
from `PressureFrontier` or `PressureAccounting`.

## Two-stage API confirmed

The two-stage arbitrary-list diagnostic API remains:

```text
sorted-before failure
  -> pairDiagnostic-or-adjacentOverlap

sorted-before failure + no-adjacent-overlap
  -> exists pairDiagnostic
```

The branch split keeps overlap visible.  The recovered diagnostic extraction is
only available once the caller supplies no-overlap.

## Guardrails

No theorem was added for:

- length-six decomposition,
- arbitrary-list recursion,
- canonical first diagnosis,
- enumeration of all diagnostics,
- aggregation over multiple recovered diagnostics,
- list-wide interval union accounting,
- coverage,
- maximality,
- uniqueness,
- sorting,
- overlap repair,
- disjointness between multiple recovered families,
- Collatz convergence.

## Line-count status

```text
  1517 DkMath/Collatz/PetalBridge/PressureFrontier.lean
  1896 DkMath/Collatz/PetalBridge/PressureAccounting.lean
  1130 DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean
  4543 total
```

All inspected files remain under the 2,000-line split threshold.

## Verification

Commands run from `lean/dk_math`:

```text
lake build DkMath.Collatz.PetalBridge.PressureDiagnosticDecomposition
lake build DkMath.Collatz.PetalBridge.PressureAccounting
lake build DkMath.Collatz.PetalBridge.PressureFrontier
lake build DkMath.Collatz.PetalBridge
```

Result: all builds passed.

No-sorry check over the requested files:

```text
rg -n "\bsorry\b|admit" \
  DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean \
  DkMath/Collatz/PetalBridge/PressureAccounting.lean \
  DkMath/Collatz/PetalBridge/PressureFrontier.lean
```

Result: no matches.

`git diff --check` passed.

Known unrelated warning:

```text
DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:152:6:
declaration uses `sorry`
```

This checkpoint did not touch that file.
