# Report Petal 176-ref-01

## Scope

This checkpoint performed a refactor-only split of the Collatz pressure
accounting surface.

The goal was to reduce
`DkMath.Collatz.PetalBridge.PressureAccounting` below 2000 lines while keeping
the theorem surface and mathematical meaning unchanged.

## Implemented Refactor

### New module: `PressureLocalWitnessObstruction`

Added:

```lean
DkMath.Collatz.PetalBridge.PressureLocalWitnessObstruction
```

This module now owns the local-witness layer:

- witness-level before / overlap predicates
- pair sorted-before failure wrappers
- pair overlap obstruction predicates
- adjacent overlap obstruction predicates
- bounded pair and length-three diagnosis theorems
- raw pair budget wrappers

The module comment records the main semantic guardrail:

```text
local explicit witnesses only;
no global coverage;
no arbitrary list sorting;
no interval merging;
no Collatz convergence claim.
```

### New module: `PressureAdjacentDiagnosis`

Added:

```lean
DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis
```

This module now owns the adjacent-diagnosis layer:

- `SourcePressureLocalIslandWitnessAdjacentDiagnosis`
- adjacent-pair-in-list predicates
- bounded three/four/five witness adjacent diagnosis wrappers
- recovered-or-list-failure projections

This keeps the finite adjacent-pair diagnostic API out of the base accounting
file.

### Public import update

Updated:

```lean
DkMath.Collatz.PetalBridge
```

Import order is now:

```lean
PressureAccounting
PressureLocalWitnessObstruction
PressureAdjacentDiagnosis
```

This preserves the public aggregator surface while allowing the base module to
stay thin.

## Line Counts

After refactor:

```text
1896 DkMath/Collatz/PetalBridge/PressureAccounting.lean
1376 DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean
 545 DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
3817 total
```

The primary target is achieved:

```text
PressureAccounting.lean < 2000 lines
```

## Verification

Passed:

```bash
lake build DkMath.Collatz.PetalBridge.PressureAccounting
lake build DkMath.Collatz.PetalBridge.PressureLocalWitnessObstruction
lake build DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis
lake build DkMath.Collatz.PetalBridge.PressureFrontier
lake build DkMath.Collatz.PetalBridge
git diff --check
```

No-sorry check on the refactored pressure files:

```bash
rg -n "\bsorry\b" \
  DkMath/Collatz/PetalBridge/PressureAccounting.lean \
  DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean \
  DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean
```

Result: no hits.

Known unrelated warning observed during builds:

```text
DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:152:6:
declaration uses `sorry`
```

## Non-Claims Preserved

The refactor did not add or strengthen mathematical claims.

In particular, it does not claim:

- global local-island coverage
- maximality or uniqueness
- arbitrary classifier completeness
- sorting algorithm correctness
- union accounting
- overlap repair
- Collatz convergence

Recovered budget theorems remain attached to explicit adjacent pairs.
Overlap remains an obstruction branch on the explicit witness list.

## Next Candidate

The next safe refactor target is not urgent: `PressureAccounting` is now below
the checkpoint threshold.  If further splitting is desired, the remaining base
file could later be divided into:

- interval-address accounting identities
- accounted-interval family/list sortedness
- local-island witness conversion and singleton family wrappers

For now, the base pressure accounting module is small enough to proceed with
ordinary theorem work again.
