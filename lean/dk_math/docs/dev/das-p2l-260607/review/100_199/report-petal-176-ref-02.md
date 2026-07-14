# Report Petal 176-ref-02

## Scope

This checkpoint updated the Collatz documentation to match the refactored
`DkMath.Collatz.PetalBridge` package structure.

No Lean theorem statements were changed in this checkpoint.

## Updated Documents

Updated:

```text
DkMath/Collatz/docs/Collatz-Overview.md
DkMath/Collatz/docs/Collatz-Package-Structure.md
DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
```

The updates record that `DkMath.Collatz.PetalBridge` is now a public aggregator
over a split subpackage.

## Main Synchronization Points

The docs now mention the current module layout:

```text
Basic / Residues / Profiles / Counts / Ratios
Mass / PressureCore / PressureCounts
HeightBudget / TailSplits / TailGrammar / DriftBudget / PressureDecay
PressureFrontier
PressureAccounting
PressureLocalWitnessObstruction
PressureAdjacentDiagnosis
OneCycle / ValuationFlowBridge / Collision
```

The docs also record the checkpoint `176-ref-01` split:

```text
PressureAccounting
  base interval-pulse and accounted-family layer

PressureLocalWitnessObstruction
  witness-level before/overlap and bounded obstruction diagnosis

PressureAdjacentDiagnosis
  adjacent-pair diagnosis carriers and small fixed-list wrappers
```

## Guardrails Preserved In Docs

The documentation now repeats the important non-claims at the package level:

```text
no global local-island coverage
no maximality or uniqueness
no arbitrary list sorting theorem
no interval union accounting
no overlap repair without extra hypotheses
no Collatz convergence theorem
```

Recovered budgets are described as pair-local, and overlap remains an explicit
obstruction branch for the supplied adjacent witness list.

## Verification

Documentation-only checkpoint.

Passed:

```bash
git diff --check
```

No Lean build was required because this checkpoint changed only Markdown files.

## Next Candidate

Return to normal theorem development on top of the refactored package surface.
If additional refactoring becomes necessary, split one module at a time and keep
the public `DkMath.Collatz.PetalBridge` aggregator stable.
