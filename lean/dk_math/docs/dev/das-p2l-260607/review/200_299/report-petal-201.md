# report-petal-201

## Checkpoint

`petal-201` starts the Beam-facing layer above `PressureAutomaton`.

Lean code was added, but only as a thin upper boundary:

- new module: `DkMath.Collatz.PetalBridge.PressureBeam`
- aggregator import added to `DkMath.Collatz.PetalBridge`
- no lower pressure modules were modified

## Import Direction

The intended import direction is now fixed as:

```text
PressureAutomaton
  <- PressureBeam
```

The full pressure chain is:

```text
DriftBudget
  <- PressureDecay
    <- PressureFrontier
      <- PressureAccounting
        <- PressureLocalWitnessObstruction
          <- PressureAdjacentDiagnosis
            <- PressureDiagnosticDecomposition
              <- PressureAutomaton
                <- PressureBeam
```

`PressureBeam.lean` imports only:

```lean
import DkMath.Collatz.PetalBridge.PressureAutomaton
```

## Added API

The new Beam layer introduces:

```lean
def SourcePressureBeamSeed
```

This is intentionally an alias-like predicate:

```text
SourcePressureBeamSeed L := SourcePressureFailureResolution L
```

It marks the handoff from local automaton analysis to future Beam/time/orbit
transport.

Two wrapper theorems were added:

```lean
sourcePressureBeamSeed_of_sortedBeforeFailure
sourcePressureBeamSeed_recovered_of_sortedBeforeFailure_of_noAdjacentOverlap
```

Both are Beam-facing names for already proved `PressureAutomaton` facts.  They
do not add proof strength.

## Local Machinery Status

Core/local accounting and Automaton/failure resolution are now closed as local
machinery:

- `PressureDecay` owns margin/net-drop transitions.
- `PressureFrontier` owns local-island and interval-pulse production.
- `PressureAccounting` owns explicit witness-list accounting.
- `PressureAutomaton` owns local failure resolution.
- `PressureBeam` names the Beam-facing seed state above that local automaton.

Beam/global propagation is not closed yet.  The next layer still needs a
concrete statement describing how a Beam seed is transported along a time,
orbit, or Beam index.

## Guardrails

This checkpoint did not add:

- a propagation theorem;
- a convergence theorem;
- aggregation over multiple recovered diagnostics;
- global coverage;
- interval union accounting;
- overlap repair;
- arbitrary-list recursive decomposition;
- canonical first diagnosis;
- enumeration of all diagnostics;
- maximality;
- uniqueness;
- sorting theorem;
- disjointness between multiple recovered families.

Recovered diagnostics remain pair-local.  Overlap remains an obstruction
unless explicitly excluded by a hypothesis.

## Verification

Executed commands:

```text
lake build DkMath.Collatz.PetalBridge.PressureBeam
lake build DkMath.Collatz.PetalBridge
rg -n "\bsorry\b|admit" \
  DkMath/Collatz/PetalBridge/PressureBeam.lean \
  DkMath/Collatz/PetalBridge/PressureAutomaton.lean \
  DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean \
  DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean \
  DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean \
  DkMath/Collatz/PetalBridge/PressureAccounting.lean \
  DkMath/Collatz/PetalBridge/PressureFrontier.lean \
  DkMath/Collatz/PetalBridge/PressureDecay.lean \
  DkMath/Collatz/PetalBridge/DriftBudget.lean
git diff --check
```

Result:

- `lake build DkMath.Collatz.PetalBridge.PressureBeam`: passed.
- `lake build DkMath.Collatz.PetalBridge`: passed.
- no-sorry check over the pressure files listed above: no matches.
- `git diff --check`: passed.

The builds still replay the known unrelated warning in
`DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean` about an existing
`sorry`.  This checkpoint did not touch that file.

## Next Checkpoint

The next natural theorem should not be global propagation yet.  A safer next
step is to define the first explicit Beam transport predicate above
`SourcePressureBeamSeed`, with all inputs supplied explicitly:

```text
seed at one explicit witness list
  -> named candidate transport target
```

No claim about coverage, uniqueness, aggregation, or convergence should be
introduced until that transport target is concrete.
