# report-petal-227

## Checkpoint

`petal-227`

## Goal

Investigate whether the cp226 Pulse-level full diagnostic theorem has an
immediate higher-level caller without forcing a broad new API.

The theorem under inspection was:

```lean
sourcePressureBeamPulse_witness_singleton_full_diagnostic
```

It consumes one explicit witness membership `W ∈ L` and packages:

- entry mass-balance: `left < right`;
- list-relative addressed depth at the singleton right edge;
- exit mass-balance: `right <= left`.

## Files Inspected

Primary:

- `DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean`
- `DkMath/Collatz/PetalBridge/PressureBeam.lean`
- `DkMath/Collatz/PetalBridge/PressureAutomaton.lean`

Secondary context:

- `DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean`
- `DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean`
- `DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean`

## Finding

The useful immediate caller is not the lower diagnostic modules.  Those modules
classify obstruction and adjacent-witness phenomena and should not import the
Beam layer.

The clean caller is instead the Beam seed surface:

```lean
SourcePressureBeamSeed L
```

The seed API already exposes an existential contained witness through
`exists_sourcePressureBeamSeedContainsDepth_of_seed`.  That is enough to obtain
an explicit `W ∈ L`, so the cp226 full diagnostic can be applied directly.

## Added Theorem

Added in `DkMath.Collatz.PetalBridge.PressureBeam.Pulse`:

```lean
theorem exists_sourcePressureBeamPulse_witness_singleton_full_diagnostic_of_seed
```

Meaning:

```text
SourcePressureBeamSeed L
  -> exists W in L
       such that W's singleton pulse has the full local entry-depth-exit
       diagnostic.
```

This theorem consumes:

```lean
sourcePressureBeamPulse_witness_singleton_full_diagnostic
```

It does not rebuild the entry/depth/exit facts manually.  It only opens the
seed existential witness and passes its membership to the cp226 diagnostic
package.

## Boundary

This is local explicit-witness API consumption only.

It does not claim:

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

The new theorem was placed in `PressureBeam/Pulse.lean`, above the diagnostic
modules.  No lower diagnostic module imports `PressureBeam`.

## Verification

Commands run from `lean/dk_math` unless noted:

```text
lake build DkMath.Collatz.PetalBridge.PressureBeam.Pulse
lake build DkMath.Collatz.PetalBridge.PressureBeam
lake build DkMath.Collatz.PetalBridge
```

All builds completed successfully.

Additional checks from repository root:

```text
rg -n "sorry|admit" lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam
git diff --check
```

The no-sorry grep found no matches in the PressureBeam split files.
`git diff --check` passed.

Known unrelated warning observed during builds:

```text
DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:152:6:
declaration uses `sorry`
```

## Next Inference

The seed-to-diagnostic path is now explicit:

```text
SourcePressureBeamSeed L
  -> exists W ∈ L
  -> full local singleton pulse diagnostic for W
```

The next useful question is whether `PressureAutomaton` failure resolution can
expose a similarly explicit witness membership from its recovered adjacent
pair, without turning that into coverage or canonical selection.
