# report-petal-215

## Situation

Checkpoint petal-215 was an API-design checkpoint.

cp214 exposed the local addressed-edge mass-balance classifier in expanded
form:

```text
True:
  2 * contNow + retNext < retNow + currentMargin + 2 * contNext

False:
  retNow + currentMargin + 2 * contNext <= 2 * contNow + retNext
```

The question was whether this expanded theorem surface is sufficient, or
whether the two sides should receive names.

## Inspection

I inspected:

- `PressureBeam.lean`, especially the cp214 expanded classifier surface
- nearby Collatz / Petal / ABC namespaces for existing `Left/Right` balance
  naming patterns
- existing pressure-layer integer definitions, such as
  `SourcePressureMarginInt`, `SourceRetentionDropInt`,
  `SourceContinuationDropInt`, and `SourcePressureNetDropInt`

No established left/right mass-balance naming pattern was found nearby.

However, the expanded mass-balance expressions already occurred repeatedly in
cp214 theorem statements and wrappers.  They are also the likely input shape
for the next local classifier layer.  Therefore a thin naming API is useful.

## API Decision

I added named left/right mass-balance expressions.

This is not new proof power.  It is API packaging:

```text
left  := 2 * contNow + retNext
right := retNow + currentMargin + 2 * contNext
```

The definitions remain in `PressureBeam.lean` because they package the local
Beam classifier and do not assert global propagation.

## Added Definitions

Implemented in `DkMath.Collatz.PetalBridge.PressureBeam`:

```lean
SourcePressureBeamMassBalanceLeftInt
SourcePressureBeamMassBalanceRightInt
```

Expansion wrappers:

```lean
sourcePressureBeamMassBalanceLeftInt_eq
sourcePressureBeamMassBalanceRightInt_eq
```

## True Beam Packaging

Implemented:

```lean
sourcePressureMargin_next_pos_iff_massBalanceLeft_lt_right
sourcePressureMargin_next_pos_of_massBalanceLeft_lt_right
```

This packages the cp214 True classifier as:

```text
0 < nextMargin iff left < right
```

## False Beam Packaging

Implemented:

```lean
sourcePressureMargin_next_nonpos_iff_massBalanceRight_le_left
sourcePressureMargin_next_nonpos_of_massBalanceRight_le_left
```

This packages the cp214 False classifier as:

```text
nextMargin <= 0 iff right <= left
```

## Guardrails

This checkpoint is about API ergonomics, not new proof power.

No theorem was added for:

- time or orbit propagation
- arbitrary target transport
- arbitrary next positivity
- canonical target selection
- global coverage
- convergence
- aggregation
- overlap repair

The addressed target still only selects the local edge where the classifier is
read.  It does not choose global behavior.

## Wise Wolf Inference

The next useful step is now easier to state.

Instead of carrying long expanded expressions, later checkpoints can compare:

```text
SourcePressureBeamMassBalanceLeftInt n k r j
SourcePressureBeamMassBalanceRightInt n k r j
```

This should reduce theorem statement noise if the next layer studies:

- strict True margin decisions
- nonpositive False margin decisions
- equality boundary cases
- obstruction surfaces where `left = right`

The equality boundary is especially attractive as a future False/Gap surface:

```text
left = right
```

because it is exactly the knife-edge between `left < right` and `right <= left`.

## Experimental Lemma Table

| item | status | result |
| --- | --- | --- |
| inspect naming pattern | passed | no nearby established left/right balance convention found |
| add left/right defs | passed | `SourcePressureBeamMassBalanceLeftInt`, `SourcePressureBeamMassBalanceRightInt` |
| expansion wrappers | passed | both by `rfl` |
| True Beam packaging | passed | `left < right` classifier and wrapper |
| False Beam packaging | passed | `right <= left` classifier and wrapper |
| propagation | intentionally not added | outside checkpoint scope |

## Verification

Commands run:

```text
lake build DkMath.Collatz.PetalBridge.PressureBeam
lake build DkMath.Collatz.PetalBridge
rg -n "\bsorry\b|admit" DkMath/Collatz/PetalBridge/PressureBeam.lean DkMath/Collatz/PetalBridge/PressureAutomaton.lean DkMath/Collatz/PetalBridge/PressureDiagnosticDecomposition.lean DkMath/Collatz/PetalBridge/PressureAdjacentDiagnosis.lean DkMath/Collatz/PetalBridge/PressureLocalWitnessObstruction.lean DkMath/Collatz/PetalBridge/PressureAccounting.lean DkMath/Collatz/PetalBridge/PressureFrontier.lean DkMath/Collatz/PetalBridge/PressureDecay.lean DkMath/Collatz/PetalBridge/DriftBudget.lean
git diff --check
```

Results:

- `lake build DkMath.Collatz.PetalBridge.PressureBeam`: passed
- `lake build DkMath.Collatz.PetalBridge`: passed
- no-sorry check on the listed pressure files: no matches
- `git diff --check`: passed

Known unrelated build warning remains:

```text
DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:152:6:
declaration uses `sorry`
```
