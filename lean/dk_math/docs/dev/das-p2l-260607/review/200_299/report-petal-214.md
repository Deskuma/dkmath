# report-petal-214

## Situation

Checkpoint petal-214 normalizes the cp213 mass-difference Beam classifier into
direct mass-balance form.

The cp213 layer read the next sign through adjacent mass differences:

```text
True:
  2 * (contNow - contNext) < (retNow - retNext) + current

False:
  (retNow - retNext) + current <= 2 * (contNow - contNext)
```

This checkpoint moves the linear terms across the inequality and exposes a
direct current/next mass-balance comparison.

This is still local to a single addressed pressure-depth edge.

## True Beam

Implemented in `DkMath.Collatz.PetalBridge.PressureBeam`:

```lean
sourcePressureMargin_next_pos_iff_massBalance_lt_of_addressedDepthTarget
```

This proves:

```text
0 < nextMargin
  iff
2 * contNow + retNext < retNow + currentMargin + 2 * contNext
```

The proof rewrites through the cp213 mass-difference classifier and closes the
linear normalization with `omega`.

Also added the one-way wrapper:

```lean
sourcePressureMargin_next_pos_of_addressedDepthTarget_of_massBalance_lt
```

## False Beam

Implemented:

```lean
sourcePressureMargin_next_nonpos_iff_massBalance_le_of_addressedDepthTarget
```

This proves:

```text
nextMargin <= 0
  iff
retNow + currentMargin + 2 * contNext <= 2 * contNow + retNext
```

The proof is the nonpositive companion to the True Beam mass-balance theorem.

Also added the one-way wrapper:

```lean
sourcePressureMargin_next_nonpos_of_addressedDepthTarget_of_massBalance_le
```

## Gap

The addressed target alone still does not choose global behavior.  It only
selects the local edge where the classifier is being read.

The remaining Gap is not the algebraic mass-balance form; that part is now
fixed.  The next missing relation is a usable source of the mass-balance
inequality itself.

## Not Propagation

This checkpoint is algebraic mass-balance normalization, not propagation.

No theorem was added for:

- time or orbit propagation
- arbitrary target transport
- canonical target selection
- global coverage
- convergence
- aggregation over multiple recovered diagnostics
- overlap repair

## Wise Wolf Inference

The next natural layer is to name the two sides of the mass-balance inequality.

Possible reading:

```text
leftMassBalance  := 2 * contNow + retNext
rightMassBalance := retNow + currentMargin + 2 * contNext
```

Then the local Beam classifier becomes:

```text
True  iff leftMassBalance < rightMassBalance
False iff rightMassBalance <= leftMassBalance
```

This would make later callers less dependent on the long expanded expression.

## Experimental Lemma Table

| experiment | status | theorem |
| --- | --- | --- |
| T1 | passed | `sourcePressureMargin_next_pos_iff_massBalance_lt_of_addressedDepthTarget` |
| F1 | passed | `sourcePressureMargin_next_nonpos_iff_massBalance_le_of_addressedDepthTarget` |
| T2 | passed | `sourcePressureMargin_next_pos_of_addressedDepthTarget_of_massBalance_lt` |
| F2 | passed | `sourcePressureMargin_next_nonpos_of_addressedDepthTarget_of_massBalance_le` |
| Gap | under-specified | addressed edge alone does not provide the mass-balance inequality |

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
