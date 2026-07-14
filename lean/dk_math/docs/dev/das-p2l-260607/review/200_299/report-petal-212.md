# report-petal-212

## Situation

Checkpoint petal-212 normalizes the Beam-facing sign classifier from cp211.

The previous layer had already expanded the local net drop as

```text
netDrop = retentionDrop - 2 * continuationDrop
```

and expressed the next margin sign by comparing this value with the negative
current margin.  This checkpoint rewrites that classifier into direct
count-style inequalities:

```text
True Beam:
  2 * continuationDrop < retentionDrop + current

False Beam:
  retentionDrop + current <= 2 * continuationDrop
```

This remains strictly local to an addressed pressure-depth edge.

## True Beam

Implemented in `DkMath.Collatz.PetalBridge.PressureBeam`:

```lean
sourcePressureMargin_next_pos_iff_two_cont_lt_ret_add_current_of_addressedDepthTarget
```

This proves the normalized True classifier:

```text
0 < nextMargin
  iff
2 * continuationDrop < retentionDrop + currentMargin
```

Also added the one-way wrapper:

```lean
sourcePressureMargin_next_pos_of_addressedDepthTarget_of_two_cont_lt_ret_add_current
```

## False Beam

Implemented:

```lean
sourcePressureMargin_next_nonpos_iff_ret_add_current_le_two_cont_of_addressedDepthTarget
```

This proves the normalized False classifier:

```text
nextMargin <= 0
  iff
retentionDrop + currentMargin <= 2 * continuationDrop
```

Also added the one-way wrapper:

```lean
sourcePressureMargin_next_nonpos_of_addressedDepthTarget_of_ret_add_current_le_two_cont
```

## Arithmetic

Both equivalences are obtained from the cp211 retention/continuation
classifier, followed by `omega`.

The normalized moves are:

```text
-current < retention - 2 * continuation
  iff
2 * continuation < retention + current
```

and

```text
retention - 2 * continuation <= -current
  iff
retention + current <= 2 * continuation
```

## Gap

The addressed target alone still does not determine the next sign.

The missing relation is exactly the normalized inequality.  In other words,
the current Core can classify a local addressed edge once the retention /
continuation comparison is supplied, but it does not prove arbitrary next
positivity or arbitrary next nonpositivity from `haddr` alone.

## Not Propagation

This checkpoint is inequality normalization, not propagation.

No theorem was added for:

- time or orbit propagation
- arbitrary target transport
- arbitrary positivity
- arbitrary next-positivity
- convergence
- global coverage
- aggregation over multiple recovered diagnostics
- overlap repair

## Wise Wolf Inference

The next natural layer is to unfold `retentionDrop` and `continuationDrop`
themselves into mass differences.

Expected next reading:

```text
retentionDrop
  = currentRetentionMass - nextRetentionMass

continuationDrop
  = currentContinuationMass - nextContinuationMass
```

Then the Beam classifier becomes a mass-comparison instruction rather than a
sign-comparison instruction.

## Experimental Lemma Table

| experiment | status | theorem |
| --- | --- | --- |
| T1 | passed | `sourcePressureMargin_next_pos_iff_two_cont_lt_ret_add_current_of_addressedDepthTarget` |
| F1 | passed | `sourcePressureMargin_next_nonpos_iff_ret_add_current_le_two_cont_of_addressedDepthTarget` |
| T2 | passed | `sourcePressureMargin_next_pos_of_addressedDepthTarget_of_two_cont_lt_ret_add_current` |
| F2 | passed | `sourcePressureMargin_next_nonpos_of_addressedDepthTarget_of_ret_add_current_le_two_cont` |
| G1 | under-specified | next sign from `haddr` alone still needs the normalized inequality |

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
