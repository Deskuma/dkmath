# report-petal-213

## Situation

Checkpoint petal-213 opens the cp212 normalized Beam classifier into
mass-difference form.

The cp212 classifier was:

```text
True:
  2 * continuationDrop < retentionDrop + current

False:
  retentionDrop + current <= 2 * continuationDrop
```

This checkpoint records that both drops are already definitionally mass
differences, and then rewrites the classifier through those definitions.

This remains local to one addressed pressure-depth edge.

## Definition Shapes

The exact shapes found in `PressureDecay.lean` are:

```lean
SourceRetentionDropInt n k r j =
  (orbitWindowRetentionMassPow2 n k (r + j) : ℤ) -
    (orbitWindowRetentionMassPow2 n k (r + j + 1) : ℤ)
```

and

```lean
SourceContinuationDropInt n k r j =
  (orbitWindowContinuationSiblingMassPow2 n k (r + j) : ℤ) -
    (orbitWindowContinuationSiblingMassPow2 n k (r + j + 1) : ℤ)
```

So the expected `r + j` / `r + j + 1` adjacent-depth indexing is exact.

## Drop Expansion Wrappers

Implemented in `DkMath.Collatz.PetalBridge.PressureBeam`:

```lean
sourceRetentionDrop_eq_current_sub_next_mass_of_addressedDepthTarget
sourceContinuationDrop_eq_current_sub_next_mass_of_addressedDepthTarget
```

Both are definitional wrappers proved by `rfl`.  The addressed hypothesis is
unused arithmetically, but it keeps the theorem surface Beam-facing.

## True Beam

Implemented:

```lean
sourcePressureMargin_next_pos_iff_two_contMassDiff_lt_retMassDiff_add_current
```

This reads:

```text
0 < nextMargin
  iff
2 * (currentContinuationMass - nextContinuationMass)
  <
(currentRetentionMass - nextRetentionMass) + currentMargin
```

The proof rewrites the cp212 True classifier with the two drop-expansion
wrappers.

## False Beam

Implemented:

```lean
sourcePressureMargin_next_nonpos_iff_retMassDiff_add_current_le_two_contMassDiff
```

This reads:

```text
nextMargin <= 0
  iff
(currentRetentionMass - nextRetentionMass) + currentMargin
  <=
2 * (currentContinuationMass - nextContinuationMass)
```

The proof rewrites the cp212 False classifier with the same drop-expansion
wrappers.

## Gap

No mismatch was found in the mass functions, cast shape, orientation, or index
shape.  The remaining Gap is not definitional; it is the next algebraic
normalization step after mass differences are opened.

In particular, the next natural comparison would move all current masses to
one side and all next masses/current margin terms to the other side.

## Not Propagation

This is a mass-difference reading, not a propagation theorem.

No theorem was added for:

- time or orbit propagation
- arbitrary target transport
- arbitrary next-margin positivity
- canonical target selection
- global coverage
- convergence
- arbitrary-list recursive decomposition
- enumeration of all diagnostics
- aggregation over multiple recovered diagnostics
- interval union accounting
- overlap repair
- maximality
- uniqueness
- sorting
- disjointness between multiple recovered families

## Wise Wolf Inference

The next layer can normalize the opened mass-difference inequalities by moving
terms:

```text
2 * (contNow - contNext) < (retNow - retNext) + current
```

toward a direct mass-balance comparison such as:

```text
2 * contNow + retNext < retNow + current + 2 * contNext
```

and the corresponding nonpositive inequality:

```text
retNow - retNext + current <= 2 * (contNow - contNext)
```

This would turn the classifier from a drop comparison into a direct
current/next mass-balance surface.

## Experimental Lemma Table

| experiment | status | theorem |
| --- | --- | --- |
| Step 1 | passed | exact `r + j` / `r + j + 1` definition shapes confirmed |
| T1 | passed | `sourceRetentionDrop_eq_current_sub_next_mass_of_addressedDepthTarget` |
| T2 | passed | `sourceContinuationDrop_eq_current_sub_next_mass_of_addressedDepthTarget` |
| T3 | passed | `sourcePressureMargin_next_pos_iff_two_contMassDiff_lt_retMassDiff_add_current` |
| F1 | passed | `sourcePressureMargin_next_nonpos_iff_retMassDiff_add_current_le_two_contMassDiff` |
| G1 | no mismatch | mass expansion was definitional |

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
