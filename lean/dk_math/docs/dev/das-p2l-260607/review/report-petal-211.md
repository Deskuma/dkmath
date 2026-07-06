# report-petal-211

## Situation

Checkpoint `petal-211` starts the Beam-facing netDrop reading layer.

The local sign classifier from cp210 says:

```text
next positive iff -current < netDrop
next nonpositive iff netDrop <= -current
```

This checkpoint opens `netDrop` into its retention / continuation components:

```text
netDrop = retentionDrop - 2 * continuationDrop
```

The result is still local to one addressed pressure-depth edge.

## Definition Shapes Discovered

The relevant definitions in `PressureDecay` are:

```lean
noncomputable def SourceRetentionDropInt
    (n : OddNat) (k r j : ℕ) : ℤ :=
  (orbitWindowRetentionMassPow2 n k (r + j) : ℤ) -
    (orbitWindowRetentionMassPow2 n k (r + j + 1) : ℤ)
```

```lean
noncomputable def SourceContinuationDropInt
    (n : OddNat) (k r j : ℕ) : ℤ :=
  (orbitWindowContinuationSiblingMassPow2 n k (r + j) : ℤ) -
    (orbitWindowContinuationSiblingMassPow2 n k (r + j + 1) : ℤ)
```

```lean
noncomputable def SourcePressureNetDropInt
    (n : OddNat) (k r j : ℕ) : ℤ :=
  SourceRetentionDropInt n k r j -
    2 * SourceContinuationDropInt n k r j
```

The expected expansion is definitional.  No lower-module theorem was required.

## True Beam Facts

Implemented:

```lean
theorem sourcePressureNetDrop_eq_retention_sub_two_mul_continuation_of_addressedDepthTarget
```

This is a Beam-facing wrapper around the definitional equation:

```text
SourcePressureNetDropInt
  = SourceRetentionDropInt - 2 * SourceContinuationDropInt
```

The addressed target hypothesis is intentionally unused by the arithmetic
identity.  It records that the equation is being read at a Beam-selected edge.

Implemented:

```lean
theorem sourcePressureMargin_next_pos_iff_neg_current_lt_retCont_of_addressedDepthTarget
```

This packages the True Beam classifier through retention / continuation:

```text
next positive iff -current < retentionDrop - 2 * continuationDrop
```

## False Beam Fact

Implemented:

```lean
theorem sourcePressureMargin_next_nonpos_iff_retCont_le_neg_current_of_addressedDepthTarget
```

This packages the False Beam classifier through retention / continuation:

```text
next nonpositive iff retentionDrop - 2 * continuationDrop <= -current
```

## Experimental Lemma Table

| experiment | theorem | status | note |
| --- | --- | --- | --- |
| Step 1 | `SourcePressureNetDropInt` definition | inspected | definitional `retention - 2 * continuation` |
| Step 1 | `SourceRetentionDropInt` definition | inspected | current retention minus next retention |
| Step 1 | `SourceContinuationDropInt` definition | inspected | current continuation minus next continuation |
| T1 | `sourcePressureNetDrop_eq_retention_sub_two_mul_continuation_of_addressedDepthTarget` | passed | `rfl` |
| T2 | `sourcePressureMargin_next_pos_iff_neg_current_lt_retCont_of_addressedDepthTarget` | passed | True classifier with expanded netDrop |
| F1 | `sourcePressureMargin_next_nonpos_iff_retCont_le_neg_current_of_addressedDepthTarget` | passed | False classifier with expanded netDrop |

## Gap Observations

No mismatch was found for the expansion:

```text
netDrop = retentionDrop - 2 * continuationDrop
```

The remaining Gap is not definitional.  It is now a comparison problem:

```text
-current < retentionDrop - 2 * continuationDrop
```

or equivalently:

```text
retentionDrop + current > 2 * continuationDrop
```

That comparison is not yet connected to counting / drift-budget facts in the
Beam layer.

## NetDrop Reading, Not Propagation

This checkpoint only opens the local arithmetic expression used by the sign
classifier.  It does not move between time steps, select a canonical next
target, or aggregate witness lists.

No theorem was added for:

- time/orbit propagation;
- arbitrary target transport;
- arbitrary next-margin positivity;
- canonical target selection;
- global coverage;
- convergence;
- arbitrary-list recursive decomposition;
- enumeration of all diagnostics;
- aggregation over multiple recovered diagnostics;
- interval union accounting;
- overlap repair;
- maximality;
- uniqueness;
- sorting;
- disjointness between multiple recovered families.

## One-Step-Ahead Inference

The next natural checkpoint is to convert the expanded comparison into a count
inequality:

```text
-current < retentionDrop - 2 * continuationDrop
```

should become:

```text
retentionDrop + current > 2 * continuationDrop
```

and the False side should become:

```text
retentionDrop + current <= 2 * continuationDrop
```

This would move the Beam classifier from "netDrop sign" to "retention /
continuation count comparison", still locally at the addressed edge.

## Verification

Commands run:

```text
lake build DkMath.Collatz.PetalBridge.PressureBeam
lake build DkMath.Collatz.PetalBridge
rg -n "\bsorry\b|admit" DkMath/Collatz/PetalBridge/PressureBeam.lean ...
git diff --check
```

Results:

- `lake build DkMath.Collatz.PetalBridge.PressureBeam`: passed.
- `lake build DkMath.Collatz.PetalBridge`: passed.
- no-sorry check over the requested pressure files: no matches.
- `git diff --check`: passed.

Known unrelated warning remains:

```text
DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:152:6:
declaration uses `sorry`
```

