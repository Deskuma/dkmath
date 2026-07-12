# report-petal-209

## Situation

Checkpoint `petal-209` starts the sign-reading layer for the Beam-facing local
margin transition.

The prior Core was:

```text
AddressedDepthTarget
  -> current margin > 0
  -> next margin = current margin + netDrop
```

This checkpoint asks Lean for the first local sign split:

```text
True Beam:
  current positive + nonnegative netDrop -> next positive

False Beam:
  current positive + sufficiently negative netDrop -> next nonpositive
```

The result is local to one addressed pressure-depth edge.  It is not time/orbit
propagation.

## Arithmetic Method

The proofs use the existing transition equation:

```lean
sourcePressureMargin_next_eq_current_add_netDrop_of_addressedDepthTarget
```

Then Lean closes the integer linear arithmetic goals with:

```lean
omega
```

No additional order lemma imports or lower-module changes were needed.

## True Beam Facts

Implemented:

```lean
theorem sourcePressureMargin_next_pos_of_addressedDepthTarget_of_netDrop_nonneg
```

Meaning:

```text
AddressedDepthTarget L j
  and 0 <= SourcePressureNetDropInt n k r j
  -> next margin at r + j + 1 is positive
```

Implemented:

```lean
theorem exists_sourcePressureMargin_next_pos_of_beamSeed_of_netDrop_nonneg_at_addressed
```

Meaning:

```text
SourcePressureBeamSeed L
  and every addressed depth in L has nonnegative netDrop
  -> exists addressed j whose next margin is positive
```

The universal net-drop hypothesis is restricted to addressed depths:

```lean
∀ j,
  SourcePressureBeamAddressedDepthTarget L j →
    0 ≤ SourcePressureNetDropInt n k r j
```

This is not arbitrary next-margin positivity.

## False Beam Fact

Implemented:

```lean
theorem sourcePressureMargin_next_nonpos_of_addressedDepthTarget_of_netDrop_le_neg_current
```

Meaning:

```text
AddressedDepthTarget L j
  and netDrop <= - current margin
  -> next margin <= 0
```

This is a genuine local False Beam condition: the addressed point falls out of
the positive region at the next adjacent depth.

## Gap Observations

The following remain under-specified:

```text
SourcePressureBeamAddressedDepthTarget L j
  -> 0 < SourcePressureMarginInt n k (r + j + 1)
```

```text
SourcePressureBeamAddressedDepthTarget L j
  -> SourcePressureMarginInt n k (r + j + 1) <= 0
```

The addressed target gives current positivity, but it does not constrain the
sign or size of `SourcePressureNetDropInt n k r j`.  Without a net-drop
hypothesis, Lean has no reason to choose the next sign.

## Experimental Lemma Table

| experiment | theorem | status | note |
| --- | --- | --- | --- |
| Step 1 | Int linear arithmetic | passed | `omega` closed the local sign goals |
| T1 | `sourcePressureMargin_next_pos_of_addressedDepthTarget_of_netDrop_nonneg` | passed | local True Beam preservation |
| T2 | `exists_sourcePressureMargin_next_pos_of_beamSeed_of_netDrop_nonneg_at_addressed` | passed | existential addressed seed version |
| F1 | `sourcePressureMargin_next_nonpos_of_addressedDepthTarget_of_netDrop_le_neg_current` | passed | local False Beam fall-out |
| G1 | next positive from addressed target alone | under-specified | netDrop sign missing |
| G2 | next nonpositive from addressed target alone | under-specified | netDrop sign missing |

## Local Sign Reading, Not Propagation

This checkpoint only proves local sign consequences of the local transition
equation at an addressed depth.

No theorem was added for:

- time/orbit propagation;
- arbitrary target transport;
- arbitrary margin positivity;
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

The next natural layer is net-drop classification.

The current split is:

```text
netDrop >= 0
  -> next positive

netDrop <= -current
  -> next nonpositive
```

The remaining middle region is:

```text
-current < netDrop < 0
```

In that region the next margin is still positive, because the drop is negative
but not large enough to cross zero.  A likely next checkpoint is therefore:

```text
AddressedDepthTarget L j
  and -current < netDrop
  -> next positive
```

This would refine the True Beam side from `netDrop >= 0` to the sharp local
condition `current + netDrop > 0`.

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

