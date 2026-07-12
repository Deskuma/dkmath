# report-petal-210

## Situation

Checkpoint `petal-210` refines the local sign-reading layer from cp209.

The previous split was:

```text
True Beam:
  current positive + netDrop >= 0 -> next positive

False Beam:
  netDrop <= -current -> next nonpositive
```

This checkpoint sharpens the True Beam side:

```text
-current < netDrop -> next positive
```

This allows a negative net drop as long as it is not large enough to cross zero.

## True Beam Facts

Implemented:

```lean
theorem sourcePressureMargin_next_pos_of_addressedDepthTarget_of_neg_current_lt_netDrop
```

Meaning:

```text
AddressedDepthTarget L j
  and -current margin < netDrop
  -> next margin > 0
```

Implemented:

```lean
theorem sourcePressureMargin_next_pos_of_addressedDepthTarget_of_current_add_netDrop_pos
```

Meaning:

```text
AddressedDepthTarget L j
  and current margin + netDrop > 0
  -> next margin > 0
```

Implemented:

```lean
theorem exists_sourcePressureMargin_next_pos_of_beamSeed_of_neg_current_lt_netDrop_at_addressed
```

Meaning:

```text
SourcePressureBeamSeed L
  and every addressed depth satisfies -current < netDrop
  -> exists addressed j whose next margin is positive
```

The universal hypothesis remains restricted to addressed depths.

## Bonus Local Classifiers

Lean also accepted the exact local `iff` classifiers:

```lean
theorem sourcePressureMargin_next_pos_iff_neg_current_lt_netDrop_of_addressedDepthTarget
```

and

```lean
theorem sourcePressureMargin_next_nonpos_iff_netDrop_le_neg_current_of_addressedDepthTarget
```

These classify the next sign at the addressed edge:

```text
next positive iff -current < netDrop
next nonpositive iff netDrop <= -current
```

This is still purely local arithmetic after opening the transition equation.

## False Beam Boundary

The existing fall-out theorem remains the local False Beam boundary:

```lean
theorem sourcePressureMargin_next_nonpos_of_addressedDepthTarget_of_netDrop_le_neg_current
```

The bonus iff theorem packages the same boundary as an exact classifier:

```text
next nonpositive iff netDrop <= -current
```

No global failure or propagation theorem was added.

## Gap Observations

The following remain under-specified:

```text
SourcePressureBeamAddressedDepthTarget L j
  -> next margin > 0
```

```text
SourcePressureBeamAddressedDepthTarget L j
  -> next margin <= 0
```

An addressed target gives current positivity, but the next sign is decided by
the comparison between `netDrop` and `-current`.  Without that comparison, Lean
does not select a sign.

## Experimental Lemma Table

| experiment | theorem | status | note |
| --- | --- | --- | --- |
| T1 | `sourcePressureMargin_next_pos_of_addressedDepthTarget_of_neg_current_lt_netDrop` | passed | sharp local True Beam condition |
| T2 | `sourcePressureMargin_next_pos_of_addressedDepthTarget_of_current_add_netDrop_pos` | passed | direct sum condition |
| T3 | `exists_sourcePressureMargin_next_pos_of_beamSeed_of_neg_current_lt_netDrop_at_addressed` | passed | existential addressed seed version |
| F1 | existing fall-out theorem | available | `netDrop <= -current -> next <= 0` |
| bonus | `sourcePressureMargin_next_pos_iff_neg_current_lt_netDrop_of_addressedDepthTarget` | passed | exact True classifier |
| bonus | `sourcePressureMargin_next_nonpos_iff_netDrop_le_neg_current_of_addressedDepthTarget` | passed | exact False classifier |
| G1 | next positive from addressed target alone | under-specified | netDrop comparison missing |
| G2 | next nonpositive from addressed target alone | under-specified | netDrop comparison missing |

## Sharp Local Reading, Not Propagation

This checkpoint proves only local sign facts at one addressed pressure-depth
edge.  It does not move an orbit, extend a time path, or choose a canonical
next target.

No theorem was added for:

- time/orbit propagation;
- arbitrary target transport;
- arbitrary margin positivity;
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

The local sign classifier is now essentially complete:

```text
True:
  -current < netDrop

False:
  netDrop <= -current
```

The next useful layer is to read `netDrop` itself:

```text
SourcePressureNetDropInt
  = retention drop - 2 * continuation drop
```

The likely next checkpoint should connect these sharp sign classifiers to the
existing retention / continuation / drift-budget vocabulary, still locally at
the addressed edge.

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

