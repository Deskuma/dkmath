# report-petal-206

## Situation

Checkpoint `petal-206` packages the cp205 existential Beam target extraction
as a named addressed carrier.

The accepted Core before this checkpoint was:

```text
SourcePressureBeamSeed L
  -> exists j, SourcePressureBeamSeedContainsDepth L j
               and SourcePressureBeamDepthTarget n k r j
```

This checkpoint does not strengthen that statement.  It only gives the paired
fact a reusable API name.

## Carrier Added

Implemented:

```lean
def SourcePressureBeamAddressedDepthTarget
    {n : OddNat} {k r : ℕ}
    (L : List (SourcePressureLocalIslandWitness n k r))
    (j : ℕ) : Prop :=
  SourcePressureBeamSeedContainsDepth L j ∧
    SourcePressureBeamDepthTarget n k r j
```

Meaning:

```text
depth j is addressed by the supplied witness list L,
and j is a Beam depth target.
```

This is a local addressed carrier.  It is not a canonical selector and does not
transport arbitrary external depths.

## True Beam Facts

Implemented projection helpers:

```lean
theorem sourcePressureBeamSeedContainsDepth_of_addressedDepthTarget
theorem sourcePressureBeamDepthTarget_of_addressedDepthTarget
```

Implemented constructor helper:

```lean
theorem sourcePressureBeamAddressedDepthTarget_mk
```

Implemented seed extraction:

```lean
theorem exists_sourcePressureBeamAddressedDepthTarget_of_seed
```

Implemented the one-step-ahead projection:

```lean
theorem sourcePressureMargin_pos_of_addressedDepthTarget
```

This last theorem is only projection composition:

```text
AddressedDepthTarget
  -> BeamDepthTarget
  -> positive source-pressure margin
```

It is not propagation.

## Experimental Lemma Table

| experiment | theorem | status | note |
| --- | --- | --- | --- |
| T1 | `sourcePressureBeamSeedContainsDepth_of_addressedDepthTarget` | passed | containment projection |
| T1 | `sourcePressureBeamDepthTarget_of_addressedDepthTarget` | passed | target projection |
| T2 | `sourcePressureBeamAddressedDepthTarget_mk` | passed | carrier constructor |
| T3 | `exists_sourcePressureBeamAddressedDepthTarget_of_seed` | passed | seed gives existential addressed carrier |
| bonus | `sourcePressureMargin_pos_of_addressedDepthTarget` | passed | addressed target opens to positive margin |
| G1 | `SourcePressureBeamSeed L -> SourcePressureBeamAddressedDepthTarget L j` | under-specified | arbitrary external `j` is not selected by the seed |

## False Beam / Gap

The known Gap remains unchanged:

```text
SourcePressureBeamSeed L -> SourcePressureBeamDepthTarget n k r j
```

for arbitrary external `j`.

The addressed carrier does not remove this Gap.  It records only the depth that
is explicitly obtained from the supplied witness list.

No new negated theorem was added.

## Packaging, Not Propagation

This checkpoint is strictly an API packaging step.

No theorem was added for:

- arbitrary target transport;
- canonical target selection;
- propagation over time or orbit;
- convergence;
- global coverage;
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

The carrier now exposes three stable projections:

```text
AddressedDepthTarget -> containsDepth
AddressedDepthTarget -> depthTarget
AddressedDepthTarget -> margin_pos
```

The next safe step is not transport yet.  A natural next checkpoint is to add
thin existential wrappers around these projections, for example:

```text
SourcePressureBeamSeed L
  -> exists j, 0 < SourcePressureMarginInt n k (r + j)
```

That would still be existential and addressed by the seed.  It would not claim
that every depth is positive, nor that the Beam propagates.

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

