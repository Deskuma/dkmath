# report-petal-207

## Situation

Checkpoint `petal-207` asks for the next True Beam projection from a raw Beam
seed:

```text
SourcePressureBeamSeed L
  -> exists addressed target
  -> exists positive source-pressure margin
```

The goal is still existential.  The seed selects a depth through the explicit
witness list, and the margin positivity is read at that same selected depth.

## True Beam Facts

Implemented:

```lean
theorem exists_sourcePressureMargin_pos_of_beamSeed
```

This proves:

```text
SourcePressureBeamSeed L
  -> ∃ j, 0 < SourcePressureMarginInt n k (r + j)
```

Implemented:

```lean
theorem exists_sourcePressureBeamAddressedDepthTarget_and_margin_pos_of_seed
```

This keeps the addressed carrier and margin positivity paired at the same
existential depth.

Implemented:

```lean
theorem exists_sourcePressureBeamDepthTarget_and_margin_pos_of_seed
```

This is the thinner package for callers that need the Beam target and margin
positivity but do not need the list-address component.

## Experimental Lemma Table

| experiment | theorem | status | note |
| --- | --- | --- | --- |
| T1 | `exists_sourcePressureMargin_pos_of_beamSeed` | passed | seed exposes some positive margin |
| T2 | `exists_sourcePressureBeamAddressedDepthTarget_and_margin_pos_of_seed` | passed | addressed target and margin paired |
| T3 | `exists_sourcePressureBeamDepthTarget_and_margin_pos_of_seed` | passed | target and margin paired without address projection |
| G1 | `SourcePressureBeamSeed L -> 0 < SourcePressureMarginInt n k (r + j)` | under-specified | arbitrary external `j` is not selected by the seed |
| G1 | `SourcePressureBeamSeed L -> SourcePressureBeamAddressedDepthTarget L j` | under-specified | arbitrary external `j` remains outside the seed address |

## False Beam / Gap

The known Gaps remain:

```text
SourcePressureBeamSeed L -> SourcePressureBeamDepthTarget n k r j
SourcePressureBeamSeed L -> SourcePressureBeamAddressedDepthTarget L j
SourcePressureBeamSeed L -> 0 < SourcePressureMarginInt n k (r + j)
```

for arbitrary external `j`.

No negated theorem was added in this checkpoint.  The current evidence is
positive but strictly existential.

## Existential Projection, Not Propagation

This checkpoint only composes existing addressed-carrier projections:

```text
Seed
  -> exists AddressedDepthTarget
  -> margin_pos at that addressed depth
```

No theorem was added for:

- arbitrary target transport;
- arbitrary margin positivity;
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

The next natural surface is the margin transition layer:

```text
positive margin at r + j
  -> relation with the next local margin / net-drop / pulse theorem
```

This should probably be a Beam-facing wrapper over existing `PressureDecay`
facts, not a new global propagation theorem.  The safe direction is:

```text
AddressedDepthTarget
  -> margin_pos
  -> local transition fact at the same addressed depth
```

Only after that layer is stable should the project ask whether a depth can move
from `j` to `j + 1`.

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

