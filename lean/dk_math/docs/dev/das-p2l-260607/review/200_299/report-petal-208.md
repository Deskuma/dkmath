# report-petal-208

## Situation

Checkpoint `petal-208` starts the Beam-facing margin transition layer.

The current Beam surface before this checkpoint was:

```text
BeamSeed
  -> exists addressed target
  -> exists positive pressure margin
```

This checkpoint asks whether that addressed positive-margin point can be read
through the existing local `PressureDecay` transition equations.  The answer is
yes, but only as a local equation at the selected addressed depth.

## Exact Transition Shapes Found

The relevant existing local transition theorems in `PressureDecay` have these
shapes:

```lean
theorem sourcePressureMarginStepDiff_eq
    (n : OddNat) (k r j : ℕ) :
    SourcePressureMarginInt n k (r + j + 1) -
        SourcePressureMarginInt n k (r + j) =
      SourcePressureNetDropInt n k r j
```

```lean
theorem sourcePressureMargin_next_eq_current_add_netDrop
    (n : OddNat) (k r j : ℕ) :
    SourcePressureMarginInt n k (r + j + 1) =
      SourcePressureMarginInt n k (r + j) +
        SourcePressureNetDropInt n k r j
```

The actual index shape is:

```text
r + j + 1
```

not the alternative spelling:

```text
r + (j + 1)
```

The Beam-facing wrapper therefore preserves the exact existing local theorem
shape instead of forcing an index rewrite.

## True Beam Facts

Implemented:

```lean
theorem sourcePressureMargin_next_eq_current_add_netDrop_of_addressedDepthTarget
```

This reads the local transition equation at a depth already selected by an
addressed Beam target.

Implemented:

```lean
theorem exists_sourcePressureMargin_transition_of_beamSeed
```

This proves:

```text
SourcePressureBeamSeed L
  -> exists j,
       SourcePressureBeamAddressedDepthTarget L j
       and
       local margin transition equation at j
```

## Experimental Lemma Table

| experiment | theorem | status | note |
| --- | --- | --- | --- |
| Step 1 | `sourcePressureMarginStepDiff_eq` shape | inspected | uses `r + j + 1` |
| Step 1 | `sourcePressureMargin_next_eq_current_add_netDrop` shape | inspected | uses `SourcePressureNetDropInt n k r j` |
| T1 | `sourcePressureMargin_next_eq_current_add_netDrop_of_addressedDepthTarget` | passed | addressed local transition wrapper |
| T2 | `exists_sourcePressureMargin_transition_of_beamSeed` | passed | seed gives existential addressed transition |
| G1 | `SourcePressureBeamSeed L -> transition equation at arbitrary j` | nuanced | equation is globally algebraic, but not seed-addressed |

## False Beam / Gap

The transition equation itself is a global local algebra identity from
`PressureDecay`; it does not need a seed.  Therefore the overclaim is not false
as a raw equation.

The actual Gap is more precise:

```text
SourcePressureBeamSeed L
  -> SourcePressureBeamAddressedDepthTarget L j
```

for arbitrary external `j`.

The seed does not select arbitrary external depths.  It selects only an
existential addressed depth from its witness list.

No negated theorem was added in this checkpoint.

## Local Reading, Not Propagation

The new wrapper is only a local transition reading:

```text
AddressedDepthTarget at j
  -> margin_next(j) = margin_current(j) + netDrop(j)
```

The addressed target hypothesis is not needed for the algebraic identity
itself.  It is included to keep the API tied to the Beam-selected depth.

No theorem was added for:

- time/orbit propagation;
- arbitrary target transport;
- arbitrary margin positivity;
- canonical target selection;
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

The next safe surface is sign reading at the addressed transition:

```text
AddressedDepthTarget
  -> margin_pos at j
  -> margin_next = margin_current + netDrop
```

From here, the natural split is:

```text
True Beam:
  conditions under which next margin remains positive

False Beam:
  conditions under which next margin is nonpositive
```

That should still be stated locally at the addressed depth.  It should not be
promoted to time/orbit propagation until there is a separate theorem connecting
adjacent pressure-depth edges into a valid Beam path.

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

