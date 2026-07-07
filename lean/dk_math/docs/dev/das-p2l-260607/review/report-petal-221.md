# report-petal-221

## Checkpoint

`petal-221`

## Goal

Investigate whether the Beam layer should introduce a separate crossing-edge
target vocabulary for interval-pulse left edges.

cp220 showed:

```text
right edge:
  witness center
  positive Beam depth target

left edge:
  nonpositive boundary before entering the positive run
  not a Beam depth target
```

Therefore the question was whether `SourcePressureSignChangeUp` is enough, or
whether the Beam layer needs a distinct Beam-facing crossing-edge vocabulary.

## Decision

Added a Beam-facing crossing-edge target API.

The definition is intentionally thin:

```lean
def SourcePressureBeamCrossingEdgeTarget
    (n : OddNat) (k r j : Nat) : Prop :=
  SourcePressureSignChangeUp n k r j
```

This is not a new mathematical predicate.  It is a Beam-facing vocabulary
split that prevents left crossing edges from being forced into
`SourcePressureBeamDepthTarget`.

## Why this is useful

`SourcePressureBeamDepthTarget n k r j` means:

```lean
0 < SourcePressureMarginInt n k (r + j)
```

It is a positive current-depth target.

`SourcePressureBeamCrossingEdgeTarget n k r j` means:

```lean
SourcePressureMarginInt n k (r + j) ≤ 0
0 < SourcePressureMarginInt n k (r + j + 1)
```

It is an edge target from a nonpositive boundary into a positive next depth.

This distinction matters because interval-pulse left edges are crossing edges,
not positive depth targets.

## Lean changes

File changed:

```text
lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean
```

Added:

```lean
def SourcePressureBeamCrossingEdgeTarget

theorem sourcePressureBeamCrossingEdgeTarget_current_nonpos
theorem sourcePressureBeamCrossingEdgeTarget_next_pos
theorem not_sourcePressureBeamDepthTarget_of_crossingEdgeTarget

theorem sourcePressureMargin_next_pos_iff_massBalanceLeft_lt_right_edge
theorem sourcePressureMargin_next_nonpos_iff_massBalanceRight_le_left_edge

theorem sourcePressureBeamMassBalanceLeft_lt_right_of_crossingEdgeTarget
theorem sourcePressureBeamCrossingEdgeTarget_of_intervalPulse_left
theorem sourcePressureBeamMassBalanceLeft_lt_right_of_intervalPulse_left_crossing
theorem sourcePressureBeamCrossingEdgeTarget_of_localIslandWitness_intervalPulse_left
theorem sourcePressureBeamMassBalanceLeft_lt_right_of_localIslandWitness_intervalPulse_left
```

## Main result

The left-edge True Beam route is now expressed without pretending that the left
edge is a positive depth target:

```text
interval-pulse left edge
  -> SourcePressureBeamCrossingEdgeTarget
  -> next margin positive
  -> left < right mass-balance comparison
```

The key theorem is:

```lean
sourcePressureBeamMassBalanceLeft_lt_right_of_intervalPulse_left_crossing
```

and the witness-derived version is:

```lean
sourcePressureBeamMassBalanceLeft_lt_right_of_localIslandWitness_intervalPulse_left
```

## Important correction

The earlier addressed-target mass-balance classifiers are still valid, but
their `SourcePressureBeamAddressedDepthTarget` hypothesis is not necessary for
pure edge algebra.

For crossing-edge work, this checkpoint added edge-local algebraic classifiers:

```lean
sourcePressureMargin_next_pos_iff_massBalanceLeft_lt_right_edge
sourcePressureMargin_next_nonpos_iff_massBalanceRight_le_left_edge
```

These do not require positive current margin.

This is the right API for crossing edges.

## Classification

### True Beam

Crossing-edge target gives:

```lean
SourcePressureBeamMassBalanceLeftInt n k r j <
  SourcePressureBeamMassBalanceRightInt n k r j
```

because it supplies positive next margin.

### Boundary

No equality-specific crossing-boundary theorem was added.  The boundary layer
still belongs to the zero next-margin / mass-balance equality API.

### False Beam

The false/boundary edge-local classifier was added as:

```lean
sourcePressureMargin_next_nonpos_iff_massBalanceRight_le_left_edge
```

but no new downward-crossing target was introduced in this checkpoint.

### Gap

The current crossing-edge target only covers upward crossings:

```lean
SourcePressureSignChangeUp
```

A future symmetric API could introduce:

```lean
SourcePressureBeamFallingEdgeTarget
```

as a Beam-facing name for `SourcePressureSignChangeDown`, but this checkpoint
did not need it because the right-edge route already works through positive
depth targets and existing downward sign-change wrappers.

## Guardrails

The new API is vocabulary and exact-edge algebra only.

It does not assert:

- arbitrary target transport;
- global interval coverage;
- aggregation over witness families;
- canonical target selection;
- overlap repair;
- Collatz convergence.

## Verification

Commands run:

```bash
lake build DkMath.Collatz.PetalBridge.PressureBeam
lake build DkMath.Collatz.PetalBridge
rg -n "\bsorry\b|admit" \
  lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean \
  lean/dk_math/DkMath/Collatz/PetalBridge/PressureDecay.lean \
  lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean
git diff --check
```

Results:

- `lake build DkMath.Collatz.PetalBridge.PressureBeam`: passed.
- `lake build DkMath.Collatz.PetalBridge`: passed.
- no-sorry grep over inspected files: no matches.
- `git diff --check`: passed.

Known unrelated warning still appears during builds:

```text
DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:152:6:
declaration uses `sorry`
```

## Next candidate

The natural next step is to decide whether a symmetric falling-edge vocabulary
is worth adding:

```lean
def SourcePressureBeamFallingEdgeTarget
    (n : OddNat) (k r j : Nat) : Prop :=
  SourcePressureSignChangeDown n k r j
```

This would make the Beam edge vocabulary symmetric:

```text
CrossingEdgeTarget: nonpositive -> positive
FallingEdgeTarget:  positive -> nonpositive
DepthTarget:        positive current depth
```

If added, it should stay exact-edge and should not replace the existing
right-edge positive-depth route.
