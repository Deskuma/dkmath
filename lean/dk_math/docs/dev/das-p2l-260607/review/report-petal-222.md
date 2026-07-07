# Report: petal-222

## Checkpoint

`petal-222` asked whether the Beam layer should introduce a symmetric
falling-edge vocabulary for the right edge of a local pressure island.

The implemented answer is yes:

```lean
def SourcePressureBeamFallingEdgeTarget
    (n : OddNat) (k r j : Nat) : Prop :=
  SourcePressureSignChangeDown n k r j
```

This is intentionally a thin Beam-facing name.  It does not add propagation,
coverage, canonical target selection, overlap repair, or any Collatz convergence
claim.

## What was inspected

- `SourcePressureSignChangeDown` already stores the two facts needed for an exit
  edge:
  - the current margin is positive;
  - the next margin is nonpositive.
- cp221 had already supplied the edge-local classifier:
  - positive next margin iff left mass balance is strictly larger;
  - nonpositive next margin iff right mass balance is at most the left mass
    balance.
- The interval-pulse right edge already gives `SourcePressureSignChangeDown`.
- The local-island singleton witness route already exposes the same interval
  pulse.

Therefore the new vocabulary can remove unnecessary dependence on
`SourcePressureBeamAddressedDepthTarget` for the right-edge false/boundary
mass-balance comparison.

## Implemented theorem surface

Added in `DkMath.Collatz.PetalBridge.PressureBeam`:

```lean
SourcePressureBeamFallingEdgeTarget
sourcePressureBeamFallingEdgeTarget_current_pos
sourcePressureBeamFallingEdgeTarget_next_nonpos
sourcePressureBeamDepthTarget_of_fallingEdgeTarget
not_crossingEdgeTarget_and_fallingEdgeTarget
sourcePressureBeamMassBalanceRight_le_left_of_fallingEdgeTarget
sourcePressureBeamFallingEdgeTarget_of_intervalPulse_right
sourcePressureBeamMassBalanceRight_le_left_of_intervalPulse_right_falling
sourcePressureBeamFallingEdgeTarget_of_localIslandWitness_intervalPulse_right
sourcePressureBeamMassBalanceRight_le_left_of_localIslandWitness_intervalPulse_right_falling
```

The important operational bridge is:

```lean
SourcePressureBeamFallingEdgeTarget n k r j
  -> SourcePressureBeamMassBalanceRightInt n k r j
       <= SourcePressureBeamMassBalanceLeftInt n k r j
```

This now follows directly from the falling edge and the edge-local classifier.

## Complementarity

The three Beam target names now form a small local-island vocabulary:

```text
CrossingEdgeTarget:
  nonpositive -> positive
  entry edge

DepthTarget:
  positive current depth
  interior / active depth

FallingEdgeTarget:
  positive -> nonpositive
  exit edge
```

`not_crossingEdgeTarget_and_fallingEdgeTarget` records that the same edge cannot
be both an entry edge and an exit edge, because the next margin cannot be both
positive and nonpositive.

## Classification

- True Beam:
  The entry-side route remains cp221's `CrossingEdgeTarget`, which gives the
  strict left/right classifier.

- Boundary / False Beam:
  `FallingEdgeTarget` gives `right <= left` at the exact exit edge.  This covers
  the false-or-boundary comparison without requiring an addressed-depth target.

- Boundary:
  Equality remains handled by the existing mass-balance equality vocabulary.
  This checkpoint does not add a new equality-specific falling-edge theorem.

- Gap:
  No claim is made about all edges in an interval, propagation past an edge, or
  global coverage of every source.  Strict false would require a strictly
  negative next-margin hypothesis, not merely nonpositivity.

## Verification

Completed:

```text
lake build DkMath.Collatz.PetalBridge.PressureBeam
lake build DkMath.Collatz.PetalBridge
rg -n "\bsorry\b|admit" over PressureBeam / PressureDecay / PressureFrontier
git diff --check
```

The inspected pressure files have no new `sorry` / `admit` matches.

`PressureBeam.lean` is now 1724 lines, still below the 2000-line split criterion.

Known unrelated project warning remains:

```text
DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:152:6:
declaration uses 'sorry'
```

## Next inference

The next natural small step is not global coverage.  A safer direction is a
local pulse packaging theorem:

```text
interval pulse
  -> crossing target at the left edge
  -> positive depth inside the addressed island
  -> falling target at the right edge
```

This would package the entry/interior/exit vocabulary without claiming that such
pulses cover all pressure behavior.
