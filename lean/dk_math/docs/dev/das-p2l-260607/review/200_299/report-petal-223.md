# Report: petal-223

## Checkpoint

`petal-223` asked whether the new Beam edge vocabulary should be packaged into
a compact local pulse-shape API.

The implemented answer is yes, but only as thin theorem packaging.  No new
predicate was added.

## What was inspected

The relevant API already existed after cp221 and cp222:

- `SourcePressureBeamCrossingEdgeTarget`
  records an entry edge, `nonpositive -> positive`.
- `SourcePressureBeamDepthTarget`
  records a positive current depth.
- `SourcePressureBeamFallingEdgeTarget`
  records an exit edge, `positive -> nonpositive`.
- `sourcePressureBeamCrossingEdgeTarget_of_intervalPulse_left`
  gives the left edge of an interval pulse.
- `sourcePressureBeamFallingEdgeTarget_of_intervalPulse_right`
  gives the right edge of an interval pulse.
- `sourcePressureBeamAddressedDepthTarget_of_localIslandWitness_intervalPulse_right`
  gives the singleton witness depth target, but this one is list-relative and
  therefore requires `W ∈ L`.

This was enough to add compact local packaging without introducing a heavier
`PulseShape` predicate.

## Implemented theorem surface

Added in `DkMath.Collatz.PetalBridge.PressureBeam`:

```lean
sourcePressureBeamPulse_edges_of_intervalPulseAddress
sourcePressureBeamPulse_massBalance_edges_of_intervalPulseAddress
sourcePressureBeamPulse_witness_singleton_shape
sourcePressureBeamPulse_witness_singleton_massBalance_edges
```

The interval-pulse edge theorem packages the exact indices:

```text
left edge  = A.start - 1
right edge = A.start + A.len - 1
```

The witness singleton theorem packages:

```text
left edge:
  CrossingEdgeTarget

right / center edge of the singleton pulse:
  SourcePressureBeamAddressedDepthTarget L ...
  FallingEdgeTarget
```

The addressed-depth component requires `W ∈ L` because it is a carrier relative
to a witness list.  The crossing and falling edge targets do not require list
membership, because they are intrinsic sign-change facts of the generated pulse.

## Classification

- True Beam:
  The entry edge gives `left < right`.

- DepthTarget:
  The singleton local-island witness gives an addressed depth target at the
  generated pulse's right/center edge, under `W ∈ L`.

- Falling / Boundary:
  The exit edge gives `right <= left`, i.e. the false-or-boundary comparison.

- Gap:
  No interior coverage theorem was added.  No family aggregation, canonical
  target selection, overlap repair, propagation, or Collatz convergence is
  claimed.

## Verification

Completed:

```text
lake build DkMath.Collatz.PetalBridge.PressureBeam
lake build DkMath.Collatz.PetalBridge
rg -n "\bsorry\b|admit" over PressureBeam / PressureDecay / PressureFrontier
git diff --check
```

The inspected pressure files have no new `sorry` / `admit` matches.

`PressureBeam.lean` is now 1821 lines, still below the 2000-line split
criterion.

Known unrelated project warning remains:

```text
DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:152:6:
declaration uses 'sorry'
```

## Next inference

The entry/interior/exit vocabulary is now available as local pulse packaging.
The next safe step is to consume these packaged theorems from a downstream
diagnostic layer, or to add one more local theorem that destructs the packaged
shape into a named false/boundary observation.  The unsafe step would be to
upgrade this into coverage over all intervals or all witness families; that
should remain out of scope until exact membership and non-overlap facts exist.
