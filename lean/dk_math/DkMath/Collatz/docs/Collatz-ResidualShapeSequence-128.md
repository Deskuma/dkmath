# Collatz Residual Shape Sequence - Checkpoint 128

Checkpoint 128 makes the residual-shape window profile usable as a list API.

Checkpoint 127 proved:

```text
orbitWindowResidualShape n i = oddOrbitLabel n (i + 1)
```

Checkpoint 128 adds the same ergonomic helpers that already exist for the
height profile.

## Residual Shape Sequence API

New theorems:

```lean
orbitWindowResidualShapeSeq_length
orbitWindowResidualShapeSeq_get?_eq_some
orbitWindowResidualShapeSeq_get?_eq_some_shifted_label
orbitWindowResidualShapeSeq_take_length
orbitWindowResidualShapeSeq_take_get?_eq_some
```

These make the residual-shape sequence readable by index and by prefix.

The shifted-label get theorem is especially important:

```text
(orbitWindowResidualShapeSeq n k)[i]?
  = some (oddOrbitLabel n (i + 1))
```

whenever `i < k`.

## First Failed Depth Sequence

New definition:

```lean
orbitWindowFirstFailedPow2DepthSeq
```

New theorems:

```lean
orbitWindowFirstFailedPow2DepthSeq_length
orbitWindowFirstFailedPow2Depth_eq_height_add_one
```

This records that the first failed depth in the window is exactly one more than
the observed height:

```text
orbitWindowFirstFailedPow2Depth n i = orbitWindowHeight n i + 1
```

## Pressure Local Island

Checkpoint 127 introduced:

```lean
SourcePressureLocalIsland
```

Checkpoint 128 adds:

```lean
sourcePressureLocalIsland_iff_margin
```

The meaning is:

```text
local island at depth j
  <-> j > 0
      margin(j) > 0
      margin(j-1) <= 0
      margin(j+1) <= 0
```

This remains a sign-pattern observation.  It is not a pressure-prefix theorem.

## Axis Warning

There are now two distinct axes.

```text
time index i:
  label_i
  height_i
  residual_i = label_{i+1}
  first_failed_depth_i

depth index j:
  pressure margin at depth j
  frontier
  sign-change
  local island
```

Do not identify these axes.

The next conceptual object is a two-dimensional observation grid:

```text
ShapePressureGrid:
  time i x depth j
```

The current checkpoint does not create that grid.  It prepares the two
one-dimensional surfaces so the grid can be introduced deliberately later.

## Next Work

Two routes are reasonable.

### Route A: residual shape profile extras

Add more list tools if needed:

```lean
orbitWindowFirstFailedPow2DepthSeq_get?_eq_some
orbitWindowFirstFailedPow2DepthSeq_take_get?_eq_some
orbitWindowResidualShapeSeq_eq_shifted_oddOrbitLabels_take
```

Checkpoint 129 implements the first-failed-depth list helpers and adds
`orbitWindow_threeProfiles_get?_eq_some`, so the remaining residual-shape extra
is only needed if a later proof specifically wants a prefix version of shifted
labels.

### Route B: pressure sign-pattern statistics

Use Python summary scans before adding heavier Lean names:

```text
positive_depths
positive_blocks
local_islands
sign_change_up_positions
first_frontier_depth
margin_jump
retention_drop
continuation_drop
```

The next Lean theorem on the pressure side should only encode a sign-pattern
relationship that appears useful in those summaries.
