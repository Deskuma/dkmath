# Collatz First Failed Depth Sequence - Checkpoint 129

Checkpoint 129 closes the small Route A list-API gap for the first-failed-depth
profile.

Checkpoint 128 introduced:

```lean
orbitWindowFirstFailedPow2DepthSeq
orbitWindowFirstFailedPow2DepthSeq_length
orbitWindowFirstFailedPow2Depth_eq_height_add_one
```

Checkpoint 129 adds the same index and prefix API already available for the
height and residual-shape profiles.

## New Theorems

```lean
orbitWindowFirstFailedPow2DepthSeq_get?_eq_some
orbitWindowFirstFailedPow2DepthSeq_get?_eq_some_height_add_one
orbitWindowFirstFailedPow2DepthSeq_take_length
orbitWindowFirstFailedPow2DepthSeq_take_get?_eq_some
orbitWindowFirstFailedPow2DepthSeq_take_get?_eq_some_height_add_one
orbitWindow_threeProfiles_get?_eq_some
```

The main operational reading is:

```text
failed_i = height_i + 1
```

and this can now be recovered through direct list indexing and prefix indexing.

## Three Aligned Time Profiles

The finite time window now has three aligned profiles:

```text
orbitWindowHeightSeq
orbitWindowResidualShapeSeq
orbitWindowFirstFailedPow2DepthSeq
```

The theorem

```lean
orbitWindow_threeProfiles_get?_eq_some
```

packages the simultaneous `get?` reading at an in-window time index.

This is useful because later work can introduce a `ShapePressureGrid` without
rebuilding the one-dimensional time-profile API.

## Axis Warning

The checkpoint still keeps two axes separate.

```text
time index i:
  height_i
  residual_i
  first_failed_i

pressure depth index j:
  margin(j)
  frontier(j)
  local island(j)
```

The theorem surface intentionally does not collapse `i` and `j`.  A later
two-dimensional structure should expose both axes explicitly.

## Suggested Next Work

Route A is now essentially closed for the current three time profiles.

The next useful direction is Route B:

```text
pressure sign-pattern scan
  positive depths
  positive blocks
  local islands
  frontier depth
  sign-change-up positions
```

The scan should also carry:

```text
height_seq
residual_shape_seq
first_failed_depth_seq
residual_mod_8/16/32
```

so the next Lean predicates are based on observed time x depth correlations,
not on a guessed one-dimensional collapse.
