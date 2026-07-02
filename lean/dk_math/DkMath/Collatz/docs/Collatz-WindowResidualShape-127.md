# Collatz Window Residual Shape - Checkpoint 127

Checkpoint 127 lifts the pointwise residual-shape bridge to finite orbit
windows.

Checkpoint 126 proved:

```text
RawGnomonResidualShape n.val = (T n).val
```

Checkpoint 127 turns this into a window statement:

```text
the residual shape extracted at index i is the odd label at index i+1
```

## New Window Vocabulary

```lean
orbitWindowResidualShape
orbitWindowResidualShapeSeq
orbitWindowFirstFailedPow2Depth
```

The definitions are window-level lifts:

```text
orbitWindowResidualShape n i
  = RawGnomonResidualShape (oddOrbitLabel n i)

orbitWindowResidualShapeSeq n k
  = map orbitWindowResidualShape over List.range k

orbitWindowFirstFailedPow2Depth n i
  = FirstFailedPow2Depth (oddOrbitLabel n i)
```

These definitions deliberately live in `PetalBridge`, because they depend on
the finite window label `oddOrbitLabel`.  The low-level arithmetic remains in
`GnomonEvaluation`.

## Main Theorem

```lean
orbitWindowResidualShape_eq_oddOrbitLabel_succ
```

Meaning:

```text
orbitWindowResidualShape n i = oddOrbitLabel n (i + 1)
```

This is the core checkpoint-127 result.  The finite orbit window is now a chain
of residual-shape extractions:

```text
label_i
  -> raw gnomon step
  -> power-of-two alignment height
  -> residual shape
  -> label_{i+1}
```

## Sequence Bridge

```lean
orbitWindowResidualShapeSeq_eq_shifted_oddOrbitLabels
```

Meaning:

```text
residual shape profile over k indices
  = shifted odd-label profile over k indices
```

This will be the natural starting point for later finite statistics on
residual shapes.

## Window Factorization

```lean
orbitWindow_rawGnomonStep_factor
```

At each window index:

```text
RawGnomonStep (oddOrbitLabel n i)
  = 2 ^ orbitWindowHeight n i * orbitWindowResidualShape n i
```

This is the finite-window version of the pointwise factorization from
checkpoint 126.

## First Failed Depth

```lean
orbitWindow_firstFailed_remainder_ne_zero
```

At each observed odd label, the first failed power-of-two depth has nonzero
remainder.  The window therefore carries both:

```text
alignment depth:
  orbitWindowHeight n i

first failed depth:
  orbitWindowFirstFailedPow2Depth n i
```

## Pressure Sign Pattern Starter

Checkpoint 127 also adds the first thin sign-pattern predicates:

```lean
SourcePressureSignChangeUp
sourcePressureSignChangeUp_of_frontier_pos
SourcePressureLocalIsland
```

These do not prove any pressure-prefix theorem.  They simply name local
features of the margin profile:

```text
sign change up:
  margin(j) <= 0 and margin(j+1) > 0

local island:
  depth j is positive, but j-1 and j+1 are not selected
```

The next pressure checkpoint should be driven by numerical classification of
margin profiles, not by an assumed monotonicity law.

## Next Work

Two natural next directions remain.

### Residual Shape Statistics

Build counts or profiles over:

```text
orbitWindowResidualShapeSeq
orbitWindowFirstFailedPow2Depth
```

Possible names:

```lean
orbitWindowResidualShapeSeq_length
orbitWindowResidualShapeSeq_get?_eq_some
orbitWindowFirstFailedDepthSeq
```

### Pressure Pattern Classification

Use Python summary scans to classify:

```text
first_frontier_depth
frontier_margin
positive_depths
positive_blocks
local_islands
first_failure_pair
margin_jump
retention_drop
continuation_drop
```

Then add only the predicates that survive as useful theorem interfaces.
