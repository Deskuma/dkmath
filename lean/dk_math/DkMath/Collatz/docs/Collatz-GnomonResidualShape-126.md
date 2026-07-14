# Collatz Gnomon Residual Shape - Checkpoint 126

Checkpoint 126 closes the first Route A bridge from the new gnomon vocabulary
back to the existing accelerated Collatz map.

Checkpoint 125 introduced:

```text
RawGnomonStep n = n + (2n+1)
RawGnomonHeight n = v2 (RawGnomonStep n)
RawGnomonResidualShape n = RawGnomonStep n / 2^height
```

Checkpoint 126 proves that this residual shape is exactly the value already
computed by the accelerated odd map `T`.

## Main Bridge

```lean
rawGnomonResidualShape_eq_T_val
```

Meaning:

```text
RawGnomonResidualShape n.val = (T n).val
```

This is the important closure point.  The gnomon vocabulary is no longer only
an explanation of the old Collatz step.  It is formally the same residual odd
state used by the existing accelerated dynamics.

## Consequences

Oddness is inherited from `T`:

```lean
rawGnomonResidualShape_odd
```

The raw gnomon step decomposes into alignment height times residual shape:

```lean
rawGnomonStep_eq_pow_height_mul_residualShape
```

The alignment height is maximal:

```lean
two_pow_succ_rawGnomonHeight_not_dvd
```

Therefore the first failed depth has nonzero remainder:

```lean
rawGnomonRemainderAtDepth_firstFailed_ne_zero
```

Together with the checkpoint-125 theorem

```lean
rawGnomonRemainderAtDepth_eq_zero_of_le_height
```

the boundary is now exact:

```text
j <= height:
  RawGnomonRemainderAtDepth n j = 0

j = height + 1:
  RawGnomonRemainderAtDepth n j != 0
```

## Window Lift

`PetalBridge` also receives the pointwise lift:

```lean
orbitWindowHeight_eq_rawGnomonHeight_oddOrbitLabel
```

Meaning:

```text
orbitWindowHeight n i
  = RawGnomonHeight (oddOrbitLabel n i)
```

This keeps `PetalBridge` as a finite observation surface while allowing every
height observation to be read through the gnomon/alignment vocabulary.

## Pressure Frontier

Route B starts with a small, safe predicate:

```lean
SourcePressureFrontier
sourcePressureFrontier_iff_margin
sourcePressurePrefixFailure_of_frontier_pos
```

This is not a pressure-prefix theorem.

It says:

```text
frontier = first positive margin
```

If the frontier is at a positive depth, it immediately yields a
`SourcePressurePrefixFailure` from depth `0` to that frontier depth.

The distinction is important:

```text
frontier:
  first positive margin

prefix:
  all depths up to a bound are positive

island:
  positive margin appears without prefix behavior
```

Checkpoint 126 only fixes the frontier and its margin reading.  It does not
claim that selected depths are prefix-shaped.

## Next Work

The next Route A extension is to expose residual-shape window profiles:

```text
orbitWindowResidualShape
orbitWindowResidualShapeSeq
```

The next Route B extension is to classify pressure sign patterns:

```text
SourcePressureLocalIsland
SourcePressureIsland
first failure pair
margin jump
retention drop
continuation drop
```

The recommended next checkpoint depends on whether the reviewer wants more
shape dynamics or more pressure-profile classification.

## Checkpoint 127 Follow-up

Checkpoint 127 takes the recommended shape-dynamics route.

New window names:

```lean
orbitWindowResidualShape
orbitWindowResidualShapeSeq
orbitWindowFirstFailedPow2Depth
```

Main theorem:

```lean
orbitWindowResidualShape_eq_oddOrbitLabel_succ
```

Meaning:

```text
residual shape extracted at window index i
  = odd label at window index i+1
```

This lifts the pointwise residual-shape bridge into finite orbit windows.  See:

```text
Collatz-WindowResidualShape-127.md
```
