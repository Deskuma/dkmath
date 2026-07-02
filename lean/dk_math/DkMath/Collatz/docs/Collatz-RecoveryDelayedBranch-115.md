# Collatz Recovery Delayed Branch 115

Checkpoint 115 revisits the extra-peeling question after checkpoint 114.

Checkpoint 114 ruled out the tempting shortcut:

```text
source continuation at parent depth 2
  -> shifted-tail height >= 2
```

The actual result was weaker and more precise:

```text
source continuation at parent depth 2
  -> shifted-tail exact height 1
```

Checkpoint 115 asks where the missing extra peeling goes.

## Main Correction

The recovery channel has two different low-depth readings.

At parent depth `1`, shifted-tail recovery is immediate extra peeling:

```lean
tailRecoveryMass_depth_one_eq_tailResidueCount_mod4_eq_one
tailRecoveryMass_depth_one_le_heightCountGe_two
```

This is the ordinary `1 mod 4` tail cell, which is equivalent to
`height >= 2`.

At parent depth `2`, shifted-tail recovery is not `1 mod 4`.  It is:

```lean
tailRecoveryMass_depth_two_eq_tailResidueCount_mod8_eq_three
tailRecoveryMass_depth_two_le_tailResidueCount_mod8_eq_three
```

So the parent-depth-2 recovery channel is the `3 mod 8` delayed-peeling color
inside the exact-height-one reservoir.

## Exact-Height-One Reservoir

The shifted-tail exact-height-one reservoir is now split into two visible
colors:

```lean
orbitWindowResidueCountMod8EqThreeTail
orbitWindowResidueCountMod8EqSevenTail
tailHeightCountEq_one_split_mod8_three_seven
```

Conceptually:

```text
tail exact height 1
  = tail 3 mod 8
    + tail 7 mod 8
```

The two colors have different dynamical meanings:

```text
3 mod 8
  delayed-peeling color

7 mod 8
  continuing color
```

## Delayed Peeling

The `3 mod 8` tail color contributes to `height >= 2` one step later:

```lean
tailMod8Three_le_nextTailHeightCountGe_two
```

The accumulated-height form is:

```lean
tailResidueCountMod8EqThree_delayed_drift
```

This says that the shifted-tail `3 mod 8` count supplies an extra layer in the
next accumulated `sumS` window.

## Source-Side Hooks

Checkpoint 115 also provides two source-facing bridges.

Source recovery at parent depth `3` lands in the delayed `3 mod 8` tail color:

```lean
sourceRecoveryMass_depth_three_le_tailResidueCount_mod8_eq_three
```

Source continuation at parent depth `2` lands in the exact-height-one reservoir,
and the reservoir splits into the delayed and continuing colors:

```lean
sourceContinuationMass_depth_two_le_tailMod8Three_add_tailMod8Seven
```

## Current Working Model

The model has shifted from immediate peeling to delayed reservoir flow.

Old expectation:

```text
pressure-heavy channel
  -> immediate extra height
```

Current theorem-supported reading:

```text
pressure or recovery channel
  -> exact-height-one reservoir
  -> 3 mod 8 / 7 mod 8 color split
  -> 3 mod 8 supplies extra peeling one step later
```

This is still a finite, natural-valued observation.  It does not prove global
Collatz convergence.  It gives a sharper local channel grammar for future
finite-window arguments.

## Next Targets

The next useful questions are:

```text
1. Can the 7 mod 8 continuing color be split at mod 16?

2. Can repeated continuing colors be organized as a finite delayed-reservoir
   tower?

3. Can a pressure-heavy depth range force enough delayed 3 mod 8 mass to
   improve the global sumS lower bound?
```

The likely next Lean layer is a reusable recursive color split:

```text
tail exact height 1 at resolution 2^r
  -> delayed-peeling color
  -> continuing color
```

This should be attempted only after the low-depth `3 mod 8` / `7 mod 8`
surface remains stable under review.
