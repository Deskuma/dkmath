# Collatz Mixed Depth-Mode Distribution 108

## Purpose

Checkpoint 107 introduced pressure depth counts:

```lean
sourceContinuationPressureDepthCount
tailContinuationPressureDepthCount
```

Checkpoint 108 adds the complementary controlled counts and proves that every
depth in a finite range is counted by exactly one of the two modes:

```text
controlled
pressure
```

## Controlled Counts

Source controlled depths:

```lean
sourceContinuationControlledDepthCount
```

Tail controlled depths:

```lean
tailContinuationControlledDepthCount
```

These count depths where continuation is at most half of the relevant
retention mass:

```text
AtMostHalf continuation retention
```

The pressure counts from checkpoint 107 count the strict complementary mode:

```text
MoreThanHalf continuation retention
```

## Basic Bounds

Checkpoint 108 records that all four depth-mode counts are bounded by the
range length:

```lean
sourceContinuationPressureDepthCount_le_len
tailContinuationPressureDepthCount_le_len
sourceContinuationControlledDepthCount_le_len
tailContinuationControlledDepthCount_le_len
```

These are finite `List.countP` bounds over `List.range len`.

## Main Partition

Source depth-mode distribution:

```lean
sourceContinuationControlledDepthCount_add_pressureDepthCount_eq_len
```

Tail depth-mode distribution:

```lean
tailContinuationControlledDepthCount_add_pressureDepthCount_eq_len
```

The reading is:

```text
controlled depth count + pressure depth count = len
```

This is the depth-mode counterpart of the checkpoint 100 residue distribution.

## Proof Shape

The proof is by induction on `len`.

At the final depth of the successor step, the local dichotomy is:

```lean
atMostHalf_or_moreThanHalf
```

The two branches are exclusive because:

```text
AtMostHalf count total     means 2 * count <= total
MoreThanHalf count total   means total < 2 * count
```

The final singleton therefore contributes exactly one count to either the
controlled side or the pressure side.

## Mathematical Reading

The Collatz/Petal bridge now has two finite distribution layers:

```text
checkpoint 100:
  orbit-window labels distribute across residue cells

checkpoint 108:
  depth positions distribute across controlled/pressure modes
```

This does not assert that pressure is rare.  It gives a precise finite
accounting identity that future obstruction arguments can use.

## Next Candidate

The next natural step is to reuse the existing finite-ratio vocabulary on the
depth-mode counts:

```lean
AtMostHalf (sourceContinuationPressureDepthCount n k r len) len
MoreThanHalf (sourceContinuationPressureDepthCount n k r len) len
```

This would allow statements such as:

```text
at most half of the depth range is pressure
```

or:

```text
more than half of the depth range is pressure
```

still entirely as `Nat` inequalities.
