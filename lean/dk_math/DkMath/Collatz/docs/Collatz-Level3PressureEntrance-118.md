# Collatz Level-3 And Pressure Entrance 118

Checkpoint 118 has two roles.

First, it extends the delayed-reservoir tower to level `3`.
Second, it adds the first bridge from one-depth range pressure into the local
depth-`2` delayed-reservoir entrance.

## Level-3 Tower Extension

Checkpoint 117 fixed level `2`:

```text
tail 15 mod 16
  -> next tail 7 mod 16 + next tail 15 mod 16
```

Checkpoint 118 adds level `3`:

```text
tail 31 mod 32
  -> next tail 15 mod 32 + next tail 31 mod 32
```

New shifted-tail counts:

```lean
orbitWindowResidueCountMod64EqThirtyOneTail
orbitWindowResidueCountMod64EqSixtyThreeTail
```

Static split:

```lean
tailResidueCountMod32EqThirtyOne_split_mod64_thirtyOne_sixtyThree
```

Reading:

```text
tail 31 mod 32
  = tail 31 mod 64
    + tail 63 mod 64
```

Recursion edge:

```lean
tailMod32ThirtyOne_le_nextTailMod32Fifteen_add_nextTailMod32ThirtyOne
```

Reading:

```text
tail 31 mod 32
  -> next tail 15 mod 32
     or
     next tail 31 mod 32
```

## Level Aliases

New aliases:

```lean
TailRemainderLevel3
TailFallingLevel3
```

New alias theorems:

```lean
tailRemainderLevel2_static_split
tailRemainderLevel2_step_grammar
```

They say:

```text
level 2 remainder
  = level 3 falling + level 3 remainder

level 2 remainder
  -> next level 2 falling + next level 2 remainder
```

The target of the step theorem remains level `2` because the next shifted-tail
window re-enters the visible `15 mod 32 / 31 mod 32` split.

## Range Pressure Entrance

Checkpoint 117 added a local pressure entrance:

```lean
sourceContinuationMass_depth_two_pos_of_pressure_depth_two
```

Checkpoint 118 adds the one-depth range-pressure extraction:

```lean
sourcePressureDepthTwo_of_pressureOnRange_two_one
sourceContinuationMass_depth_two_pos_of_pressureOnRange_two_one
```

This gives the caller route:

```text
SourceContinuationPressureOnRange n k 2 1
  -> local MoreThanHalf pressure at depth 2
  -> positive continuation mass at depth 2
```

This still does not prove that a long pressure-heavy range feeds enough mass
into the tower.  It closes the first small interface from the range vocabulary
to the local tower entrance.

## Current Tower

The concrete tower now reaches:

```text
level 1:
  3 mod 8 falls
  7 mod 8 remains

level 2:
  7 mod 16 falls
  15 mod 16 remains

level 3:
  15 mod 32 falls
  31 mod 32 remains
```

The next likely concrete extension is:

```text
level 4:
  31 mod 64 falls
  63 mod 64 remains
```

The next pressure-side extension is:

```text
SourceContinuationPressureOnRange n k 2 len
  -> extract useful local pressure at one or more depths
  -> enter delayed-reservoir budgets
```
