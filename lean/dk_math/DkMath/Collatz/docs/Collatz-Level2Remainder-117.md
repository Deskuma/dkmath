# Collatz Level-2 Remainder 117

Checkpoint 117 extends the delayed-reservoir tower from level `1` to level `2`.

Checkpoint 116 fixed:

```text
tail 7 mod 8
  -> next tail 3 mod 8 + next tail 7 mod 8
```

Checkpoint 117 adds the next concrete remainder:

```text
tail 15 mod 16
  -> next tail 7 mod 16 + next tail 15 mod 16
```

## Level Names

The first explicit level aliases are:

```lean
TailRemainderLevel0
TailRemainderLevel1
TailRemainderLevel2
TailFallingLevel1
TailFallingLevel2
```

They read:

```text
TailRemainderLevel0:
  tail exact height 1

TailFallingLevel1:
  tail 3 mod 8

TailRemainderLevel1:
  tail 7 mod 8

TailFallingLevel2:
  tail 7 mod 16

TailRemainderLevel2:
  tail 15 mod 16
```

These are intentionally thin aliases.  They preserve the concrete residue
definitions while making the tower grammar readable.

## Level-2 Static Split

New shifted-tail counts:

```lean
orbitWindowResidueCountMod32EqFifteenTail
orbitWindowResidueCountMod32EqThirtyOneTail
```

The split theorem:

```lean
tailResidueCountMod16EqFifteen_split_mod32_fifteen_thirtyOne
```

states:

```text
tail 15 mod 16
  = tail 15 mod 32
    + tail 31 mod 32
```

## Level-2 Recursion Edge

The count-level recursion edge is:

```lean
tailMod16Fifteen_le_nextTailMod16Seven_add_nextTailMod16Fifteen
```

It uses the existing pointwise transitions:

```lean
oddOrbitLabel_succ_mod_sixteen_eq_seven_of_mod_thirtytwo_eq_fifteen
oddOrbitLabel_succ_mod_sixteen_eq_fifteen_of_mod_thirtytwo_eq_thirtyone
```

The reading is:

```text
tail 15 mod 16
  -> next tail 7 mod 16
     or
     next tail 15 mod 16
```

This is the level-`2` analogue of the checkpoint 116 level-`1` recursion.

## Alias Theorems

The level-`1` alias theorems are:

```lean
tailRemainderLevel1_static_split
tailRemainderLevel1_step_grammar
```

They make the grammar explicit:

```text
level 1 remainder
  = level 2 falling + level 2 remainder

level 1 remainder
  -> next level 1 falling + next level 1 remainder
```

The second theorem deliberately stays at level `1` on the target side because
the next tail window re-enters the visible `3 mod 8 / 7 mod 8` reservoir.

## Pressure Entrance

Checkpoint 117 adds the first local pressure entrance:

```lean
sourceContinuationMass_depth_two_pos_of_pressure_depth_two
sourcePressureDepthTwo_delayed_budget_with_tailSeven_remainder
```

The positivity theorem says:

```text
MoreThanHalf continuation pressure at depth 2
  -> continuation mass at depth 2 is positive
```

The pressure-facing budget wrapper keeps the intended caller context visible:

```text
pressure at depth 2
  -> use the delayed budget with a tail 7 mod 8 remainder
```

The pressure hypothesis is not needed by the inequality itself.  It is included
to make the future API path explicit.

## Current Tower State

The concrete tower now has:

```text
level 0:
  exact-height-one reservoir

level 1:
  3 mod 8 falls
  7 mod 8 remains

level 2:
  7 mod 16 falls
  15 mod 16 remains
```

The next likely step is:

```text
level 3:
  15 mod 32 falls
  31 mod 32 remains
```

The recommendation remains: add one concrete level at a time until the naming
and index pattern stabilizes.
