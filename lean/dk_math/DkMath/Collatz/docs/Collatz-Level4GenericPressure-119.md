# Collatz Level-4 And Generic Pressure 119

Checkpoint 119 advances both sides of the current program:

```text
tower side:
  extend the delayed-reservoir tower to level 4

pressure side:
  generalize range-pressure extraction to any selected depth in the range
```

## Level-4 Tower Extension

Checkpoint 118 fixed level `3`:

```text
tail 31 mod 32
  -> next tail 15 mod 32 + next tail 31 mod 32
```

Checkpoint 119 adds level `4`:

```text
tail 63 mod 64
  -> next tail 31 mod 64 + next tail 63 mod 64
```

New shifted-tail counts:

```lean
orbitWindowResidueCountMod128EqSixtyThreeTail
orbitWindowResidueCountMod128EqOneHundredTwentySevenTail
```

Static split:

```lean
tailResidueCountMod64EqSixtyThree_split_mod128_sixtyThree_oneHundredTwentySeven
```

Reading:

```text
tail 63 mod 64
  = tail 63 mod 128
    + tail 127 mod 128
```

Pointwise aliases:

```lean
oddOrbitLabel_succ_mod_sixtyfour_eq_thirtyone_of_mod_onehundredtwentyeight_eq_sixtythree
oddOrbitLabel_succ_mod64_eq63_of_mod128_eq127
```

The second name is shortened to avoid long-line warnings while the docstring
keeps the full `127 mod 128 -> 63 mod 64` reading searchable.

Count-level recursion edge:

```lean
tailMod64SixtyThree_le_nextTailMod64ThirtyOne_add_nextTailMod64SixtyThree
```

## Level Aliases

New aliases:

```lean
TailRemainderLevel4
TailFallingLevel4
```

New alias theorems:

```lean
tailRemainderLevel3_static_split
tailRemainderLevel3_step_grammar
```

Reading:

```text
level 3 remainder
  = level 4 falling + level 4 remainder

level 3 remainder
  -> next level 3 falling + next level 3 remainder
```

## Generic Pressure Extraction

Checkpoint 118 had a special one-depth extractor:

```lean
sourcePressureDepthTwo_of_pressureOnRange_two_one
```

Checkpoint 119 adds general wrappers:

```lean
sourcePressureAtDepth_of_pressureOnRange
sourceContinuationMass_pos_of_localPressure
sourceContinuationMass_pos_of_pressureOnRange_at
```

The meaning is:

```text
SourceContinuationPressureOnRange n k r len
  and j < len
  -> local MoreThanHalf pressure at depth r+j
  -> positive continuation mass at depth r+j
```

This is the first reusable pressure-side surface for selecting local
tower-entry opportunities from a pressure-heavy range.

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

level 4:
  31 mod 64 falls
  63 mod 64 remains
```

The next expected concrete level is:

```text
level 5:
  63 mod 128 falls
  127 mod 128 remains
```

## Next Direction

The tower and pressure API are now close enough to start finite accounting
experiments:

```text
pressure-heavy range
  -> many selected local pressure depths
  -> positive local tower-entry mass
  -> delayed budget plus deep remainder
```

The likely next hard question is not how to extend one more residue level, but
how to count useful selected local pressure depths without double-counting the
same finite window mass.
