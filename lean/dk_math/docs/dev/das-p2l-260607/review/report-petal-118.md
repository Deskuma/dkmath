# Report Petal 118: Level-3 And Pressure Entrance

## Summary

Checkpoint 118 advances two fronts.

First, it extends the delayed-reservoir tower to level `3`:

```text
tail 31 mod 32
  -> next tail 15 mod 32 + next tail 31 mod 32
```

Second, it connects one-depth range pressure to local depth-`2` pressure:

```text
SourceContinuationPressureOnRange n k 2 1
  -> local MoreThanHalf pressure at depth 2
  -> positive continuation mass at depth 2
```

## Implemented Lean Surface

File:

```text
lean/dk_math/DkMath/Collatz/PetalBridge.lean
```

New level-`3` shifted-tail counts:

```lean
orbitWindowResidueCountMod64EqThirtyOneTail
orbitWindowResidueCountMod64EqSixtyThreeTail
```

New aliases:

```lean
TailRemainderLevel3
TailFallingLevel3
```

Level-`3` static split:

```lean
tailResidueCountMod32EqThirtyOne_split_mod64_thirtyOne_sixtyThree
```

Level-`2` alias theorems:

```lean
tailRemainderLevel2_static_split
tailRemainderLevel2_step_grammar
```

Level-`3` recursion edge:

```lean
tailMod32ThirtyOne_le_nextTailMod32Fifteen_add_nextTailMod32ThirtyOne
```

Range-pressure extraction:

```lean
sourcePressureDepthTwo_of_pressureOnRange_two_one
sourceContinuationMass_depth_two_pos_of_pressureOnRange_two_one
```

## Experimental Results

### Experiment A: level-3 residue counts

Succeeded.

```lean
orbitWindowResidueCountMod64EqThirtyOneTail
orbitWindowResidueCountMod64EqSixtyThreeTail
```

### Experiment B: level-3 static split

Succeeded.

```lean
tailResidueCountMod32EqThirtyOne_split_mod64_thirtyOne_sixtyThree
```

Reading:

```text
tail 31 mod 32
  = tail 31 mod 64
    + tail 63 mod 64
```

### Experiment C: level-3 recursion edge

Succeeded.

```lean
tailMod32ThirtyOne_le_nextTailMod32Fifteen_add_nextTailMod32ThirtyOne
```

It uses the existing pointwise transitions:

```lean
oddOrbitLabel_succ_mod_thirtytwo_eq_fifteen_of_mod_sixtyfour_eq_thirtyone
oddOrbitLabel_succ_mod_thirtytwo_eq_thirtyone_of_mod_sixtyfour_eq_sixtythree
```

Reading:

```text
tail 31 mod 32
  -> next tail 15 mod 32
     or
     next tail 31 mod 32
```

### Experiment D-F: level-3 aliases

Succeeded.

```lean
TailRemainderLevel3
TailFallingLevel3
tailRemainderLevel2_static_split
tailRemainderLevel2_step_grammar
```

These keep the concrete tower readable:

```text
level 2 remainder
  = level 3 falling + level 3 remainder

level 2 remainder
  -> next level 2 falling + next level 2 remainder
```

### Experiment G: one-depth range pressure to local pressure

Succeeded.

```lean
sourcePressureDepthTwo_of_pressureOnRange_two_one
```

This uses the existing extractor:

```lean
moreThanHalf_of_sourceContinuationPressure
```

with `r = 2`, `len = 1`, and `j = 0`.

### Experiment H: one-depth range pressure to positive continuation mass

Succeeded.

```lean
sourceContinuationMass_depth_two_pos_of_pressureOnRange_two_one
```

This composes the range extraction with:

```lean
sourceContinuationMass_depth_two_pos_of_pressure_depth_two
```

## Mathematical Reading

The delayed-reservoir tower now reaches:

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

The pressure side now has its first one-depth connection:

```text
range pressure over [2, 3)
  -> local pressure at depth 2
  -> positive source continuation mass
```

This is still local.  The next pressure task is to extract useful local
pressure from longer ranges, or to package a range profile as a finite list of
local tower-entry opportunities.

## Documentation Updates

Updated:

```text
lean/dk_math/DkMath/Collatz/README.md
lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
```

Added:

```text
lean/dk_math/DkMath/Collatz/docs/Collatz-Level3PressureEntrance-118.md
```

## Verification

Commands run:

```text
lake build DkMath.Collatz.PetalBridge
lake build DkMath.Collatz.Collatz2K26
rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge.lean
git diff --check -- <touched files>
```

Result:

```text
Both builds completed successfully.
No `sorry` was found in `DkMath.Collatz.PetalBridge`.
`git diff --check` reported no whitespace errors.
```

Known unrelated warning remains:

```text
DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:152:6:
declaration uses `sorry`
```

## Next Implementation Candidates

### 1. Add level 4 concrete split

Expected next split:

```text
tail 63 mod 64
  = tail 63 mod 128
    + tail 127 mod 128
```

Expected existing pointwise transitions are around:

```lean
oddOrbitLabel_succ_mod_sixtyfour_eq_thirtyone_of_mod_onehundredtwentyeight_eq_sixtythree
oddOrbitLabel_succ_mod_sixtyfour_eq_sixtythree_of_mod_onehundredtwentyeight_eq_onehundredtwentyseven
```

If these names are absent, add pointwise aliases first.

### 2. Add longer range pressure extractors

The next pressure-facing theorem should extract a local pressure statement from
a longer range:

```text
SourceContinuationPressureOnRange n k r len
  and j < len
  -> local MoreThanHalf at depth r+j
```

The generic extractor already exists as:

```lean
moreThanHalf_of_sourceContinuationPressure
```

Useful next wrappers may specialize it to common entry depths such as `2`,
`3`, or a one-depth range beginning at a chosen depth.

### 3. Start finite tower-entry accounting

A future theorem should connect:

```text
range pressure count
```

to:

```text
number of local delayed-reservoir budget opportunities
```

This is the point where the tower becomes more than a residue grammar: it
becomes a finite accounting surface for pressure-heavy windows.
