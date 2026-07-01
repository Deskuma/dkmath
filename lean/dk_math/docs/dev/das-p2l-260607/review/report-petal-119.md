# Report Petal 119: Level-4 And Generic Pressure

## Summary

Checkpoint 119 closes two useful extensions.

Tower side:

```text
tail 63 mod 64
  -> next tail 31 mod 64 + next tail 63 mod 64
```

Pressure side:

```text
SourceContinuationPressureOnRange n k r len
  and j < len
  -> local pressure at depth r+j
  -> positive continuation mass at depth r+j
```

This moves the project from a one-depth pressure entrance to a reusable
selected-depth interface.

## Implemented Lean Surface

File:

```text
lean/dk_math/DkMath/Collatz/PetalBridge.lean
```

New level-`4` shifted-tail counts:

```lean
orbitWindowResidueCountMod128EqSixtyThreeTail
orbitWindowResidueCountMod128EqOneHundredTwentySevenTail
```

New aliases:

```lean
TailRemainderLevel4
TailFallingLevel4
```

Level-`4` static split:

```lean
tailResidueCountMod64EqSixtyThree_split_mod128_sixtyThree_oneHundredTwentySeven
```

Level-`3` alias theorems:

```lean
tailRemainderLevel3_static_split
tailRemainderLevel3_step_grammar
```

Pointwise level-`4` aliases:

```lean
oddOrbitLabel_succ_mod_sixtyfour_eq_thirtyone_of_mod_onehundredtwentyeight_eq_sixtythree
oddOrbitLabel_succ_mod64_eq63_of_mod128_eq127
```

Level-`4` recursion edge:

```lean
tailMod64SixtyThree_le_nextTailMod64ThirtyOne_add_nextTailMod64SixtyThree
```

Generic pressure wrappers:

```lean
sourcePressureAtDepth_of_pressureOnRange
sourceContinuationMass_pos_of_localPressure
sourceContinuationMass_pos_of_pressureOnRange_at
```

## Experimental Results

### Experiment A-C: generic pressure extraction

Succeeded.

The new wrapper:

```lean
sourcePressureAtDepth_of_pressureOnRange
```

is a meaning-name alias around:

```lean
moreThanHalf_of_sourceContinuationPressure
```

The positivity bridge:

```lean
sourceContinuationMass_pos_of_localPressure
```

works for any depth, not just depth `2`.

The composed range theorem:

```lean
sourceContinuationMass_pos_of_pressureOnRange_at
```

gives:

```text
pressure range + selected index j
  -> positive continuation mass at depth r+j
```

### Experiment D-E: level-4 residue counts and split

Succeeded.

```lean
orbitWindowResidueCountMod128EqSixtyThreeTail
orbitWindowResidueCountMod128EqOneHundredTwentySevenTail
tailResidueCountMod64EqSixtyThree_split_mod128_sixtyThree_oneHundredTwentySeven
```

Reading:

```text
tail 63 mod 64
  = tail 63 mod 128
    + tail 127 mod 128
```

### Experiment F-H: level-4 aliases and recursion support

Succeeded.

```lean
TailRemainderLevel4
TailFallingLevel4
tailRemainderLevel3_static_split
tailRemainderLevel3_step_grammar
```

The level-`3` alias grammar now reads:

```text
level 3 remainder
  = level 4 falling + level 4 remainder

level 3 remainder
  -> next level 3 falling + next level 3 remainder
```

### Extra: pointwise aliases for level 4

The raw arithmetic anchors already existed:

```lean
next_mod_sixtyfour_of_mod_onehundredtwentyeight_eq_sixtythree
next_mod_sixtyfour_of_mod_onehundredtwentyeight_eq_onehundredtwentyseven
```

Checkpoint 119 added orbit-label versions:

```lean
oddOrbitLabel_succ_mod_sixtyfour_eq_thirtyone_of_mod_onehundredtwentyeight_eq_sixtythree
oddOrbitLabel_succ_mod64_eq63_of_mod128_eq127
```

The second name is shortened to avoid line-length warnings.

### Extra: level-4 count recursion

Succeeded.

```lean
tailMod64SixtyThree_le_nextTailMod64ThirtyOne_add_nextTailMod64SixtyThree
```

Reading:

```text
tail 63 mod 64
  -> next tail 31 mod 64
     or
     next tail 63 mod 64
```

## Mathematical Reading

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

This confirms the recurring pattern:

```text
falling color:
  2^(L+1)-1 modulo 2^(L+2)

continuing color:
  2^(L+2)-1 modulo 2^(L+2)
```

The pressure interface now supports selected local depths:

```text
range pressure
  -> choose j
  -> local positive continuation mass
```

This is a needed precondition for finite accounting over pressure-heavy ranges.

## Documentation Updates

Updated:

```text
lean/dk_math/DkMath/Collatz/README.md
lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
```

Added:

```text
lean/dk_math/DkMath/Collatz/docs/Collatz-Level4GenericPressure-119.md
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

### 1. Add level 5 concrete split

Expected next split:

```text
tail 127 mod 128
  = tail 127 mod 256
    + tail 255 mod 256
```

The raw arithmetic anchors around `mod 256` already appear to exist.

### 2. Start finite selected-depth accounting

The next harder bridge is no longer merely another residue level.  It is:

```text
SourceContinuationPressureOnRange n k r len
  -> many usable local pressure depths
```

The new `sourceContinuationMass_pos_of_pressureOnRange_at` gives one selected
depth.  A future theorem should package a finite collection of selected depths
without double-counting window mass.

### 3. Deep-remainder sparsity

The tower suggests that continuing mass is pushed into:

```text
7 mod 8
15 mod 16
31 mod 32
63 mod 64
...
```

The future obstruction target is a sparsity statement for deep all-ones
residue classes, probably under separation or orbit-window hypotheses.
