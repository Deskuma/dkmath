# Report Petal 117: Level-2 Remainder

## Summary

Checkpoint 117 extends the delayed-reservoir tower by one concrete level.

Checkpoint 116 established:

```text
tail 7 mod 8
  -> next tail 3 mod 8 + next tail 7 mod 8
```

Checkpoint 117 adds:

```text
tail 15 mod 16
  -> next tail 7 mod 16 + next tail 15 mod 16
```

This makes the tower visible through level `2`.

## Implemented Lean Surface

File:

```text
lean/dk_math/DkMath/Collatz/PetalBridge.lean
```

New shifted-tail mod-32 counts:

```lean
orbitWindowResidueCountMod32EqFifteenTail
orbitWindowResidueCountMod32EqThirtyOneTail
```

Level aliases:

```lean
TailRemainderLevel0
TailRemainderLevel1
TailRemainderLevel2
TailFallingLevel1
TailFallingLevel2
```

Level-2 static split:

```lean
tailResidueCountMod16EqFifteen_split_mod32_fifteen_thirtyOne
```

Level-alias theorems:

```lean
tailRemainderLevel1_static_split
tailRemainderLevel1_step_grammar
```

Level-2 recursion edge:

```lean
tailMod16Fifteen_le_nextTailMod16Seven_add_nextTailMod16Fifteen
```

Pressure entrance:

```lean
sourceContinuationMass_depth_two_pos_of_pressure_depth_two
sourcePressureDepthTwo_delayed_budget_with_tailSeven_remainder
```

## Experimental Results

### Experiment A: mod32 split for `15 mod 16`

Succeeded.

```lean
tailResidueCountMod16EqFifteen_split_mod32_fifteen_thirtyOne
```

Reading:

```text
tail 15 mod 16
  = tail 15 mod 32
    + tail 31 mod 32
```

### Experiment B: pointwise transition aliases

The expected existing theorems were present and reusable:

```lean
oddOrbitLabel_succ_mod_sixteen_eq_seven_of_mod_thirtytwo_eq_fifteen
oddOrbitLabel_succ_mod_sixteen_eq_fifteen_of_mod_thirtytwo_eq_thirtyone
```

No duplicate aliases were needed.

### Experiment C: count-level recursion for `15 mod 16`

Succeeded.

```lean
tailMod16Fifteen_le_nextTailMod16Seven_add_nextTailMod16Fifteen
```

Reading:

```text
tail 15 mod 16
  -> next tail 7 mod 16
     or
     next tail 15 mod 16
```

### Experiment D-F: level API

Succeeded.

The level aliases make the first tower layers readable:

```text
level 0 remainder:
  exact-height-one reservoir

level 1 falling:
  3 mod 8

level 1 remainder:
  7 mod 8

level 2 falling:
  7 mod 16

level 2 remainder:
  15 mod 16
```

The alias bridge:

```lean
tailRemainderLevel1_static_split
```

records:

```text
level 1 remainder = level 2 falling + level 2 remainder
```

The recursion alias:

```lean
tailRemainderLevel1_step_grammar
```

records:

```text
level 1 remainder
  -> next level 1 falling + next level 1 remainder
```

### Experiment G: pressure at depth 2 gives positive continuation mass

Succeeded.

```lean
sourceContinuationMass_depth_two_pos_of_pressure_depth_two
```

Since:

```lean
MoreThanHalf count total := total < 2 * count
```

Lean closes positivity with `omega`.

### Experiment H: pressure-facing delayed budget wrapper

Succeeded.

```lean
sourcePressureDepthTwo_delayed_budget_with_tailSeven_remainder
```

The pressure hypothesis is not used by the inequality itself.  It is kept as a
caller-facing wrapper to document the intended route:

```text
pressure at depth 2
  -> positive continuation mass
  -> delayed budget with explicit remainder
```

## Mathematical Reading

The tower is now concrete through level `2`:

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

The important pattern is not collapse.  It is accounting:

```text
falling color:
  charged to future height / sumS

continuing color:
  carried as an explicit next-level remainder
```

This is compatible with the checkpoint 116 budget-with-remainder philosophy.

## Documentation Updates

Updated:

```text
lean/dk_math/DkMath/Collatz/README.md
lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
```

Added:

```text
lean/dk_math/DkMath/Collatz/docs/Collatz-Level2Remainder-117.md
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

### 1. Add level 3 concrete split

Next split:

```text
tail 31 mod 32
  = tail 31 mod 64
    + tail 63 mod 64
```

Expected count names:

```lean
orbitWindowResidueCountMod64EqThirtyOneTail
orbitWindowResidueCountMod64EqSixtyThreeTail
```

### 2. Add level 3 recursion edge

Expected edge:

```text
tail 31 mod 32
  -> next tail 15 mod 32 + next tail 31 mod 32
```

Existing pointwise theorems around:

```lean
oddOrbitLabel_succ_mod_thirtytwo_eq_fifteen_of_mod_sixtyfour_eq_thirtyone
oddOrbitLabel_succ_mod_thirtytwo_eq_thirtyone_of_mod_sixtyfour_eq_sixtythree
```

should be reusable.

### 3. Connect range pressure to depth-2 pressure

The local pressure entrance is now available.  The next pressure-side bridge is
probably a small specialization:

```text
SourceContinuationPressureOnRange n k 2 1
  -> MoreThanHalf continuationMass depth 2 retentionMass depth 2
```

Once this exists, the caller can enter the delayed-reservoir budget from the
range-pressure vocabulary rather than a raw local `MoreThanHalf` hypothesis.
