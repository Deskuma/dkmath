# Report Petal 116: Delayed Reservoir Tower

## Summary

Checkpoint 116 extends checkpoint 115 from a one-step delayed branch into the
first recursive edge of a delayed-reservoir tower.

Checkpoint 115 established:

```text
tail exact height 1
  = tail 3 mod 8
    + tail 7 mod 8
```

Checkpoint 116 proves that the continuing color is not a dead end:

```text
tail 7 mod 8
  -> next tail exact height 1
  -> next tail 3 mod 8 + next tail 7 mod 8
```

So the current grammar is:

```text
reservoir
  -> falling color
  -> continuing color
     -> next reservoir
```

## Implemented Lean Surface

File:

```text
lean/dk_math/DkMath/Collatz/PetalBridge.lean
```

New shifted-tail mod-16 counts:

```lean
orbitWindowResidueCountMod16EqSevenTail
orbitWindowResidueCountMod16EqFifteenTail
```

Static refinement of the continuing color:

```lean
tailResidueCountMod8EqSeven_split_mod16_seven_fifteen
```

Count-level continuing-color recursion:

```lean
tailMod8Seven_le_nextTailHeightCountEq_one
tailMod8Seven_le_nextTailMod8Three_add_nextTailMod8Seven
```

One-step reservoir grammar:

```lean
tailExactHeightOneReservoir_step_grammar
```

Budget-with-remainder forms:

```lean
tailExactHeightOneReservoir_budget_with_remainder
sourceContinuationMass_depth_two_delayed_budget_with_tailSeven_remainder
```

## Experimental Results

### Experiment A: mod16 split

Succeeded.

```lean
tailResidueCountMod8EqSeven_split_mod16_seven_fifteen
```

This proves:

```text
tail 7 mod 8 count
  = tail 7 mod 16 count
    + tail 15 mod 16 count
```

### Experiment B: pointwise `7 mod 8` continuation

Already existed:

```lean
orbitWindowNextHeight_eq_one_of_mod_eight_eq_seven
```

This was reused rather than duplicated.

### Experiment C: count-level continuation

Succeeded.

```lean
tailMod8Seven_le_nextTailHeightCountEq_one
```

Meaning:

```text
tail 7 mod 8 at this step
  -> next tail exact height 1
```

### Experiment D: next reservoir split

Succeeded.

```lean
tailMod8Seven_le_nextTailMod8Three_add_nextTailMod8Seven
```

Meaning:

```text
tail 7 mod 8
  -> next tail 3 mod 8 + next tail 7 mod 8
```

### Experiment E: one-step grammar

Succeeded.

```lean
tailExactHeightOneReservoir_step_grammar
```

This packages the local grammar:

```text
current exact-height-one reservoir
  -> next extra-height count
     or
     next exact-height-one reservoir
```

### Experiment F: budget with remainder

Succeeded.

```lean
tailExactHeightOneReservoir_budget_with_remainder
```

This is stronger than a pure drift lower bound because it does not discard the
continuing part.  It explicitly carries the `7 mod 8` remainder.

### Experiment G: source continuation budget with remainder

Succeeded.

```lean
sourceContinuationMass_depth_two_delayed_budget_with_tailSeven_remainder
```

Meaning:

```text
base layer + source continuation depth 2
  <= next sumS
     + tail 7 mod 8 remainder
```

This is currently the most useful bridge back toward pressure-heavy arguments.

## Main Mathematical Reading

The key correction remains:

```text
continuation mass does not all immediately peel.
```

But checkpoint 116 gives a better replacement:

```text
continuation mass enters a reservoir;
the falling color is charged to sumS;
the continuing color is carried as a remainder.
```

This is closer to an accounting proof than a direct collapse proof.

The important finite pattern is:

```text
falling part:
  contributes to accumulated height

continuing part:
  remains visible and can be refined at the next resolution
```

## Documentation Updates

Updated:

```text
lean/dk_math/DkMath/Collatz/README.md
lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
```

Added:

```text
lean/dk_math/DkMath/Collatz/docs/Collatz-DelayedReservoirTower-116.md
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

### 1. Add the next concrete continuation split

The next static split should be:

```text
tail 15 mod 16
  = tail 15 mod 32
    + tail 31 mod 32
```

This mirrors the new `7 mod 8` split.

### 2. Add the next count-level recursion edge

The expected edge is:

```text
tail 15 mod 16
  -> next tail 7 mod 16 + next tail 15 mod 16
```

Existing pointwise theorems around:

```lean
oddOrbitLabel_succ_mod_sixteen_eq_seven_of_mod_thirtytwo_eq_fifteen
oddOrbitLabel_succ_mod_sixteen_eq_fifteen_of_mod_thirtytwo_eq_thirtyone
```

should be reusable.

### 3. Start a small level-indexed remainder API

Do not generalize too early.  A useful next compromise is a named level-0 /
level-1 API:

```text
level 0 remainder:
  exact-height-one reservoir

level 1 remainder:
  tail 7 mod 8

level 2 remainder:
  tail 15 mod 16
```

This can later become a recursive definition once the low-level theorem names
are stable.
