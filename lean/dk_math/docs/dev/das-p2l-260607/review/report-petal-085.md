# Report Petal 085: Prefix Residue Counts and First Mod 4 Partition

## Scope

Checkpoint `085` extends the Collatz residue occupation bridge in two
directions:

```text
full window  -> prefix window
height >= 2  -> height >= 3
```

It also closes the first mod `4` partition:

```text
odd label mod 4 = 1  <-> height >= 2
odd label mod 4 = 3  <-> height = 1
```

## Implemented Lean Surface

File:

```text
DkMath.Collatz.PetalBridge
```

Prefix residue count:

```lean
orbitWindowPrefixResidueCountMod4EqOne
orbitWindowPrefixResidueCountMod4EqOne_le_prefix
orbitWindowPrefixResidueCountMod4EqOne_eq_residueCount
orbitWindowHeightPrefixCountGe_two_eq_prefixResidueCount_mod4_eq_one
orbitWindowHeightPrefix_sum_ge_window_add_of_residue_mod4_count_ge
```

This gives the prefix handoff:

```lean
m <= orbitWindowPrefixResidueCountMod4EqOne n k r
  -> r + m <= sumS n r
```

Mod `8` occupation count:

```lean
orbitWindowResidueCountMod8EqFive
orbitWindowResidueCountMod8EqFive_le_window
orbitWindowHeightCountGe_three_eq_residueCount_mod8_eq_five
orbitWindowHeightSeq_sum_ge_window_add_countGe_two_add_of_residue_mod8_count_ge
```

This gives the three-layer handoff:

```lean
m <= orbitWindowResidueCountMod8EqFive n k
  -> k + orbitWindowHeightCountGe n k 2 + m <= sumS n k
```

## Extra Result

The first mod `4` partition was also closed.

Pointwise:

```lean
odd_mod_four_eq_one_or_three
orbitWindowHeight_eq_one_iff_mod_four_eq_three
```

Count-level:

```lean
orbitWindowResidueCountMod4EqThree
orbitWindowResidueCountMod4EqThree_le_window
orbitWindowHeightCountEq_one_eq_residueCount_mod4_eq_three
orbitWindowResidueCountMod4EqOne_add_eqThree_eq_window
```

This gives:

```text
CountGe 2 = labels with residue 1 mod 4
CountEq 1 = labels with residue 3 mod 4
residueCountMod4EqOne + residueCountMod4EqThree = k
```

The result is useful because the first Collatz peeling layer is no longer just
a valuation statement.  It is a finite two-channel residue partition.

## Documentation Sync

Updated:

```text
DkMath.Collatz/docs/Collatz-PetalBridge-Status.md
```

The status note now records:

```text
prefix residue occupation -> prefix sumS lower bound
mod 8 occupation -> three-layer sumS lower bound
mod 4 partition -> residue counts fill the window
```

## Inference

The practical observation target is now:

```text
Find occupation lower bounds for residue classes.
```

Instead of directly proving average height claims, downstream work can prove
that enough orbit labels fall into a residue channel:

```text
mod 4 = 1  -> second layer
mod 8 = 5  -> third layer
```

The mod `4` partition also clarifies the obstruction shape.  A prefix with too
few `1 mod 4` labels has many `3 mod 4` labels, which means many exact
height-one steps.  This is a concrete place to study transition behavior under
the accelerated map `T`.

## Next Implementation Candidates

1. Residue transition map under one accelerated step:

    ```lean
    orbitWindowHeight_eq_one_of_mod_four_eq_three
    T_residue_mod_four_of_height_one
    ```

    The intended reading is:

    ```text
    m % 4 = 3
      -> height = 1
      -> T(m) = (3m + 1) / 2
      -> next residue can be inspected explicitly
    ```

2. Prefix mod `8` occupation:

    ```lean
    orbitWindowPrefixResidueCountMod8EqFive
    orbitWindowHeightPrefixCountGe_three_eq_prefixResidueCount_mod8_eq_five
    ```

3. Fixed mod `16` experiment:

    ```text
    height >= 4
      <-> odd label % 16 = 5
    ```

    This would confirm the next residue coordinate before attempting a general
    `2^r` formulation.

4. General residue coordinate remains a later target:

    ```text
    height >= r
      <-> 2^r | (3m + 1)
      <-> m is the odd solution of 3m + 1 = 0 mod 2^r
    ```

## Verification

Passed:

```text
lake build DkMath.Collatz.PetalBridge
lake build DkMath.Collatz.Collatz2K26
git diff --check -- changed Collatz Petal files
```

Known unrelated warning observed during the build:

```text
DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:152:6:
declaration uses `sorry`
```
