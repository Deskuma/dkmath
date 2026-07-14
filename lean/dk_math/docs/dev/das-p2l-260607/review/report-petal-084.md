# Report Petal 084: Collatz Residue Occupation Bridge

## Scope

Checkpoint `084` closes the requested bridge:

```text
height >= 2
  <-> 4 | (3m + 1)
  <-> m % 4 = 1          for odd m
```

and lifts it from pointwise Collatz height observations to a window-level
occupation count feeding the existing `sumS` lower-bound API.

## Implemented Lean Surface

File:

```text
DkMath.Collatz.PetalBridge
```

New pointwise residue bridge:

```lean
two_le_v2_iff_four_dvd
rawHeightLabel_two_le_iff_four_dvd_threeNPlusOne
orbitWindowHeight_two_le_iff_four_dvd
odd_four_dvd_three_mul_add_one_iff_mod_four_eq_one
orbitWindowHeight_two_le_iff_mod_four_eq_one
```

New occupation count:

```lean
orbitWindowResidueCountMod4EqOne
orbitWindowResidueCountMod4EqOne_le_window
```

Main count equivalence:

```lean
orbitWindowHeightCountGe_two_eq_residueCount_mod4_eq_one
```

Main drift bridge:

```lean
orbitWindowHeightSeq_sum_ge_window_add_of_residue_mod4_count_ge
```

This last theorem is the practical handoff:

```lean
m <= orbitWindowResidueCountMod4EqOne n k
  -> k + m <= sumS n k
```

So future work can prove a residue occupation lower bound instead of directly
proving a valuation-count lower bound.

## Extra Experiment

The next pointwise residue layer was also tested and passed:

```lean
three_le_v2_iff_eight_dvd
rawHeightLabel_three_le_iff_eight_dvd_threeNPlusOne
odd_eight_dvd_three_mul_add_one_iff_mod_eight_eq_five
orbitWindowHeight_three_le_iff_mod_eight_eq_five
```

This confirms the expected next address:

```text
height >= 3
  <-> 8 | (3m + 1)
  <-> m % 8 = 5          for odd m
```

## Documentation Sync

Updated:

```text
DkMath.Collatz/docs/Collatz-PetalBridge-Status.md
```

The status note now records:

```text
CountGe 2 = mod 4 residue occupation
mod 4 occupation lower bound -> k + m <= sumS n k
mod 8 pointwise experiment
```

## Inference

The bridge changes the next proof target.

Before:

```text
Show many heights are >= 2.
```

Now:

```text
Show many odd orbit labels are 1 mod 4.
```

This is a better Petal-facing statement because it is a finite address
occupation condition.  It can be inspected by residue transitions, prefix
windows, and eventually a `2^r` address coordinate.

## Next Implementation Candidates

1. Prefix residue count:

    ```lean
    orbitWindowPrefixResidueCountMod4EqOne
    orbitWindowHeightPrefixCountGe_two_eq_prefixResidueCount_mod4_eq_one
    orbitWindowHeightPrefix_sum_ge_window_add_of_residue_mod4_count_ge
    ```

2. Mod `8` occupation count:

    ```lean
    orbitWindowResidueCountMod8EqFive
    orbitWindowHeightCountGe_three_eq_residueCount_mod8_eq_five
    ```

3. Residue transition observation for the accelerated map `T`.

    This should inspect how residue classes move after one accelerated Collatz
    step, separated by the height layer:

    ```text
    m % 4 = 3  -> height = 1
    m % 4 = 1  -> height >= 2
    ```

4. General residue coordinate:

    ```text
    height >= r
      <-> 2^r | (3m + 1)
      <-> m is the unique odd residue solving 3m + 1 = 0 mod 2^r
    ```

This is the likely long-term Petal address form, but the prefix and mod `8`
count bridges are the safer next local checkpoints.

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
