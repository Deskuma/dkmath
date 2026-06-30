# Report Petal 086: Mod 8 Height Partition and First Transition Map

## Scope

Checkpoint `086` moves from static residue occupation toward a transition
graph.  The main target was the exact height-one channel:

```text
odd label % 8 = 3  -> next T-state % 4 = 1
odd label % 8 = 7  -> next T-state % 4 = 3
```

The checkpoint also closes the mod `8` height partition at pointwise and count
level.

## Implemented Lean Surface

File:

```text
DkMath.Collatz.PetalBridge
```

Mod `8` partition facts:

```lean
odd_mod_eight_eq_one_or_three_or_five_or_seven
orbitWindowHeight_eq_two_iff_mod_eight_eq_one
orbitWindowHeight_eq_one_iff_mod_eight_eq_three_or_seven
```

New mod `8` residue counts:

```lean
orbitWindowResidueCountMod8EqOne
orbitWindowResidueCountMod8EqThree
orbitWindowResidueCountMod8EqSeven
```

with window bounds:

```lean
orbitWindowResidueCountMod8EqOne_le_window
orbitWindowResidueCountMod8EqThree_le_window
orbitWindowResidueCountMod8EqSeven_le_window
```

Exact-height count bridge:

```lean
orbitWindowHeightCountEq_two_eq_residueCount_mod8_eq_one
```

Mod `8` partition count:

```lean
orbitWindowResidueCountMod8_partition_eq_window
```

## Transition Map

Raw height-one branch arithmetic:

```lean
next_mod_four_of_mod_eight_eq_three
next_mod_four_of_mod_eight_eq_seven
```

Accelerated-map value on the height-one channel:

```lean
T_val_eq_three_mul_add_one_div_two_of_s_eq_one
```

Orbit-level transition:

```lean
orbitNext_mod_four_eq_one_of_mod_eight_eq_three
orbitNext_mod_four_eq_three_of_mod_eight_eq_seven
```

Meaning:

```text
current odd label % 8 = 3
  -> exact height 1
  -> T(current).val % 4 = 1

current odd label % 8 = 7
  -> exact height 1
  -> T(current).val % 4 = 3
```

This is the first directed edge information for the Petal residue graph.

## Extra Experiment

The fixed higher-coordinate experiment also passed:

```lean
four_le_v2_iff_sixteen_dvd
rawHeightLabel_four_le_iff_sixteen_dvd_threeNPlusOne
odd_sixteen_dvd_three_mul_add_one_iff_mod_sixteen_eq_five
orbitWindowHeight_four_le_iff_mod_sixteen_eq_five
```

So the visible coordinate sequence now includes:

```text
height >= 2 <-> mod 4  = 1
height >= 3 <-> mod 8  = 5
height >= 4 <-> mod 16 = 5
```

This supports the later general `2^r` residue-coordinate route.

## Documentation Sync

Updated:

```text
DkMath.Collatz/docs/Collatz-PetalBridge-Status.md
```

The status note now records:

```text
mod 8 pointwise height partition
mod 8 count partition
first height-one transition edges
mod 16 fixed-coordinate experiment
```

## Inference

The residue graph now has its first directed edges:

```text
3 mod 8 -> 1 mod 4
7 mod 8 -> 3 mod 4
```

This shows why the static occupation counts are not the endpoint.  The next
usable layer is transition statistics: how often the orbit enters the exact
height-one subchannels, and how those subchannels feed the next mod `4`
occupation layer.

The current theorem statements use `T (iterateT i n)` as the next state.  A
more ergonomic next step is a next-label formulation using `iterateT (i + 1)`.
That likely needs a small iterate identity:

```lean
iterateT_succ_eq_T_iterateT
```

## Next Implementation Candidates

1. Add the iterate identity:

    ```lean
    theorem iterateT_succ_eq_T_iterateT
        (n : OddNat) (i : ℕ) :
        iterateT (i + 1) n = T (iterateT i n)
    ```

    Then expose label-facing transition theorems:

    ```lean
    oddOrbitLabel n i % 8 = 3
      -> oddOrbitLabel n (i + 1) % 4 = 1

    oddOrbitLabel n i % 8 = 7
      -> oddOrbitLabel n (i + 1) % 4 = 3
    ```

2. Prefix mod `8` occupation:

    ```lean
    orbitWindowPrefixResidueCountMod8EqOne
    orbitWindowPrefixResidueCountMod8EqThree
    orbitWindowPrefixResidueCountMod8EqFive
    orbitWindowPrefixResidueCountMod8EqSeven
    ```

3. Count-level transition statistics for exact height-one subchannels.

4. Start a general fixed-coordinate helper for:

    ```text
    height >= r <-> odd residue solving 3m + 1 = 0 mod 2^r
    ```

but only after one more fixed experiment or after repeated duplication makes
the abstraction pay for itself.

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
