# Report Petal 089: Retention Channel for 7 mod 8

## Checkpoint

This checkpoint follows `__next_implementation-089.md`.

Checkpoint 088 closed the delayed-peeling side:

```text
3 mod 8 source
  -> next tail height >= 2
  -> delayed drift contribution
```

Checkpoint 089 closes the retention counterpart:

```text
7 mod 8 source
  -> next tail exact height 1
```

## Implemented Lean Surface

File:

```text
lean/dk_math/DkMath/Collatz/PetalBridge.lean
```

New shifted-tail exact-height count:

```lean
orbitWindowHeightCountEqTail
```

New basic API:

```lean
orbitWindowHeightCountEqTail_le_window
orbitWindowHeightCountEqTail_succ
```

New tail exact-height/residue bridge:

```lean
orbitWindowHeightCountEqTail_one_eq_tailResidueCount_mod4_eq_three
```

New retention-channel theorem:

```lean
orbitWindowResidueCountMod8EqSeven_le_tailHeightCountEq_one
```

New tail partition:

```lean
orbitWindowHeightTail_countGe_two_add_countEq_one_eq_window
```

New two-step retention witness:

```lean
sumS_two_steps_eq_two_of_mod_eight_eq_seven_and_next_mod_eight_eq_seven
```

## Main Reading

The exact height-one source layer is no longer homogeneous.

It splits into two transition behaviors:

```text
3 mod 8:
  height 1 now
  next tail height >= 2
  delayed peeling source

7 mod 8:
  height 1 now
  next tail height = 1
  retention source
```

The new theorem:

```lean
theorem orbitWindowResidueCountMod8EqSeven_le_tailHeightCountEq_one
    (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountMod8EqSeven n k ≤
      orbitWindowHeightCountEqTail n k 1
```

formalizes the retention side at count level.

## Tail Partition

The shifted tail now has a clean first-layer partition:

```lean
theorem orbitWindowHeightTail_countGe_two_add_countEq_one_eq_window
    (n : OddNat) (k : ℕ) :
    orbitWindowHeightCountGeTail n k 2 +
      orbitWindowHeightCountEqTail n k 1 = k
```

Meaning:

```text
every tail entry has height at least 1
therefore it is either:
  exact height 1
or:
  height >= 2
```

This gives a useful finite observation split for the next directed graph layer.

## Two-Step Witness

The following exact witness passed:

```lean
theorem sumS_two_steps_eq_two_of_mod_eight_eq_seven_and_next_mod_eight_eq_seven
    (n : OddNat)
    (h0 : oddOrbitLabel n 0 % 8 = 7)
    (h1 : oddOrbitLabel n 1 % 8 = 7) :
    sumS n 2 = 2
```

This is not a transition theorem by itself because it assumes the second
label is again `7 mod 8`.  Its value is diagnostic: it isolates a genuine
two-step low-peeling retention pattern.

## Documentation Sync

Updated:

```text
lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
```

The status note now records:

```text
tail exact-height count
retention channel for 7 mod 8
tail CountGe 2 / CountEq 1 partition
two-step 7 -> 7 exact-height witness
```

## Verification

Passed:

```text
lake build DkMath.Collatz.PetalBridge
```

The targeted build still reports the existing upstream warning:

```text
DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean: declaration uses `sorry`
```

No new `sorry` was introduced in this checkpoint.

## Next Implementation Candidates

Candidate A: source-channel sum bound.

Since:

```text
3 source <= tail CountGe 2
7 source <= tail CountEq 1
tail CountGe 2 + tail CountEq 1 = k
```

we should be able to record:

```lean
theorem orbitWindowResidueCountMod8EqThree_add_seven_le_window
    (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountMod8EqThree n k +
      orbitWindowResidueCountMod8EqSeven n k ≤ k
```

This already follows from the mod `8` partition, but proving it through the
tail split would document the transition-graph reading.

Candidate B: introduce source/receiver vocabulary in docs or thin defs.

Suggested names:

```text
DelayedPeeling channel:
  3 mod 8

Retention channel:
  7 mod 8

ImmediateStrong channel:
  5 mod 8

ExactTwo channel:
  1 mod 8
```

Candidate C: local `sumSFrom`.

The current local theorem uses restart:

```lean
sumS (iterateT i n) 2
```

A window-native local sum would make future graph reasoning more readable:

```lean
noncomputable def sumSFrom (n : OddNat) (start len : ℕ) : ℕ :=
  (List.range len).map
    (fun j => orbitWindowHeight n (start + j))
  |>.sum
```

This is worth adding only if the next transition-graph checkpoint needs
several local two-step or three-step statements.
