# Report Petal 090: Mod 16 Split of the Retention Channel

## Checkpoint

This checkpoint follows `__next_implementation-090.md`.

Checkpoint 089 split the exact height-one layer into:

```text
3 mod 8:
  delayed-peeling source

7 mod 8:
  retention source
```

Checkpoint 090 refines the retention source by splitting `7 mod 8` at
mod `16`.

## Implemented Lean Surface

File:

```text
lean/dk_math/DkMath/Collatz/PetalBridge.lean
```

Source-channel bounds:

```lean
orbitWindowResidueCountMod8EqThree_add_seven_le_tail_partition
orbitWindowResidueCountMod8EqThree_add_seven_le_window
```

Raw mod `16` transition facts:

```lean
next_mod_eight_of_mod_sixteen_eq_seven
next_mod_eight_of_mod_sixteen_eq_fifteen
```

Orbit-label mod `16` transition facts:

```lean
oddOrbitLabel_succ_mod_eight_eq_three_of_mod_sixteen_eq_seven
oddOrbitLabel_succ_mod_eight_eq_seven_of_mod_sixteen_eq_fifteen
```

Recovery height bridge:

```lean
orbitWindowNextNextHeight_two_le_of_mod_sixteen_eq_seven
```

Three-step recovery theorem:

```lean
sumS_three_steps_ge_four_of_mod_sixteen_eq_seven
```

## Main Reading

The `7 mod 8` retention channel is not uniform.  It splits at mod `16`:

```text
7 mod 16:
  next label is 3 mod 8
  recovery branch

15 mod 16:
  next label is 7 mod 8
  retention-continuation branch
```

This is the first formal evidence for the narrowing-cylinder picture:

```text
long low-peeling retention
  -> must pass through narrower 2-adic residue channels
```

The recovery theorem says:

```lean
theorem sumS_three_steps_ge_four_of_mod_sixteen_eq_seven
    (n : OddNat)
    (hmod : oddOrbitLabel n 0 % 16 = 7) :
    4 ≤ sumS n 3
```

Reading:

```text
step 0:
  7 mod 16, hence height 1

step 1:
  next label is 3 mod 8, hence height 1

step 2:
  3 mod 8 forces next height >= 2

therefore:
  sumS over three steps >= 1 + 1 + 2 = 4
```

## Source Mass Bound

The two exact-height-one source channels satisfy:

```lean
theorem orbitWindowResidueCountMod8EqThree_add_seven_le_window
    (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountMod8EqThree n k +
      orbitWindowResidueCountMod8EqSeven n k ≤ k
```

The tail-split proof is also available:

```lean
theorem orbitWindowResidueCountMod8EqThree_add_seven_le_tail_partition
    (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountMod8EqThree n k +
      orbitWindowResidueCountMod8EqSeven n k ≤ k
```

The second proof is more meaningful for the transition graph:

```text
3 source -> tail CountGe 2
7 source -> tail CountEq 1
tail CountGe 2 + tail CountEq 1 = k
```

## Documentation Sync

Updated:

```text
lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
```

The status note now records:

```text
source-channel sum bound
mod 16 split of the 7 mod 8 retention channel
7 mod 16 recovery branch
15 mod 16 retention-continuation branch
three-step recovery theorem
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

Candidate A: split `15 mod 16` at mod `32`.

Expected pattern:

```text
15 mod 32:
  exits toward 3 mod 8 or 3 mod 16-style recovery

31 mod 32:
  continues retention as 7 mod 8
```

Concrete raw experiments:

```lean
theorem next_mod_sixteen_of_mod_thirtytwo_eq_fifteen
    {m : ℕ} (hm : m % 32 = 15) :
    ((3 * m + 1) / 2) % 16 = 7

theorem next_mod_sixteen_of_mod_thirtytwo_eq_thirtyone
    {m : ℕ} (hm : m % 32 = 31) :
    ((3 * m + 1) / 2) % 16 = 15
```

Candidate B: general cylinder conjecture scaffold.

The observed pattern suggests:

```text
2^(r+1) - 1:
  retention continuation

2^r - 1:
  recovery branch at the next residue depth
```

Do not generalize too early, but a doc-only conjecture note may help guide
future local theorem names.

Candidate C: local sum API.

The recovery theorem is currently expressed through `sumS n 3`.  If local
multi-step statements become common, define:

```lean
noncomputable def sumSFrom (n : OddNat) (start len : ℕ) : ℕ :=
  (List.range len).map
    (fun j => orbitWindowHeight n (start + j))
  |>.sum
```

This should wait until there are at least two or three local-window theorems
that would actually use it.
