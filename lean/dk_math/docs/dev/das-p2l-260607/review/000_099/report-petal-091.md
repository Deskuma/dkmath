# Report Petal 091: Mod 32 Split of the Retention Continuation

## Checkpoint

This checkpoint follows `__next_implementation-091.md`.

Checkpoint 090 split the `7 mod 8` retention channel at mod `16`:

```text
7 mod 16:
  recovery branch

15 mod 16:
  retention-continuation branch
```

Checkpoint 091 refines the continuation branch by splitting `15 mod 16` at
mod `32`.

## Implemented Lean Surface

File:

```text
lean/dk_math/DkMath/Collatz/PetalBridge.lean
```

Raw mod `32` transition facts:

```lean
next_mod_sixteen_of_mod_thirtytwo_eq_fifteen
next_mod_sixteen_of_mod_thirtytwo_eq_thirtyone
```

Orbit-label mod `32` transition facts:

```lean
oddOrbitLabel_succ_mod_sixteen_eq_seven_of_mod_thirtytwo_eq_fifteen
oddOrbitLabel_succ_mod_sixteen_eq_fifteen_of_mod_thirtytwo_eq_thirtyone
```

Recovery height bridge:

```lean
orbitWindowNextNextNextHeight_two_le_of_mod_thirtytwo_eq_fifteen
```

Four-step recovery theorem:

```lean
sumS_four_steps_ge_five_of_mod_thirtytwo_eq_fifteen
```

## Main Reading

The `15 mod 16` continuation branch is not uniform.  It splits at mod `32`:

```text
15 mod 32:
  next label is 7 mod 16
  recovery branch one level down

31 mod 32:
  next label is 15 mod 16
  retention-continuation branch
```

The recovery theorem says:

```lean
theorem sumS_four_steps_ge_five_of_mod_thirtytwo_eq_fifteen
    (n : OddNat)
    (hmod : oddOrbitLabel n 0 % 32 = 15) :
    5 ≤ sumS n 4
```

Reading:

```text
step 0:
  15 mod 32, hence height 1

step 1:
  next label is 7 mod 16, hence height 1

step 2:
  next label is 3 mod 8, hence height 1

step 3:
  the previous 3 mod 8 label forces height >= 2

therefore:
  sumS over four steps >= 1 + 1 + 1 + 2 = 5
```

## Experimental Inference

The verified local pattern is now:

```text
3 mod 8:
  2-step recovery, 3 <= sumS n 2

7 mod 16:
  3-step recovery, 4 <= sumS n 3

15 mod 32:
  4-step recovery, 5 <= sumS n 4
```

The non-recovery sibling keeps narrowing:

```text
7 mod 8
15 mod 16
31 mod 32
...
```

This supports the working picture:

```text
long exact-height-one retention
  -> must remain close to -1 in the 2-adic residue tree
  -> each extra retention step costs one more binary address bit
```

This is not yet a general theorem.  What is fixed is the next concrete rung of
the ladder, with no new `sorry`.

## Documentation Sync

Updated:

```text
lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
```

The status note now records:

```text
raw mod 32 split
orbit-label mod 32 split
15 mod 32 four-step recovery
31 mod 32 retention-continuation
narrowing cylinder interpretation
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

Candidate A: split `31 mod 32` at mod `64`.

Expected pattern:

```text
31 mod 64:
  next label is 15 mod 32
  recovery branch one level down

63 mod 64:
  next label is 31 mod 32
  retention-continuation branch
```

Concrete raw experiments:

```lean
theorem next_mod_thirtytwo_of_mod_sixtyfour_eq_thirtyone
    {m : ℕ} (hm : m % 64 = 31) :
    ((3 * m + 1) / 2) % 32 = 15

theorem next_mod_thirtytwo_of_mod_sixtyfour_eq_sixtythree
    {m : ℕ} (hm : m % 64 = 63) :
    ((3 * m + 1) / 2) % 32 = 31
```

Candidate B: local five-step recovery theorem.

Expected milestone:

```lean
theorem sumS_five_steps_ge_six_of_mod_sixtyfour_eq_thirtyone
    (n : OddNat)
    (hmod : oddOrbitLabel n 0 % 64 = 31) :
    6 ≤ sumS n 5
```

Candidate C: doc-only general cylinder scaffold.

The local rungs now strongly suggest a future definition layer:

```text
retention residue at depth r:
  2^r - 1 mod 2^r

recovery sibling at the next split:
  2^r - 1 mod 2^(r+1)

continuation sibling:
  2^(r+1) - 1 mod 2^(r+1)
```

Do not generalize this in Lean yet unless the next local checkpoint repeats
the same proof shape cleanly at mod `64`.
